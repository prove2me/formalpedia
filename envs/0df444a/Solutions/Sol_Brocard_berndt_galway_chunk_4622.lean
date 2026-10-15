-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4622
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:12:28.711421+00:00
-- url     : https://prove2.me/submissions/7f02ce30-0bdd-4927-90d5-a1b72e62c814

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 831115107 ≤ n < 831294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 831116357 1250 831115107 831115151
    0x2030444070507091a0604080d090603091a06010318060e0606040e0312060a0302040204080a060b030c0a230901060f141608071103060a150b030106050703050a030e060109 75
    0x9208181007124200040011400b03105644540c0000120341c2c2e40034070b110756200040443e4035000742c0c0000d004254410001001181c40c0b40310f545500d04252100003c0303054510b090300052028003100760760035148081103a12076020760107150000f80030388141e000000b00f8500b40d1080e11800e69030146034505d480240901980103800352001d002c4d040c0c0b0801103aa480c4105600f41c1c42c16001d02d00070581079900c004190000b90b40041c0259101c41d2628500d81d00c2d80d070281000c0310309034038150350000a4100400c65291640c0028903070406a89868001300681120b40034a08202515015498556960079448c40c0a40130300c2c0c0c2c1e1803c0d405917020024082008040b4054074100c018000c880da0f00d0b6240c028210604c0c2e000003200c0e1592402d18040900d2604091040d615000c0c0904101c052880c0b035100001c40d401e100466991140c4d11035480b0305510081c05461300040c010040c10740824020b6000380000ca03020b01c0d0006600b14050641400d10800f80c219454068035001d01c00d00038210014040 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 831117607 1250 831116357 831116483
    0x170a0209131a10020a050a210914040f0204050405010e010515090a1502010f0f05090c010804050c091003060608010504060c0f02060610020c06070c080105101404020304 74
    0x1c9203003282e1480b00d4074001d0100704144101c280401c58802a4424014254410380c0001280d810700d40c2c920308032008001c4000b02c5c0e544100d00728818591b043c03056003001b080380d00050528468081d80402e11009c1c080b5007400d031b86207503000c102c0003810351a644541030084c645404002c600d54144010003000b900f50242c444a4031406000750748403a0744032400b4004446041c003e4040701c00b10f6a0060303015280e5400450000d61405480801010107038010314032900c081070555490102090040d40d20300b00940d0f024210341d200300c8005415041103110581c1000b6200340441d0f08642d00d42e40d0350117940d040c0c2c001d108165141d000340410414940181e02c00c2c1d60340c90900d07020812421400968548004200d18462121004250030b507500a02c40e0841544020705456600c0b6641e04042c003440842d449803032207543c82c0400281082104130b1440c1e051380c140e40440c802000e42002000040d403c050000e03203404941c844242c9200d8144a83c014100700a04130f0101111441f00ba200d141d809204070403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 831118857 1250 831117607 831117611
    0x190e120903061b0f280905011b050c13090f03021014060603060108061201090b1e0708010b1305101d030111070b130b09070f0501020714010e01170a020913 68
    0x4483c00b0310402060342c120000311410240c544001c60300ca0805692a4080a29101d0a6035001401e40c1d174460b010106580007078950401c12a9040c03820a009540010090642e41100601704410b143c091040d03100ca6061000104803000341c2c0e26403d46000704454102c000d0784c05650300c01076a180b41e004152072400100544400c4d46800b4010424a20000300002e040090030340015026940b41003203841d40d903000500810440c001480d0504c2e01d48000e681d84800600b42d820888404809040c403141300d015951703540c020503480e00807010020b4221034040703907810101d0080410551903048004804100680d11420311021109402c031070312801ca503080d4003a0341801e00c1c82c1c2d1301075030140886001c645e020904000b00da98028090560b074481090003040031408006001c0510400a0101c050350217815a508501d640d0300d00583cbd989a00b44141829500d80d6040007295600542e0414019a010704022a0300410550308803680c800c1290b081241c0303540800d482400c4d050650401c2003140e107082003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 831120107 1250 831118857 831118891
    0x406080105062b06030b0a06170105060a171f020301180b0321090301050406090b0f0f01030b04140a0302070f06091802071e0510180209190e12090306 66
    0x60260a4034000e03030800224448011003100401d01640941c4c000c40d000381d50070340d180c104494074401420b4180700d0b03040c0e80b2013061311060b400c142c1807151078000c80d170040c40c0003c5e480c900940d4032180e0300307030028004840c000c110f06804044441c01c1030980c000d00c049801a41c9605044024030840c040c140919852460401c094403180c400103004840b031407403004890101e000c01c40f040915403045000194040d400c04d020301080180d140c00085d03040e40315600000d01c0e6900d000c500f02c041c0780e0817540301d82655080001000400c510f40401030300503000e07003442d40c001941000d205140038018001200180c0c0403280800c004d40b580c0300c1d500090032162074840105450422002903410178101020000c03035000901504101540c09030024140940500300c144042c5400c00c0e07070f1102202e9152010f140c2c01d01b07440f45094244c5410440703046074014030707400c9181c13540e0000358543d0300015807505c0703625500d011000c0590310420100d0b0381c211039420b03c10b40e82d0002c41c0a150900c28041c2c0f10404600e00488 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 831121357 1250 831120107 831120127
    0x10831020a06030c020705010e03032709090f070b2125140d0c020304260715020a030c0204110d0203150a08030d091a040809011d13050c0904060b040608010506 70
    0x6500c0203c0c7d400b407031302410101c003c41c0000e065104003460715000c00c4400381250202d01980342c600c81e03d910b04543c0e0490030340c6c441611546031000c1301ca10700150740000c2030501112191402030180301c158807030290303c01c0180904c0d00c40c0405003510050b9000c10007420b18010b002c50a01494085103107485c000c4d038003080800007001e05000d20031410800c2500d031000005020320030019900103003203100e110000707580500d05640345020269501120350003006404a41d00c11814241c9030301c10400e41c000c103002902a1030480d000050b9100490f4465154521000d540440402400b107401d41d1150069807400c00d03290b94003100400d0b01d5658001c02d41e503217041102c44808415584c507040c000c500410844000d00e0075010307981400e403c20110340064003d100030311120001414810740280c07240e0720650740380251011401200c400203984918100080c03101500d042d08220340010340020401d081403030410000f010794410ba00a0360301c209010030204101e80d88a25a10700601c1c003030383c8242ca095240c030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 831122607 1250 831121357 831121363
    0x307020618011a0609031006060c050f070b09010c05011b02160e0103031704051501090e010f15120206070501021603081b0a08191b030b0a080705010831020a06030c02 73
    0x1d4540351244801150801c01c42e01c042c00020700c8803c901c00c042009a031503100150140510410034bd44038801c0d84540c04000d1030001d0307a4400e03104140c462500b002040c0004480c1c04d0b00c00c80f011a507654a50040294103400c482800719035800c1c540140c0850480d00c25401d00f44120342d800841c00c6200000100003007a0010184100f0701c010211843c102d9444d414940e241081c051180300c00341e000503000003084401d81e40030340c100c00d0340480217005605046071090181c450348596203c90b07103c0c120040200c0052820940a02c51001d02180c0c240b40240e200d503801c9800c050b1500211400d0b82841604055001d401258050ad58440740d403c0b040c100710f10f03000e0394043c11688106100803a40890b0000c2c00f56149401903407045070040c041c40d03010500b1f990303000e114985410f010030b0030940d15480e10b00e840000c050641d1b03001030080c00031390b01e0b02c4011115880c0c00350180686600c0780e80c080160b10040440c003081d074421501020030b504141c2c814000d1032220f40e4821f1007094600a00303240301036404 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 831123857 1250 831122607 831122651
    0x5031915091113030305072906190b040e010f080303040327051f030e030412020d03051b01140a021c091e15060812070f030311030702061801 62
    0x8008005002414207488001c0b901c1001d038169080c04000500208041d840340041440074861110500d08040300300e5034034607110341510001c0c80120a100002c1b05400c291140c0d0790320000381d0102030300941e42d0340001003066000b600400640304800005002d4454401e807980001c200a400944c51840d00b0345005213101d2040b468010820901008025107034419212580503100c000c080340300c0842c0d880d42e45541481d80380c0c840c42c007080c100b00254000c02400f0054034200e400901400751148000ea00b0041c1044901c40110f007804020b0245070910745841d81085113011409000103101032001c0c0501c2d1075014010030410f08140104040c0310f16803034524280030350728088413001c0781c1c0015510b44085c102c0c4140707000358001c045c03d00001c400c0c030a4060b40e1418800d003480007049401c0d00c0f04d0607a80c56048509429070240f4041000f01c00040404a400c46403c0c002c0c0b80c0000c030b0030300d403400522140d0310688403d401a03009a0520800c01407150f007101041040000810280b41038101c4a152030f015 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 831125107 1250 831123857 831123869
    0x1b0906261513020301060e0109050907230103110d090818030724090312020714090103020901150c051e010f05060a050616060906142a0a0c0209010605031915 69
    0x344220700c41103440c250007580c06010611410611507841e12703007003402800104e402640f0361245090018030100b5045081030000307105100e2494102c8001e0045d40a042009500012840e0402c003c07000060035100b203510491003010490303130710100e07007801030010410040c18500c40c0d004100c04100380000c0241d0100c1d0300410320902c00c04001d43c0001a10281e4a55001810840030f99018118283c3d0215451040c1c0350310f4080c4500070700b00c0900780001c80b0000d01009402601480c014440c21000e0340441225008901d0428942c0f0b00d550b0301d2a0814008490700200c0c800e2282c2c2c02051008207005d14042400b100030100300078a4150000342c0311103240c3c800c1c2401584009144481c9030255488400c0d40f82c0c0004042c032811107036103054001050048000f525800c17121011a40030f043c21182190002c91444a00c00c91180c0225007480c281e01000d070340c00501c2000410000142c82e8424070718003d1180c1d40b2550303202d00e801010964004108035004290700c4ca040f0802e0b5864002c004940c040e204 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 831126357 1250 831125107 831125131
    0x33503041101021c080118090519210c140f150709420215190903080106020105010504090b0c0f070f06050a0c0306030f1b09062615 58
    0x5010050b07041ca902d4400000c941068920b00308044c0b0b4000307401c58100c418207501d42c0c40c3d40041d200b0070400c07108149001030140c1c000704503000c0c2c03500796a00030344a03170390151102c500414184030100f0300320540350948501140b059a41103050090706490400d5000300c2801408140c048541c0705622b52040f29600750400e05103001140015105035169030203440d4904a00b00802403558400c8000130400480106880300707138100c90f0806084c42e60810243c03559400510907848a0000111840c0c0024500c4042d9401d20005081a81c0503000e015541800f90f15508840d5040000003825500142c208601403400e1101c2180003a046825041e0300541c1008a02c1d120303002c41003012600d00c24264007031f10060003000c448081c0851360780042e0065181c41c504200300c08030054160292051444041e1601c580090100c0103c1e0340000301e150354075501c03801030340b00580b2802054200d03851508120b1b0005404d0034964200d4000d80e01a5002c1031002c0018041c08a02503400300d0924030080400c030041c5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 831127607 1250 831126357 831126383
    0x6031b010c1b0503030f130b0a09210206070f02240a0809070902040b0301150918020d0906051e0123011d030607030915060b030a02160c03350304 64
    0xc0c0c0e5404042c040c2400405495507441c41071042e0304e443c0c0140042e442841c040c4100011060a04800c98100c201c1e42c1d110035010303500d006030560403124090103008090301c034a01c100c0016078444000f05900d0b03103d03075040315400d5490300511400b08081c10340c81100a15144a0300c450100d030b00141c9691003030914100e18580e80381000941000ca03d603025076401d60000c50301180d0b0174003610113035050320a0144032203400504200700301d41407011407180c401840b1041c169000301e031007203800600081c00060b0001c070396181c5666030312048800881c1c980c2450640c1f0184040c9000c1e00b82810350050120303891380c060012003405402c1e00c0d0800400c0d444c0c1405510702d007401000c04140040c17030b14000c0060544102e03241519018000e0994114101c801c40804000962115020b105d1001078582c90f203012411a40d41200007c000d512503604a5a078900d030b10f00042c0000c0c05021404043c52194289000102c4201c00c10302c1c0c80001c0f16500326070005810948101c01081030152a03000b034100c825480c4003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 831128857 1250 831127607 831127643
    0x50610021c020c09070203031b04180e0a02150d061a0d0506030a1712130b04080a03150b040509070f1409131b0912050613050715020606031b010c 64
    0xf10501c0300349a0094406401c1105598020003d14480e444802140d1110f0000c00c403402168807403401161404000b1002c0f4008502d040e0784507030781c250300c0302c0c045614444640d00002c20b00e24009210f03030102000020880d2010640d8010440189642d5018403004406854002c400c0d0081c400301086e100c0d07984001610540d010005503c1c040c0e040301b02080312509040c5d440c485a0710600380b044001e0011404280c000100c002a10075494125689951648840d03a44d80b4243d0320101c1500101500c403080da80306505c010214600408100240d940e5551900081c0901703024010a007405105040c0d134031901c0b440c0c210f600f0300f20b61140d80da8219600d5149100040030480c140054050540c91b00041010301a2080b990701413062503a141e4204065403091880d5a0080540000b022500300d20302041071845034515621a451003075064841c02c503214104100003000c400c00150042c0e0103501409051300b001c5c820380720040350b1313043c0ea0300c0c20041600000e0311907000884002c1c0001210f0700c3c06100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 831130107 1250 831128857 831128863
    0xf0210090b092407060f05011403030a0e062205030c0103140c030603120d0c2d0c080c15010f050f010903030e0d0c060c0302100c0806060d1503060906050610021c02 72
    0x81950f9801c00e05403144564101389005015031205030b20054900400400e0307212040c14420300714800100190b2800408500849440c100c03050840d400c84820f0000c0d0005071007082c04500207000140045079503614040405142031180000e4505051600300901519120403489030340c04a20005c034644c2e00e0712000c1c0402d180050050300b56050041c08156590800c1554004121030f0b0444e66513180c41c0242a102c241395180c09540b4442c2e0b4082c0c213825030400a0160075003804c00c5000e51405400c04074003030b040600b081d07410036521800d00c49540040c02810000360804016001c151032405c1852007280000c0d0a0105601002c1d00340913000f10b45601d0350b6030304c0700041c884603800718104040d86c2d5550b0001e0040c1c25088401c45c0940a44130780000e4000352489809501c00f1203583e84000d030b8807808103020407a880224603d1140d901c8069007611036240c440c000c40103600c144800203035942c0d0390410b80c044800180c05248614603104017000040e034001020560b03489e0300c00405011903c00641685 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 831131357 1250 831130107 831130159
    0x20d0c09050c09120606012f010204171c0206010909080d1119260903070512090a060507051b060c07150305070903211101090f0210090b09 61
    0x104080c1404104200c000b40c12010308000d0000b9101c89881e0f0424401079034461004880c1280018540c03a00e0880c81004d510f404501544007682c0c03d581400101180c07402c1e6030103a0030103010901140380b0b6130b0804104010001d003003c4c50544440c43c000052030001d440b14030602c03a0340c4003036440714030f0101413143c8081102c4c21502d04c94410003040400000c0101140c2041042141d0802e5000c210348445000c1e102e0008511021030420444a464440748000c03400e000c0e10720001c0748000c0c4400c00008500700100c6030340e4905a40b86a49801d80c18040000750346aa40192003080f0091004000040c00010741c100e0303245074201c0500c21450140c010948078050242d081440d48a42500060905a9641c00032845140d907130701405265075451090312940150b100062541e03103000402c0030182200c2e00d036120316001074030f0005116000b5921041c2900c00311102524824a0340407240c0441ca800319450500c441c1720304041980601c3d081000721240521102240604800f40003249210540c44460b4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 831132607 1250 831131357 831131369
    0xa0f3203010e1005062e0512010f031214120c0d02040e250c0308060103020d060608160809030708130b0703090305070504110a1101060b030115080a0e0a020d0c 70
    0xc140500703500429901d5943e0824548140e02d000049101810925043e0242c005001080320418042881e01c0074586441c00c1d10800b00b180078810310703800e80103c00005001f402180b242c40d00150030f41c00c00c45110684a80e80c2c60a005003070403002003080110013503580c4140050140c40140c1e540341c151280922401880700d0700c0d1480014040f42a4440e150658000c3d1505a0840d04c1c0c8044080340c240a0034183c021100400c0c4045076620000c1d10400c001e5510003018500035003860020950f55041c1c0d501c5803c454041240602041062200c42404004408141c50410f109080c000200c0e03407248a40d16001d01151000030303e0714003403004640083c0051100042299682c112403c000300100c1c1030b40411595130145150000300741c0340501584004d14080c1050500d4600b6940c3c2c01c3d101c0e8a044074490b0000c1d5240c120004901e403018001d1402080c0c1c20301244c0d50000c860340000e201150081803600c1e00c600c2c1c00990b05000c0da0001e80195020350542e41264280103d040c034141c4124164402 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 831133857 1250 831132607 831132611
    0x402010e12010e01050a0603050c06070809100e010e10140d1e0516180e0603010b04050103030305070e030f0a030305190623010203030609060f010c060e0307020a0f320301 75
    0x10403071420551212024141c010000c00013500c54014200c261252444090407591200c00391042600c5d0036001041003d100d107402d246486c0300100840c0400c0341040880020502601c000c900079600100790852380c1202b1120304010800264000d488003040c0107102c4d0146a002c100078601303440e41da008585000f00d000043d410034100030200e001a10080303810940c0701014401c440c550a00444c10010000e101b5145000c02034100043c104a504bc010010703541503484d0741291009480d00c3c0b042a0185010342d501094a1900110180c0120040c40c03009001e0743c0401841c40f51038501182c0d850115500d841c010841c0e840764018500200084040a03480c1803034003400103858003105000ca01c02a43c0781d400c0c002659100d4006a0b103c2c0022108030f60000c8400f0001080d52600440301c0280c4041414803620b0b103683c82d181c12003240c0d40125006580c0c3e00c001010400e6291282c5440002c1040001e056820b80c10310509400e80d015102441c2d00e00c240ba91031032188482d41c5081c00025050240c02 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 831135107 1250 831133857 831133879
    0x1b02090a0e0d021c050a090e1302090903040f030605130218160807080601031d030a18080d020a12030902130f050f060a0612060321030b04020712080402010e 69
    0x14010061411400705803251186480e8184010300101c0c07400030000045402c02c01000d50f80d40d044e102540308001c08420030041e0b83e00400c3c010b10555002e4020241070925011810103481448680180503201001d1f0703500a0004000490f04801e00d40140c03540290042180c4c0c03501c0c40440c3c07060385a42d00095101c0c2205000c40c03103402030740241d188168402c81d41c04680381da0400c1d003600d0314401500c0303150002d42010000707030741540280c01c40d6604140a215418031941074000301411500f1130690a0001900c40c06040e50304805003403a07101034107400340582105209000003031b56a0614510043c1204d820070848580e2034041d50040205540113400d845080b07406a55400042594881d0380a6092a21b400300b90103400c0841010700c140c002800e001c1c00981030030f03419260322050044032150692114000310024000b00034408110540341c5c0d0200c05000001005410b496102c3c0a20380540c0c070510076040071442c1d450444071940200d080012440c0c4440c00100e403000e808403080c035045000411 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 831136357 1250 831135107 831135121
    0x2a0a0603020d02071208041e020f09060d120302180a0602210408010513030809150109020c160909020310090c1403011b0806120c090a050705041a04030b010b1201061b0209 75
    0x240c687c41103125413620341d0109a000d00807100001c0d0414060b400882900403c2600d003401c45d0364a41151340101300c41c0300241e1690f11440540d202410200c00660003050351212002642d0107100c0d20380c411100445d91500304030000395a0310b9200040010086034aa00d05200a250f804a44c040c2c0700340002400a4a440b4881c0d04e41c0c402102c0301100003919000008040310000314414541603003100e08031361943d107410050000781d000712001224502444180c5468030426019070030082003014000b00700035085004050410f085c3c1301c2c4051900d4148840000010f1401000c442550350701c82c0c151241030003000c01b080c0100708103a004400c034201c100e0048101a001140f00b440784c24100c450000d0380d07188480e01902c602ca0000b4840d04844003501199499200303400413940a05607140490405969106c09010f45000d2402141070000c002411b00911100c0c12840f4058540446060720b4040c0c001c20281000c001482100d04020841c814401c107400003055901d413803600102030841a0034040307 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 831137607 1250 831136357 831136367
    0x50f030c070b010503010c08180f160306060e190c0c08030403030f050a020c03071e0c03062a0e0d050c04090c0518060618212a0a0603020d020712 64
    0x407400d96146440300c0c000142031805005452248034155103c5846854451100c0c1d02801e098821f4206c41c042c0303d0010b8110030040011001682005042d03013052882c606142c0d04072007258004c055054400800c000b42040b803140000d61000b0800c10004400ac10700c40101c40340240e0480041c44000004144024164075400164010401b14800c10040c0c481c99040d004074803400303964035001d8000340440d1003c00d5280301e00008480409141c5c8612418036940e40c92010650b401c215601540d440f9030b6040e070200c81c02426190fa00c10801101450000c0d40301402c0803008003480391144140034190001c000c814009001e54070400782c41440580d4051078485120200340c068a8000d0151040240106554561084c051600904418603010500c0d201d01c0d050b21030700072025088a0191b4680101501041c10305100c80396810140c42111070f45503640700c1d01c0344e003541e01d034403004003031003d140c0f00d41e8500ca04003048805a00f001039a542407500b400d00039002d00766025002e002c41c0c40806224035000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 831138857 1250 831137607 831137617
    0xa061a0c160b1c060f0302011209170c0709060b160c050a090e010b030309010c0f0f0f0c0311010e010f05180a030b01060f090803070809060715062909040903050f030c 73
    0x440d190800007090918940f04403800c510800c500715002d000d0030405035010f42940903002e41c0c81c10021070924a1526120042c1010b000243c0021600048a0b00d550800340560070103004c44400600c0700d00d00c0e110491120b401881d90055050009003107440400c1070900b07644000b001c010303004e82507003035407810003034000c24000480781615400c01802c1d2a080c9400f0044980714001612000ca00c40c2aa458103507555182003411100c8100c041c8040c80170a065800000c02284540003d10b001070640c500910305140c1c3e4500c06050180780381e0300a00d0750ba0041a600750382412840c00c036448403540c031086600496009501d0380c01c0610300101006102c0340e580298141c54641c2c40b070b26680010600100c1d07426038070344140d08298200303002c48000501c9101c020503260300c0c000c1c111403d2114946420f108203020b01030245270300c9c0e92414100074a0340d610b070300d1155000310449035105225044c1801d140d03d11410a00e03a114990341c0f00200c0406018400780c075101400c0c100d059443e4940500c0e190295841 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 831140107 1250 831138857 831138877
    0x40c1e050318060f04110102120315040b061c05090a150501140d0f02013515030127020d080307050408210a12021b070e0a061a0c160b 59
    0x105404080b0040000500345008022129440305070b0381e02c0f615070325030501441c680c142c114042d2a00e0b0b05490281100514000d0240b80d00c40c440d01c101e100100402c85241340b442c18000e080600080403920310060240c82c024250390340205140e42c81039181420050541c00040c041700e00705408a420100507403000c0c0c11f80c0d13240d00c1075107200705d060820007078000e24140008080441c10b440d0000154421060010100c2d109080b41d0540b402c1c0f99031042c8140b80c100310500300303040480104090715000f0910340302c00c000150001c10603403450780340c0d845140d034031824800c81200900702d01c001191218100001c0e001d4002d94251344074240741c03e006140b9131003480f0b0005180310303010303031481c0042203104412050170040302407500c1d001800c17900751031401c0902160105a58244542070089004c24460742254407950080d24060342000c078a00c00c003410107064040060307e06402840ba240c02c1e582e0740642188070800007601c48000c00e070028642201c1140940a02281050005504805001821600031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 831141357 1250 831140107 831140131
    0x1c110901080f1213050a0611060708070e090c04080d02030d06270c11010e0304081204120b040f021905011b08030106030b010c0605040f0c090614040c1e0503 69
    0x10740c480005030b0390080c5182512641e005010104200d1014200500d07003010745a0b00c45032a556984001a440d0410303900c1031022454100342000074000901545038414140d0404102ca8101748000404c15034030b60240031300440354540800e40c2c00808500f618000d040d800222a40c1c600541c0e4000d4072074208840080100d420034030041015228251003007460700007c03400e12400c803a600350100140c400084140140302c10b039070b0040740c2c251081c02030715450701d00200219921407400803501d2030070345d40c095100d0501e0810b01c4240700014051250302d540c15041442046180c4032402c008194a1003010300940c011155141402c81c0041c00c01e440c411240b007600d680e04100f105d4000390421b1005003200518507001000140400c1d40a03512440c034100040c0b4040100808564400303040380c038151400c0d80c100640f01c2d0450100005603071b450002d840000c80034007540745015403040c5102c0710210054070450702d401104405921606201c1681e505000303410120181551000d052580151402001c0c0382c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 831142607 1250 831141357 831141359
    0x1106070201050603100f091520070503120601050f0325020309030d080702070b03011d090a0b0a0207030c1505012402120d1d10180807030804021c110901 67
    0x250040c410248a840050090b12501d00c81e0500700c0001d141568a401020b076403100c82130042142061828a500220f00700002e402041607071075244950108800d9580c500300308289000100003100b0740706c1d40400d1411400b180e4540400503034140c026000e0b10746541c1c0300070040100701247c26124105003928a4894041e070f8800311000c0b42c5a114600407150158811b000c440000740c85050392a50240081c4181c518042d1511001c00d806d6200b85c0c412505003c80402e0910002543c00400350051503450040c0b00101556840c10610320340103044d25449940450f08906060040e0b2640b070707049a000419501082102d0084801000d0038080c0c210040300d647d000d000b02894038400c50a80d0107040e0014130075540324210010780d42c0c0c441400c08644c00d0301d032942c007201d0008010042402d400720708054090b5440300c00d2071104883d078120310589000c0112180c08041002007044400803601441e00400603651400422048400c90181d0030051403598505030511282031181203201c10102c0c1c00e06456 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 831143857 1250 831142607 831142621
    0xd03020a0e010804030c14120d1401170607051e0a1106150609090a150e04140105100b18090a0902010305160813060902180603010f1109060d09060207031106 69
    0xc044a0080210b4005030035500829514800483e9a40f12036048a201803460702c108c0d03005030040314101440c0c54445802e540f0b0111892099405480394510100c0d005285c820010f5443d2030180c107034414040001848035641c0034240d035544809074480c0d04e540e966030070900020010700e1840140c03071903402000c0115050400d0300d0001e011612008096604000604081040000000e041865800d65800204040341c0c401c030306c0700c002420380c100030402c00c0ca010b04005d00c00440d0038000203860391500c410401441401a404800c2d5588000a5516850103100c03090070400240f03015a441001c040c02c0001c00d0358213800c400103280c400c0c3e8003071005445003521141502402c1c0b5140d00418070071000101c0083e0a140c02254250086038003065241040c1c0208490343c11a03020b02800845400802003681000d014034110070b45401c2c41040050805001102c590180040300e500c580740009e100e40704011140c02045440360030030701c115a51821807401030120005000d03080814002c1c20000307009 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 831145107 1250 831143857 831143867
    0x1104060305030f0a02070504050a15080c2b0c090f0b06090a1517040303050a14100506030604020c03030108101b0207030f02040207080c0c010318030c0b0411030d03020a0e01 76
    0x1140c0e4040021410f0a60720ba107103000682208003490114803800f01e000a1580c1e0318002c0d00d0181800050006071420034491508070022a500005810b50003000c0034481600e94134401c0030024072102490754400b000b404c0001030407285440162280c0300100000c1002d03030340d5500c1354007440101101005202c2003030741888001e002e040d59180d03100c015100100101b60b8900c0c03ca810707070314080c9000d06080c904030443c2011600140c0d0b098001959030410804909040d1107512004c1035604124120ba160403210101902190301546021743c1010002c10304a45598050310450342ca414156520780da12110b20320307500c1240e40540300c94141000c0390f400c0b00d4071004510098160240d805840700500f5034030f95214101400c01e00b240c009500300400c40205054001801c4003401300805030080800a80004094503901c1490008003000f132005400000c0e0068a8112050b610481d100310366900e03030400503d01540c146041d501800343c800604016a8558002c040561072a1201c1e040f2151500044407 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 831146357 1250 831145107 831145109
    0xe04050f06150306040605180d020102180409210201110c0c131509020c0a200a0e0105031930030608070605030402130f0f020408010b060f1b07050a060903110406 71
    0x81c05410000104000c07072a07c1e00301d1503226041e2240705c078070717000d050340c9113860400d0142584006035408282c0e041440c80d02a04c0c0764030344908035024402d209030f684410040c4000e60b603641d02d40e800c0319004110703854000e42003600d101001e511380341d44481341c84031102e44510300315080c40c0c441c41200d03a074804600d6041c406c0400e2128401c11500c14603081000c0040254030032180c81e10948100008140001c40d40101e03142031604080054011854110500101d4106a000381403010038150040c0208c2d20002801483c13910002c9507240390703280a003054104249100c0380d00401074040f0115945811981c0409001c103e005d076070800c2250342d01c0d01050344503030050007000e0000b030080000c5005454880b60030702d1090b0016000041c03107030348400c3c8001102d44042e039450300240c000c5410840d1000a10600700f405e5001d65180389803451500583d4100d214209500c2080a258854080c0102c410008070340549800ba1001c551581c80e20030162448680340f000311381e40f45204100c542f142c2080d0049030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 831147607 1250 831146357 831146359
    0x90b0703090510020f030d0c0807020f1f0b04020a020c0108090601060207260f0c190e0a110712020303040605011e09020a02030d0603200d08220e04050f0615 69
    0x10703800e01e09040030460a03010382042c0e081180309020b030724485402c2c2480200b982040c0c1900004040e4107088016005200040c56030007990441c000c0c00702d6401010a0304030090860810354800e0341258800e0100809181c3c8016400c0ba01c0402d04240c02a00000c81c40c00410b0240c80d015400d58480e50525a2200240036000c01604100320400054032000e03240c1c2c404032400034140c1c1d03056a00252079850400c282082e01c04c10f5201c11901c484070700348540100702912581d0700720b003001414000e0200032401c1c05040b5003406a60348918418001036901592883c583c00182038080455500c0000d603290015201a15030b680f0300800001e5441450200c520740c00561003445000380c1c50641480300075007000ea0410f0940c0400c0080c0082c0c00c05a1040f800514400c0101c4400d88142c107000c0c0ca00038902c030502d280507100c0e62001d14041402d032015a81c13850010580b10f00481400c41c4906074015490344132103807500d05c50701804100035005c58560100d4001e10100c0d0519074500d81d200c548440d00d65121 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 831148857 1250 831147607 831147617
    0x1125050a18020304060b090f0412030e1b270109180203060a0903021c050d0c05040506030a0b04112b05060f0f0a0b0708040306060b0a12020a0216120201090b0703 71
    0xc5851010075005913a01c2030060a0005d8128050408100690000c6511081001e011020001041141d80d4484000c45242c80c00304602e00504034036907550b001c45030303592802540ca40c4107041151f640403c115400301c004191180145100035502c001c01c4d40a005016030241882c461868041e100c460840d81c0940080090a45868940360307031004004500003a0210b0080802d100b0201c00704e9462484074140701d039200c1c0c0d60361081a0000048036460000841041000c000401c85070b82c80700d05036034001514020005000d00b102002a0040140800c2010a00c40200b48021440703a00c5401c181d603c00703480c15810f401c0441c5002442125030488070158080300d4140c1800181c14618400c281038400035042d00c0c3c18a8403034280070455044540212000d080000d424810070a040c0940402450400c132094103254140720302a08200d40c05d0b010454142d40868540d480034820403d900b800000d40c0d00303403030880341c403000318000040340c0100c164041004000001182c101d0f6030f007200d41d03854240e0740d1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 831150107 1250 831148857 831148889
    0x406062d09030303051b0f0a020f0f0c060d09150204150f02030307030b0a05040216150501030b0105150d0e1c140f13030501050702060f06030f0a080a1125050a 70
    0xc243c006080103401c4103210002042032900c002c6c6004000e1600c601040d4995888600c0c0c20030081c40c3c000c641c40380300c2841e00041500c40d90302600007034440c42143c0c00c8910700c0d00c60104480c40c0c07005000301c05018091512200b004284a60940c2c010010b54411400d690707140604060152120716070009201c0042e802040066082c5100b580718855240008214100e16680c1c1c00000e01a0f82203001e42c4410900010400c0b82000104900c44c2c0c80c0d40c19260b0240069032440c1c0362a00d00c0c5005100d124000d1100c96044545071b20040d0803a610781d01c000c001003020300780b851301d004e680c0c5000104010102e00600c5e0036202c1030780100c0c8900c3c1e501c03074803051300da180070780300345039501190480c003190741d00d124a0560100c0012000e01480e44113000650052111380f90601c00c90b900c0c01000b41c010740c00ba42140e640d0091f2450007250380f80b001d60b0481402603403940301c0c0408903100e80b20059100c0442c080c80640c0c0c011400b4a08400886508150391041d20641b10b400f04442132080d403041103241100d45003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 831151357 1250 831150107 831150113
    0x3100b030c040b0426060c07030c020409020319020307060306050604050607060e0607181d07031d031204210c0f0503070606090e061605270406062d0903 67
    0x10040d41d010003248a41400c20f03640b401d02030060b07085600501003001211414086101441084c0c04190402d50010505030800034520704880c451104080e0420020616132002e5444039041107000f140d0240c22100f02026000011243c04090301c8224401e01038100c0015055200e030150b01c0660300e004010901d00783c03030101040110351140008855560f15008640c0d0a1407050042c2403241705243c4407141010030307078000040404082c0d0050b4581c0e000c0d1510940041900c8004564022103609000440302c4401c2600e01c00540300c00324030f040a00c00018041a141403015405002c4c51040b5101d8002110303200c881e015150b1031007020b20000d0082070b210400314172a0701240c4106802071090364607140842d00e40c01e007a50300c030382c0045081c50340780c980419442c0303410400c082d40001c41054a00110ba6098001031981c440d10b90b030204211707a000785281c3c0701103600ea8140d41c1ca5100500070040b80e50360700c00c041c2050500c00d00d101811010303102c0304803440c8203103110b0303010417902035460394000341c115a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 831152607 1250 831151357 831151379
    0xc120915030406060321020705060708040501080a0f020a020a0b06040b01021f020903030f040608062407060e0115170304030b0f090a060c0305060418050a080f0d0f060e010801020310 80
    0x380290340050b140c2c00000007184a440043c82c4c21007480042000c01c1a15500103450b10383d549c0d021500070301d020001800415041c500b660182d44c02460142c55035280e004d400d0010b072007000d00580d1480c0c800280326003081d070000707101d01c502c07440b070400510b1590b40c2e0410002150384420561303026800c4002101032003841a5035108240352031440060038031221300d0101e480d5400985078000d0407100018240700154100700070640c0480d080303490350500c02074440b488140280c500f85018081e540850300e0000c000d000d40080c0d284003514002084170030420291488178400e00e101d0174070a005455810000480c02008072400d503034000784081d009865002419051280043c09052140aa5003141000401c02e00441225903415a400305007070812004000032180100c40c08c480c1804080030840c001000405c0c05112103410015170f40d00c1740e41441881d5054880d03402c0400303407140317008015035058003664041e1042e40c03000c1486080c0f903038070340045908070312055440f07803d0380070740d00c0040210109107 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 831153857 1250 831152607 831152611
    0x1f0e0610060c0c170a02120f1b030109060f050f01082b0c1406160c03020a020f01020109020604180b0603040818060903070b120916140d14030c12091503 67
    0x2941c400f801c1076036142c0e020002c40f0304004a1038420b800040000065141c2a026a6a400b101001030480c3c040030f441015980e114481450402c1e20041d4100b01e0580d0703080d8010307203160760004000e01c00c0d0081c10005100904089400b055020410740020842c010002280d0100e1400d0325241c0750b280314070501d008500790040c040a410000c021481c00005078080c6211440c0f803800d40000d0100d82044204040602d9405808070b0404c4106560a004240d0004110044a8056401c04010312402c40100e000d4003450602941281c00003d001444804001e00e072501502e00c0c5c40100304010b04501080040e00c410381d405490301600340006480e5030180c1c083c0d0700450310002e20b8185000741a2010034100001c40c1c1c4000c0c100280480c0d0b54a0710303021134001550100303041001d025542000c07000c03c0d07030a1112f4000c1440220404401c000741c1e40300c000c030070010190000102d04107000303068032072a901d07405201c1c1c2e62024014112440000c00400040d00e4213543d00415031b20300c028103408064600c1d000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 831155107 1250 831153857 831153863
    0x1502010b030a0b1504111305040b01140c0114070c110126060a0905071d0f101224030201020c01093f030215090a0b0c030703020c1f0e0610060c 63
    0x2402400c4c1e89548900c50820744101d982005922418507542d02d590551aa60107603000e40e0402a641c0400c2c3c0c0d00040e043d5144150b8510280c948403071820030744c0103180940105050703c403031030309105920750001c0188401034420110001c43c40411310044503d8907208190004910021000030850145031560303582c081c0003e4640c105c136942c4c4800c44c1c000c0da0420f42c2c800021402c06042907001c24103058000203214004d0790362040c0d09010704e0109808030280700800f010082c1c12409699072031015040b4280700c04400c07145c112001204071061001401500c0201d0140c490403076040c8407940a6500c007411540b0742c80f4002c00201d041c070840c6941d5962051b06d0100c1031012030341c03072244000c000039144280b800b980c01000c1000b08120b50f40c806981c05409e00003590301c24504040040c20000115601008540e2481e849442d90702e42a0080d018410101000303000c0c0c100a814074401c008040c94403100c41c40014082c0382c0f221660341d40c64034825940021640c0d010036041c030005018010143d1241d00c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 831156357 1250 831155107 831155131
    0x91b090f01180e180105040807060c090b0408010615032f070206070f0303143702030a0b04050a11271c0b0708070c020f01110f071502010b030a0b 64
    0x10b0b280070780c041d81d6103203030004451111040184109811403031002c0b180903549030000c000e903041c41c2e10b42a00b54000da002c0281115214090184141d104202c00d80003442d098000c5526161114405030207800c4500482806008050412180703611900407070b400c22281d5402203092041e60404080303900301c030384002107940340100400001622048024441113001e60301509000c8441c7c90010203036038401c803d60b000d5103802c0c1c6c28044000700a03030029000c0109025411041a503461a16120b681800500d507680703480030040080c0002980c1240500210841c2c080006940740e0980c40116083c0d0000c0c80303c461004c0c0907224420425111a02001d00c1032a02d402c0340a40c540000703524030702c002080310380c0c440700b407000102001040e098680d002095030070401000c0c540340c4802420f1081c04c0078064440c440118901049900030f07494103107207004400545242c20940d0b540c060f41d4403040c1c4600c401d0b50404810380e40b4040e00c1031141c1f0315034000007005000c40449981318081c1c90b51016103405603100e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 831157607 1250 831156357 831156377
    0x60f13150605060d0618020708030f0403022802040506060309030708031302040e0f0d030603080307081b0409060f050a060f05031e07030504061a01020705130e0f0c091b090f01 77
    0x143d0f8100250100120414010404908100d242038842020900c6d1810060052000c0300c0007400840c145d0364800c05802240c400d659580c18101c0ca81900d00d900038030012001d40145004810360300d4503400b2140243c500b408951246001d1101c07522084402e03015a41003803045500080703071000119040301100f4826980b5040540000c1d084400c10f82e8400d0050f40411501c40d4007075818015902e0019850504004643c65030f108c0d00200d12004002e5410054004000b0790803807240011101aa138500c05a161250b844450120041626009030744e20300c0100c0c0da0000e1645040c041f4201607031140d81d5840c0868924180540380780d000038114400b58120046841141c0313601001d0184a0f040755500030982e81424104038007103885110601c4800700064590780520f1760001130410486409030713030080760305402d420311400500365508101c0160265454080d030b02a4000744048040384116816465900d621801924000559100c0050104244807014107860202c1a00c5039403001030503c00454 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 831158857 1250 831157607 831157609
    0x6030506060f220b100512010603020f0d0207023c060f07230f010b040f02211b030133020c010f2708070f08060f061f0e03060f13150605 60
    0x40c814000c0000d0006d44042805070b01d048488514070300510f010b040841c17070240b44800b503500302d00c00c0d100100e11482c0c0004540f421903d03141884181c043d41c034001040102019011840d5281003030b2118405590008207410f03603454a001111180ca8225550134070303200c4070b40c0d41c40c50003491000902451103120810000a141e00303200e00485050900000100c00d07004c44100002c031442a940c1c40d01452050044175500320080754040c1102c2e001c4010a07000e070f6140b0300d522120b607000b24801c4400050100001400012080c18055203056440c00d00802800342c81c0c926102002d03880f29140140d04c9500c0e0354180354040c03d180c206c5d4040c28a0314034101076854907000c0b0800480c600340c1e541200020020095107406103c2c12010b03042c2d4070400103c1c10720b05540031303942c0c0030041c103500501d403101400f28829031390b8481d6400c40a0a110300c5000d40c0458800090140c404114566019004070341c0001c00000b44081d00c07a10134460042885400c41e456220300c0320400020205040c0540e96041c08295 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 831160107 1250 831158857 831158869
    0x18090309030a050c032b18090c05070209150603010308070201200a02012c01030e070e040305070606080607050a0507060b030105013b010b1309050a06030506060f220b 73
    0x2c05000740d0040c48003400d0344042c1840d11005805444c489034010226088505d03292a01d14000103080c54840c00758900d980802c0c140200ea54401020030f807816000310720082d0000050841c1900072a5600d41603950241c02c00302e5442c0340c503500c560041040005000040c0c0010160010b6401807500d404403102c01c2082a5802c4100004c01500d035219810303c03401c569010b040d5405e00b140381c900d91342a000d040746840c0d20301104407105905042d19810568201d040c00c008a03402007002407a051014240b45c00c02034400c0e0f00802c010341f00c0604000300405c1c5008001412409100507568092500380c1c038610032215074001b418111511620b490001030a540c09004507401703405207403150b5035036220041d02c0c0c8221140100302400140d240034580e090344204c0303290300c030f04540011540790382c0d503080300300380e0001d480f521382029813030a1803c0240869804594031101c140c0c0d200d0012030b040c41c4c8070181000980210310b850f8603407103000a000070f508550b40c94188407000c600c540f00821200208030008103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 831161357 1250 831160107 831160123
    0x10050109020c190c060e0f06041514040b04031205071b090b010c020a030215041e091a0918010e01050a0921050901140408031617091809030903 63
    0x18526000306100d071290100f4014040100d00302e641c20704030b582050381c0f0f1180000d40f6114290a00404a4200a603a22940b42da01c44030351000313007001c1e525501c5418803018641c8020007200058500010000803000c020100c5040d03440010350141400e2850760381030300b04000c0c14100c108010b000e0140034000761503030791181604c00300002c00390039007070070040281d040783d03042d600642c10000302c2281203000d603d4902e61402500c1d015610f880722510300095001507881654403804190a07295030001480700311b84601000e0302c6800c3e80a102d003000c9200e404580c540000c02199000b40250040b5a28220508900184007601c2d8004101c241142c149242110001c840c0907a405441e013815004122071841c1104480614200e41d081900c032004000300705004803d05503062150260380704140c880c8590550380200f000d14216552000b801c40356001c40c82045400702c9003414100c00d0020b02a0001099900d42d160180c1040105200b00100b41103c02000e0f00500d07627408100b080d800191801d2090003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 831162607 1250 831161357 831161369
    0x60801350d0f0509090105090406020705030d1a060301140d0311010e1e0d02030a0305070e0a1d0711030913020408060106080f0109061512060e07200a0c030311100501 73
    0x31040c04000c81d006416101901e02100401c1420003d442840d940c00f014281503440580d0403070110741c0c403881c00740020b114008002e4054800800e40100946064118003100c400c60950302c54207940900c04e1081c50301080c00342400030302a98001480c907041003081081403e000c0d261402c000c2d014030030352508644021041c42251f40291440000d41c0c9e41803001220900840740040028094a0000946a0180248030001c060302d62000c00d910350300c01c0c00e083d0b507a9080141070707840159860b04691442c1202551143e0210303940000a412280555405189520034030301440c50403285000300314800800d2820104a25800d000215490500b0000203000c0c0009445075117450514001c99180343d00e0580c440c071001402c16005201d10b015152488000860500f0b160920701030b083c0c4918060107194025010f80742c1d4100410a0080c0e20103851400080c180194815000080405130749811001e0380c003806d03d1003144030810021748903c0b65000345500c0c00c4d00340c9031100b14241e07905082c1c0d2400c4c0e102d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 831163857 1250 831162607 831162613
    0x3150a050601090f1d0c090105030103080f040e15031902090610021c02031c0903021504021c060b0a081b060a110109150c05092b0501110307030e060106080135 70
    0x407141724003210343c0c1e480d040a0300300c1031320b81070030104400281144014007005050a0001c180190825107110540d0040d042894070382c007503890b15400c040c02c070107000040ba612911807141c40380d00e8007800c17040d01c00146030040c1801049982d020140464035180a110008520074004100ca80a82001c4d10a622145941c0513565842c0081046100c0003801034003174498a2a00c101c0c440043c2d00018992040502258098020382d81ca00002c9d6800b10038241012000445c180d80d64108000340d401240401c07021a03000c0d0000740c03100c010a42d1424200111501d01c00e174076243e4899413a0480c05004c541901c1e1400501709000814200d080d501c1442c0c040342c50340c80340107120455403014002ea8140788024170b045800d008054000a080d9203441e5150380341c1007a103c4e50000c071103d51410f0100244c0d0001c0080c0050415110041000d80c400c886500000c1c2c94024103904c108804200703a41295840da445591366400d0030f0040003502000c440c410080c00d540c3c401d2001c500c0c042840003c1254001c0c0103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 831165107 1250 831163857 831163889
    0x5090618011412011203050f03090a0b01080a0c0b030a0902031b010f050a020c0f0a092d0c0c0825081206040216060e030d0e03041403150a050601090f 66
    0x900425085441c010090030705100d14581003212080c0e0f5811170385c00d440104541500c504050310144656400355144010000030071200390000108000814401d07a800c1c0c0f95aa0384040301a180c80143e003006100e0302811808014881203200a180c005140000009060350f1642c0013900e81411003a503503400d001d261400604c290b8004042520048403410f1482c5018141c6400079220300000000351722592400b10080916210400c0c4c1001600d0000810003600081010150016440408601c040e85880c2003a5810403038501810105804545507a42415615540d131000c0f81c000c269811b1404142c010038440000b14401c88140c0240203054003580c4581807135407145565802890356024900400c41ba1034031200c1104c01e42200d9410030000030300085c0899100e411803089540230032480d81020b52003039611401100900407242080241c41c0310000820915845000c02000307448030009820015140096540055510050500d4281ca14585561074603800600540010800d000f042c02 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 831166357 1250 831165107 831165109
    0x9021303110307030b280e2104060c0b040809090f070e03010b0a1203030e07170f01140a050901181101020d0809070b161a0406142505090618 62
    0x8200d80d600c240c182c003c1d148142c02c5403203200340c5000243c08040d0801a104203224481d900220f0516504005007040c01418140d034801e42d550711028822660385001401400304265400c81140c044030074a4580c290454240d0700e41030306080c030040003903a011104000d000382036501e10780c0142c89024807904855107420482c20003050895005c941364001da2400f410245a81d6402861204850384c4900b60b0700161500c0c84d08502030000001c26101c6072186010103c0c100400c1044120f030818980100c803001c02c0400f0005099840c40d0100010403800c00010900d85d0b6405d030441030384800300d00c0c0045007010408046015070680500c0036619080c1140711400383d0740e8140401191003100d0324080349070703080282e4210703203a02c03051040340c104c485d0000e082d00c0f1892113040080100c0350807000c4800200400107900f2000d000494045603c01d1400c0102e0341c0032000c0c0000c0078094240800251500f210040241e19041101d42c0854184001440980c01c1541d5400003070805400710181d04220844480c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 831167607 1250 831166357 831166373
    0x7090f060302030712090c17010e070b07050d1d0d02041803080604060611060c0919031401111c051021060f09031e0504030b0106050306010806030d0516080409021303 73
    0x101c4001405092006841c0403c11342d05c840e005a41c0c006a9030f0300042090482c490040c140ad42c00798185028540d0001554448400034000850140042c0e40300e8408035001101c4031034481c182000c4407103820001c1d06d02e40c140b81c4c1c440038006101604c00184492100205002d01182d210101e00060306001005110706250240c100109480d040c2107400f62964002c985c0c07184001070034035040480c04203141e0a039503201c0030a40d920090701c0382d02103012500c84c240340f2284580703050780741465070900403240c1e0b01011441c2110003014415440f4412850181c00c404c0c06403001415016684c02c180c2408141d9120210651083c040030a40300c015900030792a10341c056071030242e2101825840c0c4046400402c1d0010411000c1130592868003a004526035400e03211801583c002900449002c800891182e070404c000350700032402600c4084c0c5550300e0904142c1c4c0c4000c405c450000040c2c2c180b1441040c00030f03600380c02c0b104601c1608014141038a4040c1c42c2c0407600001c0386604401c81400040060041d10 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 831168857 1250 831167607 831167627
    0x80f0d090501140106020309090901022826040f150203100501021b0a03020607031e0903051c023a0509010f03021305310618020c070b0307090f0603020307 68
    0x20100f40d0b807550314280780a501c03405440e011502070b0b8a5600001c8403518203504071a103c58106450321020407510000d440c03200501000c46010030f00741d003581450a00e500464940c070300c282c5032961106540f140e8940d081d440944100b19542448242c80c425a82024006144030f4501d28504516041c0f9103800246414040070b038001c8100089809200503848042030001640d8041e03d480d0360300c5509240407104030101100b402e070300c03080800c00e84042c154000120001c4902504c03c43d242e03e02850410800e8050f462000c0003d07900c644544400b0042e103030340d240c5484280b140c0d48003451410280c0c030b00010407425501400240000f6481003690703085241c20002c172643e441c085041c0a2400c03810020000c15000d0b0b58070441008180b409514916510308100410300d00a0786c02c0402800c20800c0906214010140407c180c04800e20481c41c4620aa40380550110b005060261500c0d0168040d60b00c0a07003000100041c80e000810030b4085401d101d80103001ca9a00140e81c0c2c90500c0d00281030b9154 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 831170107 1250 831168857 831168881
    0x606010f080c0304020d030c1a060f121b1503010e0f070207030503070321020d0e0106120b010e060109170313090e1b0f0a091b0305061804080f0d090501 67
    0x4410034000381003001d82c01e89510a9050b50404442d2001b41015102070003214001000000c099a11450003216040302030b000e01410385688614031004002c002095514000d0324050364050400c410700b80394501012040090050301c41007500d24407201403145680245c00580d0418130310300c00d00c0151480c41d690503a0040462011340200c42c115500e6581383d10a20380c0203800c000b982c20a1442c62a4511304000c0100d640300310446da107001c0520814060051000661459440c1c1400040e0114041152590481e03000c24410442e07801c0030982c1c8145500a01428100844001c0c04690441e903001040883c2c0c101e00011615029150b04c12949019650030048826007885070150070000300203602c502c040c004103201d449043d40800031a40342c80c826240c0b5980141c44000000e1143c4859000040070b030040201440480403952043d0281c3c1e4064031040d8003d09406003500d084241d01e0201c5400c1441000072038644100201d02490329041040d05c0c900b000d40e92183c560030030001744074124500d41 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 831171357 1250 831170107 831170117
    0x40b0403051c020109080304080f1209010902011805010905060304050a050a08130f18020901110d0512010e250c0204060608180d091a0c010203150a0e06030309010c1a090606010f 78
    0xb181c6e464074194000070b4001012568017140c200314140204094803020980d40c0c1080c6400d280104280d4040d107207200d42a0301098803c01d0304501440859090001c2d641d06845241400345000180043c5910042080d10640911448003002450a00001e03511a00a01c0c001e500c90100f000d00c40d200c6009984080303407040305140200025010400314a00d0f04130600401601e440300c15005884100350001c2c241e5240c000d1200403407182d60410702422900700c942070754580a0303885070340180000d802602c0342650721221402c61101c1d08200250b103134450340f81d17140220318181c4903400305090f0350140c0c0001002c25410b1040100040354000010b00700085080102041d00f00300314017a120340c0d154090400c441743c58040d0b01780e0580e102d50845035640c1c0100001c65072407402e000303201315080c558031075280325500000000841a8041000c1c2e0302498008004c0c5140c400882d00641d0107402d401c004a0345807601200442d4450f2060001501c43d440d800040e00e21885c1030380004200c3c0c018081c44400f480 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 831172607 1250 831171357 831171371
    0x20a06030203070f0e01020a0b04120f0302030606070f0512040b03010303080c090a030b091f0b01090f0e0f06040905101b0306120f021807121103012702040b0403051c0201 75
    0x5640207188025544e9030307007009a410121200100d05000305070381d01401c49440241440304100c0380d4100c540030140d042c0c2d00d030094126125801c80c141e22090b035600e40d02000601128020031011260140801d101e001250221002c40c41c2d0010540c00c0750740451010036010004000b0301d82c1104480d81d20503c1e500c000c915082c07003100050f1290f83c4501018110709918800549070345400c01c0700103a102d05036585909000d60544078138000c0c10640e00b802c0e0005408290019003518030745000015503ca40c0100380d110303a90780c42c01d04014030006000560007503c8081d001c2c049070050110f0410238400d48008514810000c000c015283c80351000e241c105480e10804100c1d404892289001c083e81c041c001006c168201d0000421000c40070002100d54800241400300d156003064a0800000f4808010f11a0069440840c2801c1c0824880c440c0742c500301140b4804c1150140c106880104244e000040c2001d84400c160340040d08203803c02c40d05a400000c41d0001100c01d00718550a4100310310090040c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 831173857 1250 831172607 831172621
    0x20c0c0a180903051e040927110a050411090901050603010f14040e010509060405060601030c09060825170906060607030f0e0d032705090c090a080613020a06030203 72
    0x307020702450900d14503903140d114008141c428400c071040300c044400200080b844083c2c0040c620350080c46542c072150301c0c18140c520340d16074400d01c1803640c5007000c03940003c1d4031040e1550b1005408003c0901e41c0622800d001042d00e40e40e074440c0301003070320101c85000c0e107600c0d00d8418440700c1c03107040c2c0119120b22004c3c80100034402c29514004103860f800042861001290b0000c034014064108480456508013002c0061429000a0591295020350308039606074030340500540460b00e0105210000402d001003e200c110300441c1c020b5003010502d003015400501034010074001082c0212080002440305404102c00e0f080460031b13540041d1008041d01040c00c1c04e20000e45148249040141848040058111001d02400c128840038402030490102000c261500524101610f922288001e0740c0c01540740c0300300b4140f16030005172080508003814544270218103c0340c0390060403105610200e1130300d02007101d007020b001e038a0098046840c10011200c9500c10000600026041342d42010f04c1401000b80c8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 831175107 1250 831173857 831173879
    0xf0f1203050a0510080c041104030b040f05060711060115170702011a0109051818030d0b09070c030e091803041701140708070e0d050a03020d08060d020a0923010306020c0c0a 76
    0x10390b14221f80000c1c4d850001107548203940619400904025004410401031040c0b940381d01e151b89109106a504558582d00159014001e44012001c2580141c006101880200405500708016401c042d000c2100300c035941070074064103c84840050b51114045103a150710081c00c1300003a102424030501e40c90400011900ba07028501042c40c214240350301040245c2d0542034142210741511003078940d54902000000b01522014403c6801b440d50940000c1006118101810074961315544d05108403c0403401c00c201c0c2000a0311131040501300c044222030109040000304002c2c0b405d180b101c1940002e10801500312847c40d9240d00b121400303801000506540801381c90762100e000c1c105041c03100e10b000301141541210303410007130852180e04c0022042c10740000300c0403000d003215544c420041c0d032002c09001804165410013500174410340740c1442402041d4005c2c181c40707000c500c5030030081d99a0140c0703410440d1003a4415203005900103131260207501c1c03d00c00000050381c01c0d55101c01c154680600169 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 831176357 1250 831175107 831175123
    0x6031602062811160c0303170f15010e0303040e01080d08010f18151202120c031009080c16030302010f02090906010e030f120c0c0d050a0f0f1203050a051008 69
    0x5102e03030340c0f42401255014100c0584e03440707440c94003032441c01c12241e00d0482c140c001180415404107400e056822901c62072300310707034501c61023400640400359101c07040b42c088000652840709040c042d401c3d1100c146504c0c1000500020b0001015203200380d4502000c544c10001c4000c40c2a082000c004014811054010070840031129411030220140c03404d1010400280107440340082c9024105030005842c480008918007828022203002083c540e503001d40c540c0e40d4102e46001600350f009540031024001d0725921141180d401909400e1620300c01c0081c150400b11190f100d210b403410158002d106155091040003044541e000d42103161051241c0041c40c0214001c026604001d04460355000b02c0d10240115103900c5540400c0b106484400c3d40d5624441d08482500f43c5a03202e4402a00600d140140c60034842e1504000030b008d102c45140c5a0740c5811500c9101665180e0001e2000c10004100300840c0c00100c1a5540010b02400d10060340d2090b2a0080e101001840301504103010142021034061 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 831177607 1250 831176357 831176431
    0x1308030609040c050a060e190311060a050f0406051903020c0c090601050d0f06170106140f190927050c010f090b070c03020301060e0c1206010c020603160206 69
    0xe000c50b80c0320300d0440c0d8502c8840d041a0380200c1420b100250350364120745c149611110890f4854011802c00401c00400000e6120152030003800c4803000c015420484000c10240f5a9071410350703d020708094840013598415400800020000140310841d000d560350007080d0300d04140303000c2d40f034108200202da56412a02d4681481051702c030b40424101ea004d00215101c01c54803035400c3c060019019a60300041020344907030a16042c0c1c2c58501c1c2c0d04a441031007180180c0d1510b102841d80f041840003800b8010f0350210905800c07408450545410311002d042c0704e00141724809000c1208519210716010321001c101e9210342c00b55844a140300000c1012803c81d800d0a03081ca010145840e25171400c842d070402981c49a07480090001d410380510600011400a80f4000da00a01002e9500c80d6144103681041750f070300c40d10640a10842a80081032021507802c103505241c540400c95898000030034550040e03405907a802140e00e001c81401ea014000c940e0b0100390440341c0191107040c0410303000c14078040e01d104 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 831178857 1250 831177607 831177619
    0x507061815050f070506070201091103070605030112020607150504020a150c0212010f11090a140604090e01021e07120306062f0f061b1608090f151213080306 69
    0x40050410303c0340c1503c500c6900b102c101c407100d0410340b002034002d01c017a8000751420320070b1030300c51300d40c40c10000703070300800c442c519500d90f4516840d154544039141840c0d10308aa00580030040b18021800c00d0105100201d490140012141031910410070003680f507030710902c0b5500100e45205541c6030032081c01e01d1a01d40581c2d03540048540041c0d8a80100000603180001626103410310040860510107055544001c1d00c2005040f6180e06800c02003140880c1c100d0790080c4100820301c000811600301882c000101400076052050702600c8049908020542145030000881c01d14180440784a0f02403e2959038181088a40d003081001401e0000b0003030449040c0e4003080c000801088d6449211340404914070503250308000d590a500c0c1c4400c03013070b141030344100d0710960f50441d065169000c48040102035050511224250f564600c41c039000701000b02d45c030031002c02032041643c0ba01e003140074204800c0d00340c25507100383d410a200b180410240082100c000408032280c0060000e41c11139400c80402c9544c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 831180107 1250 831178857 831178867
    0xb0a1406030612010606030b0102060c120106050708070507150e04090b240303030106050307122703050909042f0a0e0c070807060f1802011e0e060403050706181505 72
    0x8183c1103140c0d0045610990f2070504002480c0340d069000703002d2003400342e013a1401c0d92501d074040c1d091805400503950943c4200c5004000700380c018001400c80b144180b9809040280395195142480411340c4180c94003610280e1220140f41c2c8206e50b01504501281d04004162030ba4907046510000184040c007403070040840740030711200d503c00444200400800300c0350b43c0d41c0c450348000c165400130385400740422a0348012216030003082c01564444190034410031090b420403c01c0419869010b0030039810301100b00880d2109490701002c0d184210f00ae520001510080c00018003a555001d50105403130410368120b50304582d1312020300e00304560229100c05442e495450303c142c0c192140c684028110035002600c0303401c00c04a44c01010301d54800b05400c002c0700c2d010017281c0d4014290320720020f000401020180c0c02d0700c0700c0d16240c8c441c0d00c4414544145954582c80c01304081e940550001d42f01640441000c1040da41c0c44060f004100d15111415425146420064042c0103081d0710010288180410 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 831181357 1250 831180107 831180109
    0xb0412110d1e0207030f06150506031b09120a0b0403020d0302040509010512070b0301030323030106020309120c06120a27080901121e0c0809030d090203030c0d020d030b0a14060306 79
    0x2c2183c4c06075821404005d80d25040d460f01a000307101400c5441c02c031aa0a05000400380780030801e40748074034440c401c800c1582d051201c60318465408500300c1a40000c1101c410f00030098208004400948500d2848030141050305010b40303410540c41c584d07002c06004105c180080d496108801f411030b1400c0e500c2040702c880c0c1a0760715003460059045503c034880044000002c0c07640c4000780040c10807020b02c080c40c0e00e03a049001c112231440240152005640208248022400e1101501100341090403e032200e4440d900e00050440d80144030200014500e80709104050016101d01c1d41600c00751104842c126402c100321540151121074051300045021440090b20313401240c030400b001000060401408500c070002c0c20310b40c02c140307202c0001e41e86001003030070741d1500403030400b0b0041030144021428025241c084401070000c10303d049806000c10300c159540c5450030450002035400c0354010b01340002e02c03441d00400300d841b40103a40b0f225040d03040c0100900315820f4190350f07251030140c034040c1c3c1e645c3d00e03e0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 831182607 1250 831181357 831181363
    0x312210c0d0c0207060f0503040c05060c150a020703030f0504020907080c0f0d0603060b0301060302011e031d0609060f06100311070203070b030a060f0506090105070f0b0412110d1e02 80
    0x180000e00d207241440b4021402c10360100c2c044090302c0050312009a10340d007115003120030b4001240c004091040028084c001031402001600c50f04200100f00c0e0440c0300d21180c440e41059042c1d0310b9840151300442c0724000c15405005071014000035030320030421803810740c0018002d03080250100c4140300441c80818010000503040310380d008102c03464956503801c00c0c42500b0050242c2d01c0103a80c040d1518050010311324040c01001e044030303016580e120050f03501c0c1c080d0b0303429404282d0b103031400d1641e100b1090314071810790b0380e81021800e0070001500c41480c062903503604000005000c051070340140001c00c0066501c03800c1d540c19084c51440c000548000c0c0c04040003ca00c21000080c1d458854400000340000306480118400e054200c41030102943e501e10360041900b032401201e501c404140400091544600098018140141e24011400e041600d82d80c0c54210169025100c000440003418100b03a0008031080ca502c860b0801032044890302d00300105021050180b0b440a0a6800c6150300214030030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 831183857 1250 831182607 831182617
    0x515060a080a0c2d4a061002060a02090a1707080f03090a03290c0a090605031905041113020301050f010905011704020d0606030506060312210c 63
    0x344200e890810701401c091034021014820142e03452414242000300060b910390386549001503500c0506458144009000380344140407100d0f00760481c0509440a000e40c0c8030b01d09080315028106583c10f1910300b4404842e402c001401c03070b806089010b101c7c13807541d41c0c001140307a80000950401600d40310000000b070804105640301200000c42c0d00000359114030081103034000c403404034046070034003140242d45688a004a121855010024400c200045100100c1c4c05a40202d61410303500300c946295140803541d041034070b50007030b8094007081e801c1000350170201041c0946403e041035419407074000905010f40910300c4030080d02d182c40781d02150800c150080c03102130f50b95000b080007100d40044a00c0100940091040720711a200650616155500521030032040e05c0040e92080d47c5001110040b00e00c070007001c0c0c402c07038000050301210801328081d03101c1c6001442c0708001505080c20942d00301450706a60b0030882c420540d041200100701d501c0813510f50075400b04e1110708802c90360382210244617070080c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 831185107 1250 831183857 831183869
    0x40504020a1e0509010e2a0a0c170a110601061701090c0903060e0c030c10270504090809040c080c09010c020613031b0e04030806060c010905010e03040f090203040515060a 75
    0x2d1000800d10060f41c1106c588130b02031114881101d07480c1c140601d500d9000c0d40d00c001c120301d0030402425407800d00c541c3c0c81c1c0c21076500615040000308649440116254030104e8050700056603c0340300040f141c4140410341c010708003440c00042644c1e08960305001c01c0c0b01803281e0551180c3d94100501400d006480b094015031b000001048006a044001519040c0804800d4070078007c100300c1a0782846c1aa042c03c0c01140546d5440d030381a1900c140741c1c4c80440980b4021040149606400110380c0d0700e500514080310700c56001943c66648803014003003a6205000c05006102c0d02004100b0040b5600301a02c40d280804d203405104400c4a0000ca041c511900c0528403071030180d440d01100340030020644001001400041445a81d540c240041c000b900c15100103000032140d0022807503500d081b00150900481c00000000c8407512030383d80390f00316505045081d000d0780010174100710418150720450014081c04070254a9894107980b65502c41c507401850140101100c004694540c80700400702c006000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 831186357 1250 831185107 831185119
    0xf0e0301091b0f0806130f050f030c01020a0306050d15020f160b071b050a02010c1a070806031018021302041d0405060a0c08040b06061911010605040504020a1e05 71
    0x41c46200040b01c48070035019a04500b80c080724002101c21000600c03e114000d01c034450006040140d0741d2411b06d800b442820740c0c503403203010003c0d04807402c00e00082150407190000140c3d11060a080a029034000342d00551240e012080e41c41c0210341241e6803009440314490005954005250085038540a04c00d8400c9071802c80d038583d00d08000b070b8420760700d01541440d10b5026444440050406188880184c0184180c000410043c015401500181b0389070384241c1400030f440d1000d0181d61100c9804541c80000190080700303000c45400c00384001c203810102410140a41c0301d05540c00305405441d414024000c2703141e0810703110784d106541e055a000d090301c08180c40243c0d1188041c40313114442504c0544550065402240081e05079228482400015846030040c0c5c1e6241c0d1035030701c50154006c04e4543c101d8010840c02c0c1c129002c0440340c0c1e40341400381d2510726155145c0c4419908403000e41d00094055480e1009205c00750780c640c030101c01254800d081074030a009404920a582c491150f010a4100f0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 831187607 1250 831186357 831186383
    0x3151d031606051303050711040b042a080c0f130801060b0403031205060d0b0402181003050c180f0702010b09070309030e040911060a090510020d0801060f0f0e030109 73
    0x59181d44606151402510240b08644503055022211001418014007160b02084000000342c00c1d00381c05041250002c04c001140d403494004141582c0b110760101d0b1901c4c4900200341000d042014039180c0b03044842c40e00e81c020745004140707818948288001510303a14000b10b004c2c0c0c01c0f0000024594007030040344000307000ca503039120b411100755002800102d02040c602c83d030395001516144034017403040600404241104013581c80f81a07085002910907030f00030000c0c41400e50046e101445903802030a550401d004101e180d4104030b07042406408116108046d4560344900c200c0a414107281c1252801404c8005138403401400e90041003480700041e003001ca20410000c00d1601984070610240c042e889108002540704c0400c411603014940080483c201c0400380b0f00241441c601400b440881030522404080d00c9400103040c00b90f20150080042c0e20064003200200c4d4001d040c10b0041a05080950b2001081103000d0440d07800c8203181300801040c07000091095500b50403188045400015500710b038 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 831188857 1250 831187607 831187627
    0x1606120906110f1e09060a030209010e0a030c090c0201020f09010e27060103180302071517040b010611060108070e07050409140a0b031906110903030301150e090103151d03 75
    0xc0d8004d4003000940448a41c1c901c60205009022140c4c410401001c0302c1c0b901740301c014203400a4205450781410030085660541150701e6000d000f0700a10301500707842003c03902d80008402650741440c404401c59005009800228210f90140c500210003400c05401c41052500441e042d01480d00000008484280e48041c0b801d244c08042c81c040e9000384c0c0e0911107040c90b8402e4500189108070000c00513031051000308106040c1300b13104c1c46500360ba4a8504d0309041d80d80f90410030048140d0f4280c6840300b203140101f003559040300715219a1080d140140c0316940c90240e001313403078201074412000c081e1400400550268854811140901022141000042c091041100681c80d0882d0340315a0a0b107030012004840c907001030f50780341d60008454901c951042c5c82e86c81c20003a2140d4200300c400404184100080d03503a0134400703580605024118100540040b800c001e02400400c03140c54000d806104c01070010981c500c0c5040070341364082c0e501103004800c0d10510036221041c4070417142c0750f0001040c400d0340 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 831190107 1250 831188857 831188887
    0x32101050f060306130c1803060f180c0b0f1908040b070305220c0f0803031e0408070b042f03010608070602070315090609060608160612090611 63
    0x16900203035454010041d615091002d20721040e10703000e500000007080c403040d2034403d82250100c003070b0b14070304000390341d400c0725044c1050360868201f142d003649c4802880b600034059100302500300c00024140200700001d40c860444540c0103000340340c00c106002515800007981c60080318038051440108281c040c141d0301008001c05410b0300c0031603007900d0305408940740c030f446402441d001e0f914a420a41e0345020742d2000140820b505807007103c00080080d0700040000214200800800c04000696500d18042105440500c09140380900c0c8103100800c1c4070100b018101510003980e40001405a1500d445c2420500c40002c1081d502d400303081c0c80038540c1c8401e5500094481d40b1815402031203916210100d00791039000500440300140d001c11010008210281005110701d203551800045040240d1a400c050704c0314200c00365a101d44500080005031001c008440c8000780318401080c0c01c1c4d007030440c014200c035280c180c003002840d00e41d01e4085c10f00c6001d0340400040c10b11a800951303525950040c080e0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 831191357 1250 831190107 831190109
    0x1e0216030b0f07020a030f0e18070201140702010e0309010804110d12030c090e1b07150930080a140f06030d080705040e04110d110f01030c0c060905032101 68
    0x707100000b8202044090b800054904803c2d80c1c0b6859904005601c0305086031062010030559520005101c2c0060700000768189442c01640c4540c008030740c003c81490002003110015140404580c0f604291390300100d0040306507882254240303007400c0540c8541c1400021720040c0c800c41e40d4440c1a16079170303400700015802903c001e45100d0300c0510040d103a10324161100c40c103910030f403090b03100d903200010312000c2c3d0100006051500800700c02d00700003040c3c50750340d15809149180e81c0780039611080102800070700c285001210801c2c42a04650f43c220300c0d540e6181c018503003030308400c0c0702c5454045401151a84c00407428029207201c065150314007200603684035642541c09034068040c001c0e095414500c02c407042c0d482070840d9111107140038600000007011401c028010f07100d0008200d1030340a81ea480101644180d80203a8150403045c8100c001c010f15113141417401418586842000d00001380c00c9601c1c1d40005800c043c00142a0f00310b806c019007188162900c200c2036050344000b440c080b003070160307090b4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 831192607 1250 831191357 831191371
    0x12110d060503160b03010b0901020a0f0303050f060d03020c0d06020d11030a180b0f0403022109040c0e010c060b040902040c09170c1807020c06041211101e0216030b 72
    0x3c0c00a542d43d240c480c2030324400d0b0083c1613098408100600200300c04c0383c0103145c1c900041c8100c0354040300341d484440b01c41f0101d100440010382c480090040350101010341c81d40101040b220700300360f015140d030040d560f4104200910701400b03601924100740042079040d141c041000c00c40c107004110f002d9107030780d07075552046502c0d1078840d1030507603002014128842c80b901450707406001d484003a00d4240664000c1000204101c2c01c510440100f0000c054415202100302c4541c581c1558a80917018200030a44844d00c4628081203541d140c1450a682d200705d9065620750824070000c0c00c5480c0c0404500034183c82d8502030340007410300209019156000368028111030040240300021f000040b4404d40316020000d80f0351b0f001e0080b03410040f401c0c0c81d85c400300e50481c1c0c090048403011142e500200300103401590080c0101d5204a11a10920121455501910b41c048a46a010344503212004c0c1c500c900008510b85040142d28040143d03034020802510300c040d004804000322596854040420b6008403000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 831193857 1250 831192607 831192613
    0x13110f06121519091d19060f060b070605131101210c0504030203160b071410060b0c07080f070306020307090e0a0b040c030203150603060a05090c04080d0908030a12110d060503 77
    0xb851614109412861744100d0024001110140045007201c080003030703040d242d80703a55056a18140030740c3e100d2007008001c030240990300e070104c034244031f0200c0d80002c0c106442d035000e58120300000340c458086150343d4242400c02d4102400c81c0b000c1090400c10303942040e20083d240444030410030f50131001500c22207200301d04640c0130000103e4005481e014500c10142403c0d010311950000a00e000b5401e0381c421052400c031103844040800080540e030490313203c007040c54000038002130f49120038000040904215001001e41100c0e88101c03558510366880041d20341603000c0041240188a41c901100805815480061600703140c082d080080060035071940c400c0f440d0824042d0090300a009980c498860031018280c0c0d41340703140031722945500050149074444855400450b069840e00059801038240c40745150300d87e410f200071146401048901c04c0140908480208002c01001040358002012850000140e100c481003020141144040a481400003c10b0324000300c10681c0c85001190811022 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 831195107 1250 831193857 831193871
    0xa03140906011a0f09040b0105090301090f170a080118061502030c06011d04140102040504020d05011502030408100905070e01120515100e060609060313110f0612151909 74
    0x40b43c0102d10840452640c03811041c03107840c507035103060791041c10f0110701810290315251030800041c2c01c50f030451404460207111a0200401d0020004102a441c0b41130705403103140800e0241c014080348014450744501880720f1403032201c031410f15000310004000404d41d1241c1c0d0445468041e44a82041c907020802d48181400012800e5130034941d03e0605860301e80c0c0c003040c1e403500e03103d0703150112000d20b0600307480d9000c200014064440d480107000301d8880039400102035040480500c1110320091050007158814042404141c0c0701142480d180360400d0b4001801d19100d1030010700b440000d45c08858461034a0000141d214909622400c0161140c4107990b6658605150502c00c3c901c15950780b010031400e29424084082003c4016400c804000c0240e800c110510000030059071088851412154200c2c83e5441044040c6000c018450f00440700480211203a50104106000d46450301c0319034114240810022054513040000352500503040710b20890b00c00c068258080002d00c10052805c1c90505 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 831196357 1250 831195107 831195149
    0x1b0c0322060c0b0a0603080a020307050c0306070e19030c030b0a05060a030c09090305310902030c0f090d050d08070914030715110703030207060e0121020a0314090601 73
    0xc24901a00c00340d841d144442001500e440144580040c01500f82aa40e40404804108000c000c0e0422407019401156200041d1506d0781c14107034040122030190780030006005c001a013004e8100b0305000d0558001070f0112100350302e020310045662014203180224940803060004881c405c0c1c0c03103911001003e00c15a1605028000c240e5090b01c80078104000e801e2080c012240140c1010800901905d030560515401300980c0c024801040b251805251204502c0c2c05161950180b40c0014824160304609520f081000803030302d8400c0058040c4026400554140a0382c1e4150701075283d2500801102e421088104024100c3c000c241d40b4078010540e201000100c0160317604a00e59815406805016070610301654141e2061602043c042800051305082044000c10800840150b0080c1e005008242c5030210180449036414005810040f001418000209a90100c804000c50300f150050751603c0102c030440c0204200301d643d0315041e40704001d000c031015000850b68169040081d00c0f04402c41048 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 831197607 1250 831196357 831196417
    0x423010e10020607320304030f111f02040b070606050406120512030702010b0d0f031403010521120c16120f030809030405120d0f030b06040e1b0c03 65
    0xc605680183c1c4810009890144240c0010703003090b00c03000004203030004036800503d0300c0c801e035801401580c201000b00014180d01c860100c0c180c01c0d0504004400d010240111078541c0303104804100140200502070008801c16030484004090001e0000d44914130780c0350010150480d48555440303241404e00109043c81c00d0b0100c2300544d235008000b84819507090840a0aa4000521250641d543c4070b00540c450f4648048e400d00c2248902004da58401c400e14000e44541110760055145d588180014012501c540007101c0c0d0440d03062600c0c030860417100601030729156003500c055841d8000441c0c0b0710341c40480092140803816030080c041c0e200b1521080c203403448542105001e040725400220000100740540e82d4507030488002c04c01d880c030303050700c030310108508005107850403106500c0198181e18080d40700d111020340d220585006c1c082c0d051541c000900c0d0740124003540e9000e40b03050703010490381050302c2e95940031100300c032076013030303110603401144039200d070010b40100301d4010300e0201c1407010f07a00b15 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 831198857 1250 831197607 831197629
    0x315021902010b0f1504092d0c08040b040c05131509112203051221010303020303070e0310090602030402090127020a021f150501020708060c0f0423010e 67
    0x1381c60840c01c548440304100942210990012410504000100d810300c0d41780640018075070b00c18101440e02041e16410300d000740c2400621115180b504004906c0c10781e2003001e054200d40c10040c0340c81d240e00c841c20440352187c2c5035400586c0c4100001007032245044284c2164070220000c0e03213200b1000b90744445040541c2c502151821001d00d00700710f034045d103440140c6203203180900c0d4600840d0480c0c4a40c2c91a213040b00d00b26003018040800300d80740d600720309621084091030b801d00d80010007035403542da40a941c0380805001c2c001444411923400619440400c401d5540d0460340b5424041c02c940307401c14400075841500d042c0c1c09245030700d00110710403800510030705440d0004600c0c400007010b070070b02c2031009410040d60b040440c0105100214207212441903000032034411480020101445078110300e00140c82e910260644d0040c007010080c1d1540031500940c8000710010081c1d4070050400402c1851145070003140e809408406a001b0740c5981c010005031090003070301c9800c0444101400c05c8440d44038 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 831200107 1250 831198857 831198859
    0x90708010c092d09020d02040f12020306070e0d0c0914010602160311180933041209050315091b091f0b0408030d1b08150a0315021902010b 61
    0x30f00e218180050414660024035069030700f0341c4407001134913440e500c42a684500c0d110740046402140a00451040100040041810b00d8211881700d20a07400319455000081c04902404000e00c08940396440d00112254201d511801800d45952501c413014010848010011000c03020340d4004601e66000041443d4034108612400c0d55a038a1950340c07181072040c3c0d00d06260404900c18002c0d039108403401006d070040d14520701600b5814044503d849203008140c4020700d014240501e02c0c0e50002104540a8015070030051000b001500140d0980e04800160b004035014801c2000000501c2030201c1510700802c00801541d03842a0015400607102c500048a141c0c008100c074089140c4041c0c07580b00e54018031411503000001c035658040b48016800c01e034040c55094100081c0607013215014881c0f0680d0f906a00d8040c1a0705001c02402030070321200900c505001414011400e8035561416141f000845d8004020703000342016898403030203504007050344d10302c0c3c44881006000c46030060041146a0070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 831201357 1250 831200107 831200129
    0x21902031209301215090c0a09180209031504140303040206190e030d1d0a14120c1c020f04060b03340c1a15010e011205090708010c09 59
    0x491002802d03600d0040c081d40b83d08003d000c02030411111019440907101d001580c1044d0004044801845003103580107014042c02802040085900c5401c003010105940841919251101c0d074014020002c0c42585503e81c0d16102d6900b82d09540c0309018180c45c03040b4440c24501000b50764140b403541c0d89007c1a20029408082400254155007000e52501422603042c64016180c0d4504404681000861250040001c900000f58004d07203000b4520900582410385c1d0450303980b440c0061400c0c2e5461000c071000d10826600c200c40380d12030030401c15810500350080c1000845513021001405031040c510b02280a8030303000c4680b080c0c0d45054403c40b012201e201610300d2a40c2d407032084801f840c0d00384c0c6040b8100700d1040004080e11000195504611384900e860f454001300d91404c2402e03412541e4182030703030f1140f2101c013007258050703041c1000c01b0006170a0901400071241c1c880140c3d4120352440544a170646090100250503100103040e104403100080200301441e4865021245007444e8018649052 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 831202607 1250 831201357 831201403
    0x14030d02060106081302011b0308150102060103050c0103110f160b010503060402100e190801063015020c030d1409030c190c030b100501020709050603060403080a021902031209 77
    0x49082417800f6121071051500010351060240013107514000000c0c10f50002e0045401c0052030701c0c041c0c0c0c0321401e80209000519541d891503480554401d007040f00d4a0405450f039400003961020303d42601e03001c070b4840710710580328049861700004055440c101520205649000003549040100f8018001c1d070b000381401c4c038030143c0004240d40002e07212501c01d07000032820a51039050325200401e0380c06405544008a1103915000c0c4881c00c1c4820500100398114114444582560300385070020034035603000c0f07941030b4030000340f00d1400b00900608c42e4203040b500000036040c10840b03065020005407428444090791b10780740c00d070361140d0341d006c2e1217175240503036000c0300034aa034094040700b10074402131045000c0d840141c2c8a58407030402030710680d40c070503112004207000c1c0300c01d41e018024413002e0b10003c08100b00b1407402c41d0000365a248080c1000d824019403802003002c400b0035130100d444484103a10000f2030049451002503603036102ca800902890b05440100f114400045080300400466045103140301d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 831203857 1250 831202607 831202621
    0x81003030806040b032805060c040b0301061d04020d0e12040b09220606020a03020607080c0d0203040f060e0c1507030248190f1503060e0114030d0206010608 69
    0x1060844104c950510541004c1c44c0d054640c40c00041074400c1e4600c89600a1165140152402101030146044024180700034496040c101050303904560592170a02c00c01074014211041c0d00700c610b40c4054000380006560000714205801c641e43c01c0b00303600700b140d141c14444941ca2a080c0981d00401e5001801008001800e2400342200550343c0d41000081d9a4500291001d0040307074110b621207005604101d188000b41901400160b40c40b000a00b840704891512064078000da00c607000c80c01170b60540c04804202440603141d1524195580644104290a40042d6490b0343e450440d072464030444d03081124100380301c02d8000f0b80e800c0c507074150010070010608021080540a5158417042c0d400404191440c0c26446200400c0400000402c03035035141c1640818841021030600c205090186400820030110200049200c101d032803040e1400f64501a46108802822403540f02c29900481840086030084481c541e40d80005021012200300f400141000c0ea2180000d208280100c1d030700e01c0c000f4600d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 831205107 1250 831203857 831203861
    0x151413050c0301060b09040c0318210e010c0b0c07020a030b01082a010c0f080f0a1e020703030e130f0506030d09060906030f11070f020301050901140402060a050f0c0d08100303080604 80
    0x2520317107181404200c141c0d00104ac1c0c100303202000010754002a141308030802e000500c840c2c50880e004946401c00100c03920f43c002820302e80b056480100b800c80c42500250704400c083c0d05842c1c0e8254010720049056030b030b82c180004c10a2080c0283e09003401007200010685e0041c95010412144d0b94903030422010002d4015504032701c6032042520703000c00301c481d00300005142d54001c2012200180d042c03600d6901c2d5100040c18481d05060821710501180800c17003019400144140450b503041c40d18100194241c80810070307110401080e61040c5082003c2104203c0075504464440d150640c121340381d0002c802d108945401c4644900f00125854035000e001092007a000490342c8441d040c008a61030904420407e602d80c0022000d445071040c0240040440c9070030b00903180c100600c04024008000c80064400e1550006080248940e10000e0354682d00380c0241c059034010310744e4412558481504150040d01c888000226000003010711f40011240711041803268140d07501681d6001255540c6424800 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 831206357 1250 831205107 831205121
    0x31f060e0901030803060a120f1509080706110c01020c01051501020106030c0b0a0903020603011e0b0c1e0708061303031b12021806030c0414040501080a151413050c0301060b0904 78
    0x50810f50071000820034603091510340c40189d01c20380500320110024285041d100480003100c18405080550300e2012a40840695007001e42000c800501d10142002001c1c0c540304040380003030340b9400483c01481490041d4030540c40717500000e00c00c0c0c0540740c614004a00302c42c80e0b40002041d146904c8018003642a826029001c0100035090000d0380035201e400061440e0001d910202001035a2500340c8594141d00f4244001013880420741418101d548150945801540e507008040441110740c0404611041200e50002c2c000142940c01d5420003500541110103008019004681001c03603580441c00c61400e0004900000e0b0b03989050308200d122220069804020091011095425450801e83d40c680042d4000c2000c1c1807a80e40d80c900c0c1c03502e844501030f58841c50620403403500004100e00b1401080081321690320546a00c580880245020000c141c19000188a06005001c0103141020380c00026100340c003540c11682d101000108240c01e890380d50144800e00c1c0c406011649032803c042e00a40 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 831207607 1250 831206357 831206359
    0x1a03040c2303010603110f040e03030a09020a051203070201110325021314010603060b0702030d140d0204270c09150504050411071209030f02130b0402031f060e090103080306 76
    0x9601c480d1000002401c0d60b041e6002034507490039032003045041c0d01c0e00302084084504150344c01d010f1103c0400c00291a40002004c0d11411034560340401c00b1592207218a4003e408000e10002d40c003e10301580c15580d4100480481c0811803480701c0b50300c500c0c000000e844a00350707103050000380039058011a40d01424006022038001c403491011750b078418640c4c0075412801c20590341d003a1042d894201c0c01402c2d10001e40c803c0b02d0750764041248a0140c1c0300850403441d201000d04040c2000c1d81100068800d6110b00746c0d0007400c4e14408500401c1d0544107080841c2801c1c42e40d0b04070341d2a008504151011284180690300108030040c5042111044468400104452600717043d400c065803000805c00740d13000c0c0007248402d100001003503c2044600c02e01c80d00c41002c58900303130700c80d141036664400f02941e102704082c0c407950350100b00919002450304070040002c00501305644a090030a01180c20050940c00b60701e01c0c548110000c41c00c0c9120785800b062149005201e54000d0f461600e0710403455001501c02 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 831208857 1250 831207607 831207659
    0x509060c070c0302240304050d02071715060a12121709060a0509190f02090c030603030708070f1a100602060603030d020322210c170a03090209101a03040c 68
    0x345d1407030600714002d140308a0156010340004001444001e0404006404c8003080300e1820441a060400c0094114401d00710240c904c9813a0301e900002440e100c9081d8010001188000c2c0b80e50100a400d40c04076181c008075460701c510080c0c1000016814a000b22400c40307407684640d0002da031403425604440d820818810558500707403034400c10002411080c28054038900180c024940c21403c16019483d0711038081c03040903040d410040c0010303460307118100c80074001d4400030032400184074802c0c0802c840d45510418500c05501c20244080c14218101c030f0070070300031412840008801c0c0c000304003584280700c010003442c03414030041180030003504003400390400326020024085100440f9820040c0c0c4a014107040f403010140d00111400314100500c03424100529288444005010154270407140f1017000b81450312542484c8048005020043c40654800c81c51028040003c0c0720f0000c40095540300120795017403441c501c280060343e110070740d0018002a00344400b04010069030b0f100d400300007188525 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 831210107 1250 831208857 831208909
    0xb0103380a2903070e0105030714031602010b040b240c19050d02070b0f0a1e110d0305010b07110d05060421080402030d0e03010204180509060c070c0302 67
    0x11607a03100c0641c00540c500e03494110610001c620300002007550903000c44000349140303003039100100500d800341050340c148400880802c04242c059203240440c00050315035140c6a10300310784984001002c0c14046000b5520385002c09007336051a01914a01c201d0180000034880041e18225a103c95107045207803030400c0c280808980080207020841d810f5401030102c240030910360400340e0601c88502c960809540c0145401c01c940c030003074015154981c003200006500c0307014180341070780c03c900000c0c03000c000d1040c0f5525200c642508142d8450f031041301c06003100e5040d81c5020702641103031828041d08080700c40920549000921a050400000c8c1014200c0d14031340c0600e558251600105890440b010f03070341d0352654242100007007180b000c8020285450201341c1400d8010903146c800e074101103000c210b1010807180c960b407004d40445000b0700541c145080303482280741306800144000e4807011828001c06021410564401c0c2c1900c407243d030045080b410551a580c02c119590360095a8940f003429060300c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 831211357 1250 831210107 831210109
    0x170715030e03070b070908060f010603051510080405250b0702032404020405130206030a0e010b130218040603020109090e010f1119020d020309010c0c0510120b010338 73
    0x741929910581e821401410b1254001d007100501f40c1001089521007010451100804000b080c1124450300700041c203600c0702050041400381e0103605981205000c40a402100c0d44a4005071207a8011010341e488150032010360481e50342c551076051b0307100c50310b04001d00c41c1d482010014100c183c03004045803108980300e03001c003c940c00c2c2003c41902040c2010200b0080d0b0030280203403588940000019400c000e0310ba800180340d03001c05032080d1248c5a071055816040c0109600c032a807030b200010070b0701070300b01c50700c156079001380d030040310010480124919094224245805140266903050710f070007041e5420800d01000900340740e4001c034074940d2207a00c2010b424202e8410f15003a500c0e60a0074179620300c520310b840c03400c4400c40c2c07a00c0070440d444100880390715a0302000341da14500b401d103041c80d0016043d05104000101c10380210744d00c60084898800fa2a400940d0784804560090081c4074180c55400154221500d0750b03180302c504918684000380810b00b40d1a41c0941c101038140310350003450b600d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 831212607 1250 831211357 831211363
    0x111e130303050d0212190b180f1e1f05040b061608040e040309030209090c0922021206090d02190b090a050d05031009060515030405030f070609020a170715030e 70
    0x550300803100d4040d0084091700a841340100c46a030b003030540b101e54a11040c03032480d1a40d0323100180400c0c0e10a54190201d6825a200f5419901101113034910100500b0400c081000040390503041018034000007400003070b5418117001e0841c4141d0020440c50800d03428942e1038200032001c11702107030184420800465119400c43c03121b40124066510f41d41e4840c2984140500c103c006440c004069104820104d01541c60702d4840741e000c3d241443e003000541806080080545000000039480080e903911030824101c0000d8140c07181c03030030300c080303030300c00da650060aa844804170b450380c801107150b5404803800301c2c803900c2681e90040b080e84100e460403c095202e1b00d0030841c030080e2a4001030f00010074003048140c1c0807801006090010b008201980c81c000004140300c603d102100010032010001400348041481659005041c82c4e841542d500c00b14541500189a000300c100d20814641d84041180e08103d103180544212490042c003845007800b04102100e5a0490f4080805454a401d83c038013aa0034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 831213857 1250 831212607 831212611
    0x1704080f060103060f1b0f020109060f0e1608190c0e04050a030e030325020420130b07150e030408010c0929070303020a05040306111e130303050d0212 66
    0x18060940741d415880c1050590f00d030180000d08081c01c042903000c26006e041c4030340440ca140c608042c8405a0180c009038058012808060b140703070318121080c81070381c2081d003000c4511080141070310124050107050605d910900c0c012103c0540c8200400d2100400030741000b010a4016080007000341d5403a060712000a40850b0121015001840840101a04195803010420049000d10300300102e01944d014285c0c03d51440307001d031504003103284065450341d52000603521044203400100144205882e001e90380000c142d40400c0300d480d01d00150b25880103055580556014120b40340d0f40d8a0418500c0140c035030a8911400b50004201c0001c00100903c941202045a500c96030345491400700246440220402c100c01001c000090304150b41003a42c017200c254950604006880700e9407458201c516024039003008108900e03103980c461072822490b024100700b412101d4407040601d405e0b103401000d80910303044540301e12001c803c01c0c00003d015002230000c18031550801810414a100c0518a103001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 831215107 1250 831213857 831213883
    0x6070305070203060702062238010b2511100e1c0c0b0318070f030b0a200c0c060301031209150206010e130501050408031008010905030304170408 64
    0x300148039011810705011203580701941e80040c00c00c92070a0503000400e541c954540c0c074032042d88030a400c0c08015000c11a0171041c081120f41d801608203071140c68652000d8849089102000740000080b04c9031000c0c01c0300d0400000018012501c1544200e803a00665422022900805040c00e805c0c41f540321003107500c0320400c0c50b035210034038041c003c01840002030020900703104040a04404030701040c9a02c100404565246030310076500c0da11511101441007180c0c2c01d203a1a030054403400140c010410003018107403401011151010740361102c0a01c116021106601101c0321240142d4140d0758004001e04602000c0600b45c500390b204100c0018200d030b0090300300f144d88408807030003150140d501451003005407410601508008412100103951120144070350f40c0840c0c207840000342000c010400c50070b610796005000340418106454001e50641045801907500a0007003400a00b0a105028602615030850051851a162038942107000fa0b040580c4254805e410800011855000c008200b420b0350 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 831216357 1250 831215107 831215117
    0x30906091520070f12020a0b0708010e0c090a0e130f0b01080c0108040506060d15050403120b1909050c0903060702060406050f0403020c0d031809061811120604020405060703 76
    0x14400b51402c080701d6040b88903401c021400c3c000c0d00f0005440d289034014054000001172030303aa0740030104919084d00a2801842505004184001c058005004506071402a00740d10190780c0c4080f242303203050152003400c80d0701078141081084070600310740303240741c021158529900c1042e176142c444903000c40a4690440c0c00041c0b10004200c0b0a2042c41082c403801024030b440442801d01e511556030310b50003d04994452a98103e5400401440118400c125145007106001c41c0c0341905024001d1100290120f080d036040083c1000c0d186401108141c20110f082031001c07196003000741e0308000708401002c3c0d80344a402002859a079503802c00c60700c0e124120640c000c0485103070503d010030507543c01038401107840e91008107100c0041d17000704802520308002e403810740d905021800d04a40032003240e9500d08041100d8400418268016000f01d002e541e42c098445175444100c11410b0101c07024205d800c2c035001d50500070a4002e404220845400c03030002000075040c90345420000d005a880118100d000c90 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 831217607 1250 831216357 831216371
    0x306190b1602090f040b040803060d060c03020910050f04060e03010608030c0f010c03291503010602010903021c0e1c020303030a020301032f15040306050108030912010614010309060915 81
    0x21908043c10340e4812007a4032852024100303a0f580060240c07002e00300034007940c3c1c080009130f240d40380c0480e03402c0e941d60400401c1c000e2410101c00034000354029040c06c1d01031100f260005120500490032210090351443c40e0700e151914000c0d0848000080c2d0740c019525548807500007403102d104202030615020b00740c002c0c008031500c0800e2142122a50080d060601d03041220110040c40c5040c04440c0d0b06000402105161841000040b801d0b00400224101c110b404400440c150341d055204441c2c05121345c00311002d0382480c09400c20744a00c012110700c00030303080d40c11506840c10821020500c600c5480c10408101042e90f0000381950400c4480d4202c0941c04801003080c802d440c585001c281e561000c000d40c0c44840c2001e901d540c1e2144801d0507000b020070b08a9065004d204600712170046130000d408010f46e5845811040d2070341e000b074074a6413040e20111071078244464180f01300c2013101c48000800441d139041000540140640741c0d810799010b40d540c0c5000011805841d120b6080003035199001501c2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 831218857 1250 831217607 831217609
    0xa0e130e0d030615080403020129010306050105070209070e190303021b1c1e081306020d170411061b06190606020304051c080a03090203010612080306190b1602 70
    0x5025801c28004142c201407080000d092488841c3c0f0070741c03050b4a0300c024255070b24241070f805045141034a07100700003130805a11800b00e0f07040240d88040d109980902000d42c0d42d00045070035010303201002e940301c00c060f40810f00300d074041c03c1c01001d40e40015202c010000c02c0d6907013144103000c6a074011350141c0c000e036015020b400410440b81441c2030301258000007070f40e46290750010344850440e004102c01c1ea46040c07800082c1c0c0c0d040303882400951290816695072040d0040c141d10100621805002d48686510041003d008604110000400c1aa001d40c0343d03541d0f460300c04041e00030320046904031104102085007008480d00307041010301c0c204010070940c00e2060030f002e43c500340007006040103850f1400c2400700ca50b000c0201c03011601c040325000040c0100752a88291104081401040c095000541c00042174050300402c09041c002c4001b000003a5544000003602d100303008004028980402c0082d0480c41c00300110314200c21030802d000300c402e40310440c20700140c2c0082a0000c1003500396800387c0071 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 831220107 1250 831218857 831218863
    0x110304110907052701020c1e13050f07030903120606030c0e03070f1a16150e030304020603060105070309050a1e080c01050313080c1005160809030f0a0e130e 69
    0x614030b01c0c00c01c0c64001030601d103120b0304d02200040c02d40c0d200d40c40c028a0180e0300c20842c440c1ca803d0300620407509405007064103907040c03449006039030203403445082260030344185101d44c5e40302c2d00ca040311241c81c55442d80c00450041407205804c40034040007101d00c4000025520440b030141030503803000a518862520f014005007a450314491103940480021f0202c0703250310111034201c80100c0c140c40c04102046c0c105444074001d014580050207403020001043c803000003c4c9038054810355808020310b0300000c1d40191644801c960181d0460000c00c046195944120002d00819001c0d00c0c00c48000b80d150000104114245c4d40708900b522203034005001503000c07181c001801444c0d030000400d507544101e40081e099000040800e940004804581d8041c0043c4600f02e8a48103540740586014450031030041c00280000e4614440400004116111450140704450f010b0800b010080d42460546042199544c0c0072081800801c441801110741d240c8550141001d036582d00030012a06101d00241c07649 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 831221357 1250 831220107 831220111
    0xb0106080a15060e2101050115090501090b0d0e0f060118090f02060309031c02130e04030e060c0f03040b190215040803040c0b07030e0a0b090a0504050405011103041109 74
    0x800c0034a4022441e0700c0b10380b5454220300b1200e403400c00c80c1c0402c0b064000941c0141c5601c41c00407030301510000c1d40442c10b030194415070586025070181012035084003411140000c280c002d90340071440c902410300442e441039010307141020a440c80400c0030344298003064240048070145515a80c006c000600c00c5840300340b0780c10315014461600300040c01d19501c540d1805801c0c403202900030040000840d41d0038405100305c480c4018959000e1101c9459401100b000354410308848040141c0c1c0c0d080459603038040c000d0a07024603015a0340c0c25a1018031400c00c01d0942c8092a02c510502c81d10038040041301d8144090002801e02c40101912918058a0100c451030112200821500b00d44030f0340381488181c2c3d0180350005c2d002103505407255240c0c5040f100304c125070780144040c42004030354030081503405020105030400680340c100a45680d4562031889025842e401c5034800700b415014001c2d42031541c00294002d0082002280505071440b500c05140e01c2a50103540c0c0c107800030882c409508000f1182a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 831222607 1250 831221357 831221371
    0x30d0f0207151b140f0915031302030d14091e0d050c0405010807050d0f0303090c03051f0507050a1d0a170105010b070f0219170718090519050312040b010608 69
    0x4203004448413079003032045910704008000007045190b101e440e5146d01000003c6503061840d03680c02d00d0000c3c0c603100541278404900c02d110781c519824410384661401050034058044417070502c5040401c0010301c030600039981c0c030b40441d00c041d07441069942115004202c0d0150740074200c01e6225009000c16184160042e00469002010801c20fa4482c0740031030044503000841c2092030940c5150803809842104030103080d00c0c10544012092040204500b00c010380c030118075548001c002c1151600390740b03041710080c0105000388048000315000300511244803074001622507091056a0004003150080d8015041d00c0e0141c0403d1040380307002340b01e10fa001d02140c5201608010807550350031151501c283c002800b545109400b40f0441c160301003020050b10a91014554055450b840d0aaa0302c48610652400c078401062140c88120148101030000e41c000018000300c15085804802d1108101c400300c40510042290028054140c3c11a50003544034800c000360b9549410300c01444030002500d81 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 831223857 1250 831222607 831222617
    0x4020d0e010f02090102331801050a0608061b041e170106080307080c0c040e0102032211210a08040e070206150f010c080705010204090c02030c030d0f0207151b 70
    0x40860b0380c0021f620511a2403100455049480940b210305c280342080390450f001c0e9040d6420720a0141c1d000200c02040041c000c003c00a650340ca40764241501d03440d01c1801c6003030b00140d001c181c0c40d125403060102407403420444035191640e40c11455081c00c0c200740600700103104840b424000d003450b40002260440904c0d00a1050a08002c8802d80781d1150030001000d2610004211400c44007d12040352401c0e002481004148100b550183c042c0d030080b180000100c1c03c0211980306c95161304146000c5540000d41807042000f201b05000f215411040c8983c90004617588021840c076003001358403401c40c841d0000e0360f11245082d0007214801e101820001c2590081820410340c0e00ba0740c81c100c00c3c4920201c034000b40303010f038480059030192280030740a00741d424009100010311105400500c21545040d00c204501200060b0403a00c0740250801280c05400420443c0750702a10b58100b0002c11046440c0185401500d40c0c0c0c00c04c00b4844600240d5106072280c0d0514500c00c400c0c600c00040c00b0b580d0401c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 831225107 1250 831223857 831223867
    0x11403070b0a030b0f0405040b190c02070905090703050a050a120e0303070f022404081e060a02030403020705060c0d02100c021225050604050c01020309010c06180204020d0e010f02 79
    0x2103007007240075039502d542c20141d460a010600d40e5403900c44c141e040340c02500401c0141800e003803401e02d00c501190300700740380b003203004c0401040200c030321440810321500da001d420407600f0300d40d01d00040d18014140014910a004021000c900180102c952540c42480100070b1034415141c0650b2a00940004005000300c0d2259040c0945010044514159000280910150152000980d42840346180c0c99459249004010300a0a2840280191407107401116001900000450460015074007041070a4224001141c0d840c5400c2e000382d27401034860300582c1d00094071070b404200c0c65000203290115a6000c0c0c41c5495085030148001ca0100710203890500c90105031801c00b039a40c80c60044400c1c8210300000f040c0c0c1c000075100c940a02c003103401d078056044400c5a0b041ca00d80d1008203403070a440e50b000e28905180c9030f40c00003044420701e07401a16070441043c0e01d51070340002041111000c0f80c0902c0325140201c0141e4491004104407082800c0020345502c00e01c4c100b508560b9412000d18582e841005 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 831226357 1250 831225107 831225119
    0x207030318210f05070603200f091e03060703050a15150f051308010204050108070801030b010314100c080a060f0e0a0203101a0d181a06060702090f01140307 69
    0x2068024820b02149a6241e007403518240460501d000034045010703200011407440c1d8503400244e00e0800350781e8003504c074003208100c50310144201d103000c4c41400742c100081c0075282454100e0b1060740042504c0b09800106020100703007040070072210f20000079551000c203c0c0044003885202440f52900060042080c109450700100c06588059401408015000351a50034414400c80e12100441c0203049a160340d100c0e00603007c0d4021f4020680881c410b00c0c000340400d4071901007681281d070001040c0c8c0c240d9107140c0b47c4600c07803258900c07441030030300461400f900380f03010b00c1c050030400100c42e40d0b45501c00e2a04940f007800701c8003181c00c0a24192034501c0108180c10076602080d403c0216805c1c010b80c1d0340c03500060200d45094070740c0300702e00845003484940346d0071001d44080d08000140c0e000900a88101c44200041d110440c0e600a1895042c00554000c504043c07055660144e809008186052170070b400050000c0c0c000c0319078101544104005001d01d04c0099030142e02c801e401d400400c0c110342046 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 831227607 1250 831226357 831226379
    0xf051b0c280602181f08040602131a040305010e06151e031608100207031205070c0f06090308100501020d030e03040b04090f0c050c0601120816110a0b180103090f080301060207030318 80
    0x7d000985515008500c3d0024441040c04402c01440c14840801c50021214415111a00035220030f59555207403002082d15401c000c01d03803034854900070520100c0284540d0800c0201d0049100b04003011540c1d00c0c0011540d00c0030000054261082170702c8400062808148138a021140c5015010080c018021100003039004207901500c94006000030a03280d48103003040301e5502483d40003402220900e0004020302029038001604a8001d0381c40480c19075961101c03501c0240c00344250740c0140e02c01c08a49103903034405d43c081034002e19a1411350b45401d5898807a01c0c055042030704810081a0740c0c1100b58481c140c2c9110b84443e417802818884c1c10101105001034031800c0500c0b0742142d00782500614000c0007080400c6070301d4001010703001c50007980c5070300305140d2072a08030b006039010301301d65500482d00f0380f040c0b016551000201200300341c1100c120001100034111420044440c07695503805500042e00c51005103018280d240c4c001c0c00c0b06451400e0003040c0402c20751040b1025000e03110103100300e0b1042 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 831228857 1250 831227607 831227611
    0xc03021305041137020601030b0a09061b0f09050f01142d0405180105030709110c010204080f0601060305010e0f090a060f051b0c280602181f08 63
    0x40302c0001d007003400501c4072070191041081540840409202c4c56403040048020344001c450004003448aa0f0344540c000d903174800080c000600740340030400c00100c00214070381250410910501000c150410340e0418500f01d80c409541e5203000c2000c07900c0e403160107640070889000070302c011a103800d10440140f001030800440d500349820040c1000581c3c50700c2852020004031822510114000243c55544619403d40c22a01070640b1400000c05010030250410804605031403000b8040d001c89403400c802c00c0010001c0b4070350440410424031004040c00030a102400041030984007a00000c4410490582481c1050b0440381c180b500d000018030503032070190f420b01d40c00821428440716a403030384c071801d0385043c02032031004002c28203145030880148a9030700440d01910400b1408020400700303a1005103a070049911a503400d501140700d40700c2155661703901e41303450901d41030341c6412601141c841400766400620020400030310710030400720320b0030081919030510109030b5040a44184151004004143c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 831230107 1250 831228857 831228859
    0xe150702210f0406140c0d0e0f0405090d051602182a09130207200a05040b03190c0e0123010528030b030a0b0604050907032102160603050402040c03021305 68
    0x7010700c0841741c64030700030101c03100700c0345540440300701c120000801004800403c0d4128042d107240e540040060600d40101801030754407501401031660130034000c85654028464074040406400102d1005d0307144c81d03400b010050740b0f920400d4000e240c00c40503481c8200d650b10b07a81b486480402200a0b9070302e4103c0c1602c2411104403064607103200c101641c50042e014210010307003103901c108102207130b00854001c4807550385c4003601e42500095894003003000b251084020070350103401034001c0c02d001d103484015400006200b107100200841d200c411851040809030015107802403805103e00e181901940383c006201c20900e001c3d4580040798002001c5800d103a5034148461800c240300700521030083c2c2101d80c5228001d8101d80070000790303050902103400281c4140d4095450040414603440700491540103481d0040001c10042e0580520008666414100f071070460041e444c0042c2171947d520065001400690313800b0902c2d08040c0100070480382d040b010030042c98410010100c4544809040e101200d02c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 831231357 1250 831230107 831230117
    0x60203040b0c15160e030606060f25031815140315061c05060d050c130f050a0b091e0a15090203010806071d010e040e150702210f0406 59
    0x5400901c0e00e0401d2814541030010203080c04c10010048820001e542d070b80941d130b21014141c140809240c0c03245d0060b98407580025003040354245024200d002000a851100f00319440c0707028510350301492103442c180440c001032510f040940e221581d00c0480f00a0301000e01081560001290701505040110801003848030002c0700141007640655100f0321180c001404071380da6001c503042a445801c890041f110202443d0001184803407c0120002c118294040010007900500204002514032000710700d0450315191602d9425403440ea005080c01b81003a8040403a001c0d80960030407005020040c02118912003414003068103907011b000345900803048036400501075441c1c2142c03078601034680d006a9126400000002411400040c030548241501d9503a031051007200a6404203200141c0007040c002510f4080c2015540b5003640044160500300e01214030a001c10501076030050802c880c28005a04542c5141462680241c018a01d010124895a10704070503101d181040d8000d5001d1242041 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 831232607 1250 831231357 831231367
    0xc0c0b091f0c0e1504090c0816210e28050a02040b0d0605011409060303070302030306061620030606030a02031c09030b0f060a0e0106050a0c0c090f0e1501060203040b 73
    0x24041c3c1c030740b044805805080d622002d2200a100c04980d4001c0c0b143d0202e46140a00c500d0003684903005081c011045401d20803001495450100e404403c114810982c00070758a0800751444610300c43c3c42910507084014280d42d00c800540071200c0d05036403090280d072010304104000003800100b111614a035044800045460b1004081120180b41d440c5c0281200d180000210b0320880071081e2812110040750b103d582c6a481c00c080c15200c0c00b43c1440207015034018800329480307240a0003d00140000c000c200101768400c0e440782c010000805000d214209008034000c0070a04040c0640d5034418025001440310040c2e0b40e003ca40d89224004004640c40007562091100030300c0340c07442200541e000203040b05c1c6130500c000070080465040d102e091080980d05c1c40061b501419071a0607048446944541c0d041c5020b1210541c0c1410b0041021600c1c418403810100302462107105184046042c0900010892240398105240c204100d00200c20645520010032030503500000310360603948420080c1e9154 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 831233857 1250 831232607 831232631
    0x7020603180c13020408014515091a1905150d0c1503270f0204060902041703040b04030210050903011a041a010f050c03070203010c0c0b091f 62
    0x4040907140142d07000e2400443d0000481c0e050700a0415107000000070019138501205052003410121084501040b4011502c56441001c440f0b400070345101030004844078030340e40e03104c8017500ca540d440005801e0391428802d09002c01ca00d10424010900504000c4a0403c3c20406030036000800c4482080f94403080080c0780008800004415101c0183c00381d004881185800c00b802a004d0068100354180c183d40450300c10310034029030403000805194442c41c2004000c0301d028100b80c0083c03d4500180c07842c0040016140c82c440c2400403d01da260051b110b030304140c0c5480d494590302d20600081d520611090144003129011a001c5941c11100b421a44508060135a824081d05000c903526520b003005203892582850b2240003120801c440801c05581c0b20441170030500b1100303102c0380c005600c0c0b040c061141030060340240541d83c145800c0741c0c1040070980c000b030301751403002290200003082400800308001c00441e00940066189000e1b04030303483d000091701d001410602d1a001655201d03c20b01c540 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 831235107 1250 831233857 831233863
    0x30510052806050d05030406110c01050a080405151923010b0a0909060306200a0816030905071e0609030f0206030a0209094f03030b0a24050702060318 66
    0x1048080c00703400b801c13001c3e410b01c0c5440360414451100031550341e901076140480003188014400c8c005848550401d1700b140c404480420b4000c0c01280c903403041850652008200b104d9207840391001d050098100700100c5000010b0b12520720408070300c0c03410701c001d4a100040c83d1802905440003826010744862a1035021071b51b400c46d651203544868500328012041c010780c0d0b0000d00540d0181c12a40001a989407980c200f10300c900340c3d5081c0041c48440c003090355003a9001818980c82c101d480c02083c004110b4556505244007076000700e0003444500c04850303060100c044010018815070401c2c0c2919455034840c603004028450000713205010000020340c1511180e81503500d42c1b00c01502c0c0c54400c0c540b8045070510b03c40594841104041c5e004000c0c204a055400c40f41e00170340020303161880f82c015004001d1880100e0001c200c00b415255050b4140a8451035208170081643c0c6880080390202c1c03590030200c1c014416a80003c01104000550241e10b46904483d0021042541c92600740c07845068a42 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 831236357 1250 831235107 831235109
    0x1a0a0f14151602010905061612140c16090926070f03030c030b0405060a03060513061506030e010b010f180306020406030209030f0d1e030b100504030510052806 70
    0x14050744040340751219078003811154501c0c14400e072205c0c04255210002c00510b070140c0c1c08105042d08000b40c40c040055411001d07030040701c4060409003410000014883c0e07164100194008040d8444141ca80b41a0ba070b5000202c004d0024600c00c01001c5120389504540c845100013011080d260b0542e0000b84580900450317001540020861f103400489203001070180c510900014002402e00390015864a4948110380c02900001c0c192402c0514596418020380b00c01000f0107840c400c00c10301a000301c1c00502070300300b07458010b64a00c9006402c101e0082c0c210b0320805540c94071a0314151491203680d0b00010b0300c00241036641420b00d507810210041d103400035466003000300b815001140014042c0d406401400340b5031400c9003980c107aa00c1c05044641d82c0c621076980103000a240705220070402c56204180710300444686000300f4041212070211350070400321007100000860000f410018014184503400c24014a0b540a00240c24007001985081d80c5c05c0700008031343c41104060301c50380c3d0240e0340024 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 831237607 1250 831236357 831236389
    0xd031109061927060201150e160302040914011a07050705090402030102270307050301110f2a0a2001020606011412130501141e1012061a0a0f14 63
    0xb030b0b60b040352011090414a214400c50000d036003442007c812090111121000352402e03105510200c1e13031181400c10b619025204c089080c9075080101003500601c50140349408003003544039074100d51420100c2001d0101e141c1081c001000c1c18000940092008610881180c03401c440490998589000184c024459a00041d2545c00f0a42e103078041c070b0043c01200d02a88908409484140366204185420394014104d00040c2003020498200c84142c403c001d000c15800d01c10064002118041c244454031108036a0b4150390f81c000e04100c820818501c10500164440c0f00c0100190116180007030369540d0080c0145040c1f01210b0450808900c2010a0b515a007100750140165400c103060002050400c1c0042651154242058403109841950703985004482c001c03080810303540d0b105607440c06088040d01c2d10b007000c41180000500e802d02d110902c0b050901904000038007032185401e0541c1050303600d0101340607540d500f10400c200e4590b29991000c0340e03803c010080803103c001d00040c80c000b4141c3c0e600 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 831238857 1250 831237607 831237647
    0xf07060e01090c0f050d0b0117242a18030c0319120513090b0402091329011205040f080703020304090b0d120f02010b09090d0311090619 60
    0xb030b014406410003440403150385149403903200d505d9009200d00084c400760003416420a07080104443c40c1000d1803d0280d1141801f5039401011007411801c0a1030410a0009100b004005001e1280100c1e40c6c603180c44019261200c010709051051071076140148141545071140c4030f003940d07134a52414008a158208024160750052120284400c4103802403402514880c141102012650b0701480c02c0314517500c800030000640a1600400f80080d040308054250015000e21002d84191a1291301031802d007020003021a10040138007a00420301110340c40078052100e1100c02848990708034204004004619502242d00e580d9410680607008041d04002c12480300001c0c60303414164040054002c3d0b54a00400340140c22041d420004007500921001d46a241c1207980050814007504006004004c81c0c0004600e1000c10350010300203100844820a0940091680c48007855040c070920003440d80482500f4103050881e00401e803640540d203510480c0d18400c1d02d44420b4503014824003150740b506405c4e4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 831240107 1250 831238857 831238871
    0x20a092718030305060d03021c03150b0d14070e0d111003020c0f010c0807200d02071409100b0906040902031323060c0d150b031e010305030f07060e01 66
    0x758000400c03041d903041d400685007901180d02c61a1a00b94000100d8050340202811540602c4d403105040b0201411010b2607a034500003504075029260280041140d03203040c54507650380440c10300075034840005084001d0665401c210b400780c0c11110113103816806a4185602c3c8410f85840d14a0010400d8405c0d4081e002c80a1148000d42c0740d0000c00c0103580410036038a11400640c00075081e03844043c465008504040b00041601d40704d9001d21008034040c90340a0210427800f558142810140082c003001a001000c00344250241442c810103611015203008000d8a03028501104c11b03000d900517000000d000003400f02807591a03c2c2910702801c2450011503403400c1038440100401c013a00022103d4415162a100c40700d00d501c402c0007030140c1414040c1416549a01c01c0040981c04400031603605030782e42c04074848801400e1160806800d00030461552410000e1003401d647c03401045180110a08000500020b00c012003611521010100131946541080c50004060320101d081040190301e8050 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 831241357 1250 831240107 831240131
    0x406020307090510020c15070b0907030611040503072102030d031a0f0f010804062c0105010b030709060c020102030403020d0b0a0b0301051003030c0c05040212010801050604020a0927 80
    0x20003540106199160054265680d205002d000380505400c00007681010480c0802402c0620486d03181c00c683c002981c0c980744040e504c0480c80308040e030354103015a1003114207004005140c81124800b0642e06030160400303140c100000c2d0782e2041406030076521500c251058684001f04082d402c0070503802070a072403044020420090050010729401f46d07005200c40c505840c0341c18010003400079000040e1510505c1d0300311100550350101c0141c02204c0380d43d038411207200c000204020045041c03100f45e00c000914813014008078203407101a00900b02c0b1820030414404581e0300305240000300d0f003450810206082e89800180e04500896001941015010500c00c081000f10074400340f01e56181102000320120744400d05080315012035000002c5820060148040f0b40204085001c03248074481142d5026102d070003250990304881400e59041d0010740062051801c01e00031642c0c400d40a840031410103010320401484c2c03441510568510364a08011030304031244050225103032401103e828403540801039 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 831242607 1250 831241357 831241361
    0xc2113060f09090b01080105040203060d0804080f0c180601110712080a110606061b0f0a0b1e06010816110703050f0d0503010b04051002030d06080a140a031d03030d050406 75
    0xa0303501c40005910100108000071180b040c04110034041c3d49071040d80c2c0c00c20090100a500140031071b40c2c00003406210000140c040c03002030005d03204600240034a5040840e806150000703840905202d40303180d8640420610320218410352111092900462117840365210500304451500080750201c200d00c000d80c20700006070018561441c059441c4040c84003403500700340d1680015a522948000c081001d00a5519214042041106400291034401e080c0405e841c4c5000500740e41160188000030400040304020354141c03102408054072201d507403400034002000d080b0003d203103d4582840c43ca03040803951141040b81e1981c0b01040c119014641c403824210f6450300d0012a0b4003051244440d94104184500c080d207041b1040c0c41580c07820319041408021008001c883d07034a046200900296030420355901a10300204407c0c00a00305494030750800352001e41c5020b480582a900000010000a920207404a510b44100420004800c84580040c2c258800c25810010803401c0c64248001e01c0b0b45a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 831243857 1250 831242607 831242627
    0x2108070201180f06090905100b13050901030b090606030d08040305031302031f1803090302100201200403020a050904030e040507051303060e160312080402041805060a110c211306 78
    0x2c0d1150605c19a481c000b0f43d05544e0111001c0c8459555108204044031441010b4401801e0404904d0134003500e0300d02007202060240c0c02a105c0880700000e001440109011940d0080380c140c003d031001d00c1d90f80d1000381200001410017800c11030004006408402c0c0d21010780049580181031701c56540801700c40c10003250640c078031050003a00d40b091040c0461020391000308007542c551540c404040c995000c102e6103c5440400c0000d554940051000300211007001080580d410300382e09440300d045005000844045802245c040d000c20310510001c243c00442200003654100c40104d6640c1e07580504450f240126218000c032200e81800120800c6101d40090b5000c1000c0d01c200c44a48103102c02a5500c45903910015004200c101d1301420514428016258014000362010070104542000610401d071510b609980c140c11010074800324804a00a4001c0086002e021904000541c041c1e95140c04a916914030004125040441c00b0351070709080d560b0071207040c450a032119076a014058402585 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 831245107 1250 831243857 831243869
    0x92406091d0a1d0f1e0d0324080a03080a060f030f030c080307090602060c0304030f20100902030c0910090b0d020603070c0c0e07050d020a171f2108070201180f 70
    0x4400c0c441c103a480d040081003012a9605d40201810581c1200550040141440e54201d05070701c207090068007206d06028030300800c41c00004041f090035500b4024091180900030000c0075003013503010020400850201016250404104070110601d8a0301b903821416010300204024404000c00080782d4009101008035181e64095603526612000080d0180c8030482e8000c0126100b140000c4025208800c1940340d444c40c200e00310b0b142410042d01d0703460301c0c501400703440410b07444010002c210308050082c3c891b18501514071242a04000c0a0714215401e01d01890700215550f407030044071545d43e601032080a40c0c000d031103540d5074141164018040b00d1080002e0300c05206c0300000065561000d00114400c080c50f903a058100801c00c104140170b0751101010008000161070812542004803a030a40180c141c4200310818a02d40e00801d41c00c154290b22642d1407800300500b19061401c5a90051a032a5126910b1a5214258401030303c4a50f503d04100000b6030349401301042c1e200b202621082a541 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 831246357 1250 831245107 831245113
    0x60e0409021e100e03280813063e01021e03011a0703020309090705070209090f0706031a0904060e12030601020c0922060204092406091d0a1d0f 63
    0x3c50000240c8120044203241038240d1300c10300036006850380341d08840c40c0903051051059101021915541c88a03040302082c1c00e07100001c02e8041008640046611141c104c20701c024564955412001142ca244222180703011180d0580072080044002e50440d8440180c801104264600c202c0b90800340b41c100b406007000011800c0f42401405005905a0314001d5041c5c0c001c44c98a40458188081c044024090700c06000061101100581ea00c03c0c1c4070384a0941d4100070251141040d801e1468265141d22000a240c40c0221980d8001c120800f0600c0c0c030745068840f910b094440345402001814030b9500140d16002d454951070a005d08080218003841c8241c0c21a0140142002004800032044d192819800b1041031000c0f0600c0c035640d80c24101500403140181403665410450703040e2450103010440118070b83d08880c5a03a52446000c3c006481146001c40200341081c8034455000c1d00e5840340030f1040142c0380002d80c06109904880607203440c04d621024501e10801100c1e945812910100b20030f80 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 831247607 1250 831246357 831246379
    0x10b1012050c030c0f0703051603170610050406110304150915080f04021c050304080a170301030b0606070f060f0f0e010c1407050705150c06091501060e0409021e 71
    0x4040306081c0e1303005955002283e4545000108410b00551100e00103c0902034144440034006002651451019029890307804d4402190b03641c2c0000c4c0c00c1e0040000384594001224608500e5000c82510265107003802c10300b50120581115038a980076a0b0701c892003002806600a40c441d80c880c1c201402c44241844100e40220008002d03180003404480b1a0840a03010000401502d810f0304d29541710343c0e040300040800f82840c0c80d42810b650080d04401e03c0781d40002400020850701d182c1994221407658441c608650440c1d540000008000e0b044901c207800110f14113040c050b03c5400081d103940c0c041404c01290020741800303006028041009001c0e5403074240c0900c0c40d03800600907202201103da807080b038003e001c60303110756043e00640c0b07060321940328060340440c0503102d040110b004450100c0800c1c0d00c0b021505192458213800030904466034001800301e0081d0401042110b040d502076040074194420a00c010034020a080b250103580000c9804224491510741d81c01580d0703e00c4142c82c561500 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 831248857 1250 831247607 831247621
    0x15101707032304170315040501080607020d08040209060d15021c0c110705041d010e1b100c03080c0c06150301060803040803040315150b0901030b0a080d030c02010b101205 75
    0x2011040703c01030b020400b011160224525208019940000407011031a0807041c00e84c0400c0407608240c00990503030b800002440622501041000403452413464440446c0c9030903808510050000b4104501035004030201104022005603900d021080c0c000d4219200d40d0004d161525203c1c1f10030164140c5480c003c000340c4003a1140b003840c40510b00a500804046281c542408001c0401203d40340059058141020302080300f80200b006407600352009000628151400420640b040a481c038810751902c01c0d1480100c0c1c1195903032030b140380c150410412a54600b41050313038a10840714144400d0182e20108080714600d070888918080082c1e000b082000e8540010b140e0700d00c02c1d0701500303845900c144410030000c4c80300103c000ea02d40301c01001141090105480229102c42600055507101c2c0204000a29507403500c60190090000c443d07242100c1d2031305070380c01d840c2d107512001402003589603520300c0140c41c000d412108162601401c03c906844034504010b044a54503204074200c40e04041c049159 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 831250107 1250 831248857 831248921
    0x70201060e06300c0d031e030e060a020f070f1212061d100905010b180a14091e1603060f0e0105010c050703080426061510170703 57
    0x2043c0c61449100550011024110286900d90744502071082103103601181d190148001c40c0584a5100d04c40048801107070303c5503c0d942c42084c070081502c0c01040000001000a020360041140c45c00141c0d104107038202c0081c2e0344103549000d4040c80c2c00c00b406d50200f005032440000e26600e1982d50400c01c41404110744182c1ea603511800401154600503403e0030080a1486c82c0c0140080100c030b1140d90b80c0e40b020000b0764009911995180002081180f02c40d542246610584401161144415070800c241c0e001d210392000d00c030307501864820340003c0740c229a9a2070320f030100c40b0101060701c641c03030204828483d428400c8249400a41400750004403044400060700659042c1c0702d8000c10f80c3c2c00c0100448403115007050641e41d51060410020204202000400c0500800d199003050000040c02c8115980c021008040303059108800b00101048400f860703402040d000c80755124403060384c0c0011506038070010b2a015a8900560038095060340550200d80715410208038900c1e0310716803912000d1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 831251357 1250 831250107 831250129
    0x2040509060601051803070509010305010c1e05031b0c07300c0b1309020309060115021c030e032a01060f060c0605100803130501111f020906070b070201060e06 70
    0xf01241c0e0511410944441c40da41136050b42d400601110700850b0307104d002070131b4080300707074802d642c0c0ea5522500702c444140e210b200f035480313490b2000c85d0031031500300c02800600600c801458044107007410310081c0d8030030300801d04440003602a94221502c00d0348038080d100000344290424960f14501c0c3d103100c000b00400c08070800b04260000d0300c00150743c0c54141040c01d40d501040c194050b8500c00c01e00031800304160301c003550184440ca030041c00796606064440310810300c2c508000c0f0a650100c00050940c01c0c004120949410603841e010840740004048145103008014940e908680c03505400700f5100088191140d100c4140802484129915804440808010b01585001881e1020481c001c55040d4001039000703100165203a17079060b0364441d46400c580144019414030380c24007000b040340f9a48440b420311100401707400b07401c0f20380103500d06040100c41c03d10051040390300400c01070305a9490009032a0907a4122106081525048500900034002d90060740001807000000c84c03002c0c20501d01c0c0e44 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 831252607 1250 831251357 831251359
    0x905010903150209180403020c01020705120618010b03010c0c060b0a120b070c0f1505070e01051b0f0d170703020403030e0f0a0305030d090b0906061008090304030204110403020405090606 82
    0x8221001244840c0081c0d40143c01302078025111030000701103012000242481140285d000c0c0165100c891300080c1880b0840d071140380f04554090702a82d5409001c52050303000801544030522082c1d1441c01359024124101905516502e81035402d2021070700000f0700030400c3c0c0300f00b10070401d80d040001000f09240e1700c3d003d800802450106040c000440301000290000f026007401c02d070741c0d55030fa940c008000c00302e40011102e11115051420920800d03002e669040646403e1000c1d0010307440000800c50700801c521841041c0c00f40c86154440d070024052240c518040d83d082e106080c1c800d0700c01038080e1114142c0c82c44e51170360ba10000f8107400d1080c42a07400b506d6255440390016407025042240c0368000c081010780c0031060020000002c0c50400080030003004503103002c1952044c4c0c0c00c100048c103400900080003030b003100080140030703510402902030b66155810706000b16160b01f04c480340b5600076034200a40103844c200c45092840a4140036208403407013110180010358419004030b45894050b2019 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 831253857 1250 831252607 831252623
    0x6040806161e03060303020d0306030210050d0609060608160c02010f05030619080619141b040806190606031a060a1b0c0603180b010311040603050a0302010c0905010903 74
    0x400e41c45520410754036040c00191905030070310001410410000398001510001180e5940c004008064051000c040128285d0802b00600d03071a40e00400c1c3c90084c082d0401007006400103144030680155800700001c0e14041c1001c0002e01d80b208406404840181c070028514401107200c400054860040d01c041140d0680d0b406032a542c80034800d4844c0e40010707140c280d000c1e02d080d0129006800c01e003104030080800340003c12113401c1200365000e084081003800c085080c2400024000c03154803000e070390307006445000404000c4c2140d0b4417120490046800c0300e00580a000c09000300800c082a00c1e60403020260b030204010f41c1e0301c1909034121342c4100e104481c80c0c0394500b5002c07103914102000d082142d0950403c4400c8000821211881e00e00c50301c01141ea03048200710500c2440e0749441f4a840c04090145441c1c68002c294981c401c2042051200904c0342d0090782da0a859a280c50f048603006550180444424001a2601031301801038000c02d600001c02c00c18000513158480c2c030707d03641103075040445 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 831255107 1250 831253857 831253861
    0x61207060509011e02070905011a03040f0602072001021b090703090c090f020d0b010302090d0f02040b060406200303190b0612040c06030609020f040e19020f1806040806 74
    0x81a01c00303402c51140c40b07062008480e1121181511207841101040d12a4054000d49003040d500388111201030300b05801400042c08034815a1013902c01700c03500141c06c0100003801e0803051800348007034800c0d044000c1c116250700a041040d51004020740a0038407098090381c3c50f04048c60000300001c207900d10700710ba000b0700041c0482e4842c0d010390301c201c030058025a684490303140c40b100080d0581e0742d040381d50000e56500041e040c0248002e440b510307000c0402460258682803c000001d00b44003103103039014000d900c001303003002c08550300c591081040500c054402c40d21181d9550015100340e0405501c0b86d0342a00e00600c03080100c40c048102e0b0b01c0340d149040f0280c00080c100e0815802081c04100b0243c00520802080000c92240c0d910380e84954411900c112030a4203003c0d008083d01c506500081c00c09005119001594455801703603002c0c2c800192500010340d641214001c0800c117814510380c0840e01c0066103000c1d0844920060156228043d55a400030400805002c1140303d184a41c002681003800 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 831256357 1250 831255107 831255119
    0x7080403120e01020a02030717040302181008070e160906082703070c0513050f2202150315010507080a03021b030f040918020a05040b1201050a050906061207 69
    0x180d0480301c221254400902010300800c4182268441015000941d001003070f46000c2100c0403269044080301000c00509180c03465010500c00d20041070030000d640300340b400081d40342d040f0f56a541d004240940c00c45545039543c03030240c00e040c001550141d00c006100b005003098035000701d02031400ca07002542c4880c0d0559030740c4800101c1d61708541002503100300c40307038a0700c08400040000d885464000e1f807555403003d1400080040011500b9220460a401d0604109010310003c1d443c03a88040001c9081c4005004840c0b10b0344551002d44000794000e031400e182031a40d90100028611402030000d00340300c0c01c0008001590310707001c0c0762001884080200304842605203e0340142c040300c0c003400104500000401700e06800d41d000890842801c203400b06041015030b680c0d0085078a14451852094074500650300403428200e2180039160041e900d41c0700c161165100c2200c91082546c41c10000c01c08c90410300300c0c6e10090f040640705024584940800b144040c0340000c030903550b22900800038014140b0b000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 831257607 1250 831256357 831256367
    0x17010303083408101e050108071b030507020105090907030b030c03010204031e060b1c0c09020a02030a230c01090b090f060403080c0d060605130f082e06082407080403 73
    0x148038841c0284048000076010700c10403d44919001d030803101905c21030400c0700040c41c00382c4c0105080c040043e0b0810030a84d102c3d0b10710320b01c0c000c207400d0307c1c180b42d4416543c00142c0b40d521900f81d520383c1290b0304d40b041191055141d4081c020b0404101c00340d4580041c10401c01d400e0740118040901001c0b1803403000f102c3c1c441461240409a40300d00d401050901d110400207411402d1044000c15540140451108212407408030302e018140e444021401d01c80b0200000759240a410505030600c0348c20043d6128140c024228030849000d029601e80d901d0300c101c20094040d000d2200211962400040400d0788040c010034500d00e4103110344000c08680d0307503503102180c0b4410080c00020410204008590321142c00d801070b04050519919080c0d5100c1c1d94641400008115511004500c014414140010304000c03e0030281c070240d8040c1d44403140d40300c0c0020704548241e190001030300383c94650000303002e0001182d50f01c0209100b42d1304428040812251140a400c122070140019486400043c0068022 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 831258857 1250 831257607 831257611
    0x2009010e040e0a020301020c030a020607021c0c030207211b1a0304030509131a0f06030a11040b0d0e070605030921190305010519210317010303083408 66
    0x1034000c03101c4841081d0086400c99208c055850361603000014100d81060b010004260050b0842c4003d04001c8408100c40c0280d0340241c60400030010003114840905100b044800301424481425852a150590180b2078400005600300e9484036491003c0714030804a8550604507280140502c0401044500d110100d42c4001d2080b004d00809000d4401d00d07440b0301565036210700020000061001041c0740000c2020310350129070381304030510b01000780706c1c1e2a80c509a0703030850803412010808060400d2008118012034100d45448034020640444001403900450a00c11000341555000c80c5c58030021a000e10049038101c01c03980c4180c001c0e144000d0b90844560741040e0070203c00c1e0401d504240504048103404003487c00298445005100c5890181e0905090800e80904441c0040c54042610043c0b0061500d81900c802c584c1d4001003070500132030100c00139206d11040d034034096840385000340c032019064580c5a0240c1000340032010b442030307050307614400c000348641041e110354041c3c8044980e0000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 831260107 1250 831258857 831258881
    0x2090f0402130909150f0b0d0b09070b0705030d052419050904061d011e0c1701081f06051c14010f020d0506030c0109060c030c1202012009010e04 64
    0x7205000410fa41a44507100c00d00303200314404100c0f10b080c580082e0a844c0040c1d02d001c0f015180a50315007141ea1280045900c49a000b403040c030341545c0d9081c603981002c03015802581a028005241001c0120100c000c20310446070050401c80d5840c1c94500d001a0740e0350b20848d023252001109483c1803480c0004a014519a181850100142d00c90700843c50025081d02d08596140e21070410540380a0700c0c503010f20207001c180000f04160b5003020340340065040441e0090031080d60b5140314280c0603108120b50040c0c1340401503204101d5035107100383da6030354162030b21224024001d2003040c46c01c250b00b0301602080741c0005103014440da031b0504580141307114514045900000840100d22801d20a0151f40c901e004181c00045c3c0321b10700c20003400d0a85d400101940d1298014072001042d40c0e0700800000283c900324a006150650b15103401c0c0c90840800c1001383c1104001d900d9100803a47c15042408c1c5540b0000c50701b908210b03200d0210b030580c0100c0a400303006c00d042944440340c0b07060a9001840c0892 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 831261357 1250 831260107 831260137
    0x206040b150a080c0f060a320f07051501030c170a1506050103110702090403050c031630090b0d09080c0610080d0824041505040f02090f0402 62
    0x7485a0000364926203540c01010203801810035081a8540ba5086218103042560640d107865100c0500074100d01ea04801c0142c41d10480c072900208010303180c25000e8103200e01403400e695002c681030b20000390300540c01c11503042c800c803000359002c4030400c1c604a040b00d50200d00c000150741003294540e040c00001d40d0003501c0f0f101c0c41550301d0200b41540444c0324202102d8000182c41402d00c0001070a82d0303410300f40c1d03050121042010f0401078842c0c00401d6403007905498059220303402e26603451b040d0f00c01d03010b03004403039448026031105212210a802203992680321500b031182c0d003ca8100101d00481050090115006072020400544904000c1480f504200700c00102000581d403038035125000021250301e03940c400c00401268814034140702001d032202c1e50003400040b03101c100041400c4001068584d070700134408081490a20302034004035000400820600840000e118091b40b1303480e4074071030380340b260341003180205801d03000d4401c9890110f8080d14400c83d60038003c06103c0690309c18210004052 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 831262607 1250 831261357 831261391
    0x3060f0103150b03090d0306030f0639080604050610110304030506090304050103060f0b040311060909070e0906100c350c0723090a0609180c0608070206040b 69
    0xc42c40c1410031000e00740030400961070303050910b825442d10046d4120f0708181460408140701141000744420006d5501003070100e0f2401e118840300300743d8440403948031038100080d0964032950003607000c1050070000c2555421020ba03180780401c01641c08c00e413201a00301c20b03032030b0119540c3d0b44200002d54040b000711086030700e01aa2569943d1070170340101c3c0c940c20141c00c007140a2040c0e69140c0101d8000340840502c0000150410489149500c2a0310009000102146e024200c64a8240980c0c0700700c08001c0103c1000c0c030b0b01800181c0784070345207024944141100304c0042d41c0751a0401986042180700c2d69144980f010aa8419010040e00c140c0800c0340c0c203140958070f42d12a064281d41c4030412324004c02545030141554801d14010864100c02001d41902c040404500c01140303044543c06412180340d0025120240d585008242035040196894101601d864070016038426a4002074400d000e1078880517642c03042100e500c1402d0703428000513041170020502007a0700500e696001748002800c42426 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 831263857 1250 831262607 831262631
    0x20303040803072006070b070807031104140109173c150a050c090d060b04020c07051e010906080414010c111605010503160302041d100801020403050303060f0103 71
    0x50b0071500c0f0440300024040484142000c1d40f24002030854010360740c407030030120180c2c0c400c0005c10005110300c0421036440c0009925522940118803104e1001501540d01c645031071000e04941e05982416010a0440340d002031001000403907022581c05e60401703080011410344c0650200b01020885074041b00d20078500420510840c5050808884000010a511110600315a45d04d901c000c044c140d0041c64101000540c105d4003049826183c01250090f001002c907250050051100c4901c0d1030300b0610220320314280000001d009010354004031655601c11042e00c2d802d45110414124041c005980b107003080000c0ea0048545d01d0b0418407503001c000c464032410f1091401c50f0205150680050900d41c8107203c903880501802082c00011380301104094101000030b0000e01c40030703001c2880180c050f02c088015074402d905443c00b034620040d242c048128102168103004401307641d0b401c12040a540001207911051007101c085a511901a60031030383c61404100c0c04006e5420094103168403003d0362206 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 831265107 1250 831263857 831263863
    0x408030a3c060f0f05120606132c010c03110403020f010e2b03030518060103020f010203040306060e0106030c111203060d0b09060405010c09120602030925030b07090b070b040203030408 81
    0x1030140c1e030b080300105a04d03100c200410b81046d000310860760b402502c284032190f00c840c2400b61000d084640081820b82c1c5c040d0100b06450001c0f00c00009848408401c0c0d2190b00701900868603810043e58107000d0003483c0c45860415102d5484000d40c400f842c01c01d5036540d9400f5a02c1d26592040083c603001c3c2d03141a072510b6a0b01d40915011007250640e140d1000000c240c0c052203140d804c180b040f1000c644140342d07110b03210b81c0d4038010300010f0310a01c1840039103101d9030720800885010b158442000c1c40060344c0c0e8034000800c01800c0c0200c0c40400d04100c0c2641c1400c0c42141041c141024400040038152055203860a1503803010f010300d03030000c15249211022640b50310040d409900c0b40c0c0b004180506c0d2a0a0050843d071b0284204010017450b18401c2042598440c00040e100307030011f60060380c2e510760420061900100440d00244444144003100c004641500d5147c01c0301d0044001000c1c5541d07010044032240c0c1385002c0c42c00788031000d00c00d4170f0200d1032003c80780345e01c0740c030290840e444c0546401507145 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 831266357 1250 831265107 831265109
    0x50d2a0b1207030e102c0a0b010b0c190f0206071101030509030c0d08090c09010f030b01080c0a2105030d0902040617030307110a0b0408030a3c060f 65
    0x4824200144100c08000481d040c10780c812082d150401c1075161102c500b98803507100855180600c0c0e16000b5403903540340140d10742c1814110307080700c1100c14040c1c06180d45d00d9081001081c6d4a1741d0100307000080e6410b00c807040b5401440c080c00a810f410740010310341c034801ca030101000c2ea1800883d80d200310044c0c903070390700418400c2d0040c40c80c60b840e8140b02d00010255940100550354a820074408485852030010b013240140240e800c0c590a10f0780e5241ca200d2070480b02c00901e5601c5502d00000040d0403400d0701102c2c09490240400c2c4000d0307a21012281c0da11000d0180c020780000d9822010000390205420361000020391a100c074a400409845203461508a501c8040b6072580ea0581182189024402c0000901c00d19048091580e490b580140d124080105910306000c8401c0100303000901c14041240455030190850220b8201400c041d07a0f5034004841c44240702c0d140c2000d0401002c0c07140510728000b02e101840d0601001680b111100903200800c400d043d10743c860740041f07101c07110310b00c4c200 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 831267607 1250 831266357 831266369
    0x1020703031b051002091906121a0301320103020f010e01120e0715030b0d0209100b030f0a1a0a0506130b030a0c02010b0105072a03050d02061807050d2a 67
    0x96102c541b01010000400324003072508440162001c0c0402034140c00483d81c042a18440c50009080c000850000d0f03401c4a09c0704003240e065280c60190035118440d69140102c3e17607007501810388030000f8401c51700500602808043e500c031400a020201c158030a400341c0d81411418076080c490200e85c2a5118140c541c3c02c0d081c05003a420404060041d00a01d06030020544d40514062016251140c042409500c042d440039014440050001d140c105803502410b004102545a655032890607052112015009a030046500c5052100310080c0c0d25003001c0140501c01c00502c1403022500e0030042020b690b00401c0c0e1540081c03014100010482c400002552103060410000b081140d221700009007142d11412001d410f2003804c0c07200c000480c908400320f490a104254900641c84010381c00000400741650000f00b5611a1450402c0324550210340c3c1c5000341c903080f2400852007844281350380c0741c0902c1d011703040d04100002c1c042c4000c41d420481c014105103c0e19500c40005104800008040200d50020 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 831268857 1250 831267607 831267611
    0x6070614010e07230c03040503030c03030f010b07110f012a02040608010212040602160f0609060b04051905040f1209080c03012d0f0e0c010801050301020901020703031b0510 76
    0x100003000c690910341d0360040407450604107203c07040700d8000010340907034020700c1c113114003050b90300005000704215405460b0040481c0d407508207038040340d0b42d2607104030307603241c81c0e0307480c04000081440740308080c0d40305658085c60007151121001c007403201010b0341880d61410400d042d030000024601030f214104290485061414803000280140300503552a83d000024507881008410180100c1c0c922098015901140269980900190026490700030050240c500c0d4401c04400c1d042000d40c0c0c0c0460003003441420140600703502d2600b0403007100e2040b6000804001006059850409560b100c00c0d07100c0e100e00307100c0b401c402c4a520783c054190130081d100c00c08204401000d102c0b884040145101821088000340010703032500849070305290300d080342d050511030202c601c100000b069070040c034000c020183c010000b401031206403d5440c044c40c1d914501046941c40003082c5820180202da5041e10180c0051800034910b80d001c44540e018401c007400a00242c5c2c0e4410b0004409100707040c03902c1d28a00c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 831270107 1250 831268857 831268859
    0x702030c01051e0f04080d021204020f15041721131a0901121e0209010f020106050609100507060207050706030b0105030906040b06042d050601050705100b0607061401 73
    0x88500311540582428450040d08050407804108008056404214002d203511302e6201c9140242c82d5000da0154001101e001040b01d66462058000552265000311042e0041940d40c3c0103028840315100440c00e0041000c010034000240c00905d14458005642d0448010541e05041c01541c0c420414210444160024224800f903500a1084000e02440300500d8040405540000c13080d1003114000d41c14480d124101c8103601186030301c03840301012060030381c040001020710414000d41c030202c0b40c0c1d07002c540610004010148144213880903504085c0c081e40c0f5009001c2c0c1088061034020820b0f8003003100811074040003550074005080f01d540300354020324040741003a402a09803686200e00314100601841002010740c2c1c001812600650400d031750600c50b480c3e210200d0041e00d00300700308a6845003080c04004d0310852445846000140c450303010070440c3c840a0044a81e03201d20700b409400f40d44100035902d080ea04544c00071550a1005007020f18ac2140d542e5420180c4d080503025595810711100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 831271357 1250 831270107 831270127
    0x6011e1107090e07050a1a0a030b0a08150402030d030b010806040f06050616170306010804030c020f060c060a06060903020a1401090e040609060501152a06110301080d05040302010f08130605070203 86
    0x1d00000501440f00e08510070100c0111114588c6c02180c03c440c7c200354803018504c44036143c0c10303400e10180c0308000c2664001290070341d15610325036054808078000d01c83c1c4665a4503a500c20310403400b0b000c5050707442c8056600ca003000c0001810800b12907007490f0b641d8110000e803a5840ca4000c01c29080380c80040b103032600d86401c05540d8250206501114171004008100d1660303400b440d00c5030b22503494280340c00d4108490020a88881030004a26041000061800014200061101c1c4129140301003480410f481d24021038000302c003848000d400c904240c40510020803183c07403a11080006240c8102040d0ba01c0b410b80c4841002564242d9030316550300540024014640119809041800340b0041100807100b4010003842e80709607000841104113040d80c000600c1c4d00c201c610055005103090281c4440b45445458540c0300780304110b5103104909004542da03004078181e4046a4058558105854450006480c40c16004015a8a0548480c4a00001022407241c54080d01040d401541c544134000c1d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 831272607 1250 831271357 831271369
    0x602070315060e0115230a05070f0209072106051503090f06070306090b01170612210306030f0d1d040f0f061d090a08280e010806011e1107090e0705 65
    0x1484440816580c900641b02c0003042c84102d6030040458a4040e41e105402c1c2802004a207540000a5101c6003110138092580d50004903405c0351405940400303001b00ca040310071412a07103070344203190300f11804c1a030b4101003040a001944d03015544d03405485800c0101441c1301e043c07000c1101c5900c00320360f40e82401c1c8132001252107170340c19000702070031f0034042c0521102c450748109100400003440380146480c440311848060280e101040784045038045035501030169866144c0085416a00030f1103400101c14a4248c0043c540c009010581c1701c80c134640c04010052650420001c8005402a44030101640200b081b0b106080100b02e039410b0026210341011044149502d404061210004200c01440401100403821038005940066030b5951081d60840510044201d69417000d010019500440c130f100c0e80010103681c003003030240d039400c01e40c1d900c080040d600d030951030240c0080304404070010992756005100b0b072583e03284013108940f1a01e698496440036507040015400c05038120140400150800e0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 831273857 1250 831272607 831272627
    0x311120406030e03031017120708040504111e0921010504060c0207050105090607050a080c010c030506010c05030307080414030a0915030605240d0504030f0f0302040602070315060e0115 81
    0x15102440c6141040306c80d80010303000c24003174461400c07041e540380c00e0501000c000b0740400d82041d102068841119042c03044850708a40318241c000c0381070180c502408540d402c02c80d010031100d008489000701c0c02d10810038113030f0002c03488541c21408090415044003403500302c0304a604000340c000305803445c040c40c040b01924007880281043d540011030502c0140c3c1c008003550380140d0140c82242e114111410070601d0182d0062001e4801c0e0400200642c0580064010640c3c034946900c1c18411a00d42c0303001110034800c0b14401500c103800500c00300300d04500c01c90046401c2130046e02019840d0f803960716200d003142d1101d0105400f04c0c0200108018004403504400200c44080c202040384920348000b14644000020907440609000c01a010100709007805440c5840307001503081007246880d203030141c5141c031080080c10115180c02c60758400c40b0b10900880c1e050300d0840d400f609819141d40d9402918026865102c000c26441d03a8010070f03840c514008050013440e030003813108400c03201103c0240c004564 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 831275107 1250 831273857 831273881
    0x2030c0102060c07020607060609020403080d06060203130e0928020a0807151b050a14060a050103020f04020708070203012d0e1f09171c150909031112040603 69
    0x10035000c2250585403c0b0a03100420780503198a85e0703640d403500c0d04000a1440f5003091003a94404900801885200780c00303880b0507003280b80304101c2b20741c940c0c80581c1e41e4060105054803800d22000103125450200240d260020200d4048800c042141807041004042c0d0340c0480340d441d49502c2c2c0d1070f029441d014402d00000c1c0721840141004030b0400801051509455803440d050204024503001c0400c22060010061908601511040001450401c0c0740c4802d003040c410700c1c0d20441c80420400c038554811141220780c02001c0f540c0c142c00d2401480041d4101d540162483d444c140a2840961800e01a030210000350280e503c0c500d41c620040c80d008910004408400d0925016802201c4880061508100400d040040c407524603120306103805800c1c03001c0d00a0400c1c52490340c00805d55042000b0340364840045921032018000c3c04900c1046604100405040b405151400c0000d42c40c19404145214002d21b444161070480590141c50100858140d00203664001000c00c009903043c81a030f076513440 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 831276357 1250 831275107 831275113
    0x42c1209030318150309060412030b0112050901060e01300c14060417010c02060c09090604020336010f0603030c140f0f01020304060b0616142802030c0102 68
    0x110000440c0c0d481c0540d188101d0050301001c0c01001075599814045981803583c00c07025139034030306240300c11f89411080e501140d01b1140382d4941c4004602900070003054020680d039040e0911048072032039004c0c04020f001c0030310ba95030350b01c0d022540c5d8074428042c501800b045465807030010140f5207034070712111072640062010007014021000060242600c5421a001c2c2071110031a941020002440b42c416a40540e01d0700740d0b080f0035442c2e41d40c0c3c10f4003c2c850017086a000d942030303a510700d0306c480880d11556042540c020700c4030b8009425468603902446d00410460500f64600101c4080c003441c2d4580021a01a9090300c181039059840e400d000d1a00000418a818031026107143e80c080c0c110912240300401e4942142c1c051013000c0c85c00c0201091402c4240c0c11940b0f01d491175040365000b5401982d00340c4c1c00038104a242c003090f081403401c41c0c0c0c42441c140107520440c1c8007601c2303110340e16404000116490007607180651000910301445c00480d0500d2014030341c00d480510406141246c05002075044d50 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 831277607 1250 831276357 831276367
    0x1005120702031e0906041d040201030e0f1005100f230d0b180f0303011221091a0706050f150a0311011b050105070504060807110a11042c12 61
    0x251070083d1900569075056051311a4000800909035020f03c1c0c21803040d44581d0a80900e114001d50b03ca00d004034001e8908200e03503800c0303a101c9030301d0380002d43e12490f040e0312100140b401c020081d40516800542c3c9001501341640b80c0c00b240c0c04036141a84001d25809405400211233a160302d01e0404107102122180501e12242d03031892005240206690142c80b50030101c4c0c11005e90600c151b100c2d030749516040c0c1359250384444284911507400c500c1a5910b0001000b800c40143c03220502c10403840464940c84032141c0b0380020a0348000184207203002c0303c01c0034410040010304500820303002d200c205940c020707289040740c0484001901e20740807500c5801c0c01d58041020952140041c103016000f0320304240c40c1c1c0302800c89a69043c3e4070b01d8004103151f01c1c003020040001d40c018007420940d8200d0b5182d00310fa495010b02102c40f07003c500d01c00101d58024144803400178140004102449c01c01600101c1d001c1e900801c00d0a07959411030026018151034400615003807400d0183c4000341d0031108109041c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 831278857 1250 831277607 831277627
    0xa29210604050f012a021009050d020d0302070c120f060501140108060103090c090209150705060114010801140607150513170f0405150702090103030302190c020f01080a0605100512070203 82
    0x1216100c0e40044a40070600200300c240c407d108100103640c03145800d00071812546080c4d07a44d941c085000e040103009000441c0300d0345129008540d02203400001200c18181440804032983c3e0340e1a0044918145504181d000208503020301402001c0042c01e050320345031600005806d1400042c60281014600400200099440012075017660b03940b6000580716050080422403288410342e003840171041c04500310040100025419060311440980002c2c034064010054a05500c20300a07445e05c0e0104030760075803036420004050306606d070145440302e01c00c8043c0104a4122441912200f841e003401d41c4c80712040c0020f04a0038801d80c4241008249042a00c1002100381d00560062500c02c0b13103801c0e10b14114a44190550344026001403185025594901e0007900943c000004000b802c81c8810000f000c0d40c4c0910132446100e500a00242c64138a1140c0c0110341448004010342c0e13003030303540340c20100f00e0ba00c8400078100c0304001900d501d65103482c407814034100b001b00100b0710001c540c000c10a007201 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 831280107 1250 831278857 831278891
    0x501060f030f060b0307080307080d2301090513021e0a05010503151e10080f100317030601021c0210060b1603050f0904090605010e0a29210604050f01 66
    0xb041d00410002458141c040c0043d007011100c4d440940c1600c0042074010511480c04010315100102d5030041151072210702c41045c402038205c8404258090540040013008001c0e00721a9010b07245d100204c24804d119030020700b107001c03000c034505544685c80b00044103906010300e1000c040c280c00d081060851a040102d0241c0301840e0a000340911020110b0b0007034941c03210004212100300520603642160394050003889030310b04455615821007004040f50790300c119044003e09403600031407408200f0080602d044402c1d031014244c1d504500c980c00f0782c84c08550030050078820100c03056003e000003072404144e400c2038540903040351000400c10040074820f08440256050820383c1801c10603201c2a542e409641035000301c440c0550030508040e909030410085900c40c1d17050311000c0304103804645032101080100d03007100808950704580c0c11621045907041d8913a4408c0080014550703125603031852071640c8221010003641003039034880028801080400c2c000107a01d80c00000007003003a00000d07400421 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 831281357 1250 831280107 831280133
    0x6040809010f1808060702071509032a030b1b03100620030316030e0d08060121060b071e030507080f091c0c0b09010503040b130b04050a0501060f03 65
    0x414045041001036480f070248003c1c040e000124560740c84081e50361119103840303403030445664005008801d80450300620401c1c007a210203410760340d00c80359107003181e40b1585a103607202e003864804000c0c0300700f60540403600e540c07a50185120301f40544d00da04141001080490401d096064501d07400d001700038003042881c08003402c4030800d01d40311400003821f00b04100503c0c4031355084066804008100007585002c42008260020559010040d080c4006065a142c101580c000c1b000142f500c00840c03525846a41030f940d2100d0740710600b00322a01d841407010201d82d06c540c09074001c481c0200d1004c050240f02c608400c0d280c003100407060004030f002c0d900100248101d120040c110300e800700d5020703090304002040d9140400081c0044040d030b44840c5101c43c0f02c240910341110000412040030501d1090b40741542c841080684699045460b19601d480105e003009001c6a0050031049a42d0007195000c00680d0040b40a600500005421070420900350b56090b0000040681c400340d041000881d0461b80c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 831282607 1250 831281357 831281359
    0x60904021b0703050105060f06071509020f0301090b1509100e1e0112120318060b040207060501241d0d0303060f0b12150d02011101090606150206070206040809 70
    0x10394503080007850750540e0408401016039441610070220400605505c0f203030103070000b00c40006820401b041001500c0c400e0040041594511a00c108602031080e00001c11a9200909000504c80350070f0120b802c4034008103042c3c03212542e23035081c080030008403414902c99280c291042d1603549424196400c1c3e80515200c0c03041d4240c80303200010070302c0f00f5075131b102d0700f001d410b01000704080d59445260340100082504150b40c88080700b2404000507000388500c81007100907903403074016803406403074940040c541312442c1504103408122034400a034542c450315020b0510100d0341c0c0c4104d45030440c2c1148076054000403400380260011036008001802e942020303502c00483e040c1043c00111300d030480141200e80e01030110b002c284040171800d0208a00904014101c030120f50300942c1c1c0c0c9100c480111126801c106400c594551042e80265200d0f0001c91440c0c00b0f032100101b070000196952004892207035004031000217800c410b036160300b075050010940080c0c6a00c004c20f10750410791100003851041c03424907 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 831283857 1250 831282607 831282611
    0x307050a0e03010c17131a06040b01020105100501050702030f0303010906030309060228140a05011a030c090402010c080c0607050403031202130510030b030105090d0314280b1906120605060904 84
    0x41c0c1c6107050400003c46c0c2540c04440c01c070804902c0030405c22480e10954805100340c0c100f10303c150440d4030511940f8880c2d5805164031407a03601d00401034a4540c03007580241e8241c010344112501e2a070042004500820388010700003403c0d0703d94180100440502c0d080034045422040414840840d02c0d15070034072003121540d00c0c200c2c0320200e2071312003501200107034000003074000c05407060144101980301c0c10060010404002521210b5406c06440d41c140850390b5911032a00030104002d54410001d6400f4030303100d07521261804103600704482c40e00d0341c11581c035000208000307814001c0660080d054400c2e40342d10982581844010141e00d100b00d00710740115409020454120429548640c1148880000c054020092350034080c140503120000384002101180c20b000c52180c1184600721a135106044590f00340302181c44104100c0c0300712400250801915888807444200d90f134883d80341d42d030051404012010b03640d14151010f420020312000b191082032400f10100900e850300c004484a22904680c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 831285107 1250 831283857 831283861
    0x819080414060d0c030f06080111040b0903010905060906090d0e090a11091504170d050d230c0d0b090105011b020d0602030f04170711010c021201020307050a0e03010c17 74
    0x700d01d075801400c3c0d025020070b04240d801c5a106406038419070900f204040c061005d81e86444850303080e03a486412204070108104004c01540d0004400303007a210038000c0000c0345654040d11454034101c400d803500203080c1c2200c020b2000300001001403124001c0f003414290602c00201c3e0000e06c600034000d08080416880d90480360045584104450034006c0040403036454201d04c08030710b9502d030410700461910141e84110f10150080c000340904070108540e03180c43c541004c000c1000098480130842c54500d92000981408640c0041d10981c0720764401403030f03c2d480c1c1c0b0721102a001926040841d5034042e60a6400505c8640da000f00c03450088008110180d001c014944089540044524005040b052001c02440f60800040200c94000c41c01982c040707058415102e6a05128403c540780140b10201c07001200c5d816501480c182041103000520681c4548401c001d0542664411540711f0001000082c002074900d800c10306000c102e02d0b043e0000c00030384070f107110007820003682c03202461004040800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 831286357 1250 831285107 831285109
    0x1c0810030b06010c05010f090515010e070c140714100c0c171c02010b180105060301170109020915030d05041d1015020303060f010e10030c020312100819080414 70
    0x11083d059617521600820a0399440c4070030740001c0103402400c407454054508000600042588114162142034680101d1a106c14a0a54081340910021030b0940b81000e150310304039509004410003082483c0100003040103401c10486031480c04c8218009000d03043d0310b20740100d407941d89450306480140075410300e81c0401802680c82d040168400c130820b07409520621040e254103421084034580c0a0310b0030000a4081d0341e1424600030240513480d000a018001003001c0128083c0034008460038500000c1c5010144d00411980502212070b820326041840c104e030341508040041d4070600303c1519140f4145418500e0003d6003a009044c00c0789042c500d040440e0b402d2000880780d03001015050014103801605100280d201d42003151140c1c46025848803c41180d4010f04030012a0440100781c2c0906840116040e0b00600c8140c1c40c480452005120ba40700242102081d2800780e6020f070f5451404900d0a50241d2426040c07603442d217150340f50850f60100180104080d40c050318408440f002c00040504 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 831287607 1250 831286357 831286367
    0xb0c0c010e0112110d110412030f0e1017060d02130b0a050904050709050f090d030504230a0203060c0703051209100614040606050903030d0506060903010e1c0810030b0601 75
    0x83c030320711003145081d140c0a00c2080301c0006040d01c1c004070005100602c606420403c1c2d50056100d403003007104400c003440700000d00c40d400309000050503041509a024420010803281c42c040d01d01c000219a41003000307200514920380c0d030f5500900031150029200e00907800306e032203070705484501080c0c1070302c2c1c02007008a41d41d48074100f4094a00036201c0c20340c924041c14090f07600c85d028469100c0740d6140101052040d030905909510485001008000c1d1442d861812401460010415903d49130404000464058420016a000c0c02444018420030419004050038850301a00504103900c0802c060400a604002030780d10404040314443c0413a40c4450b07106040040144100c403004d0703e085800b03c0d07441a070380c400c0c040101007650200240740e00e42e02c09603001d100f0341c0d11940c2d1503401480f0071022006150069a400f0310064040b0381010400c1010a00b503071918203100b81d50340c001616002000c400300d904842003003107a10700481c180c180b04200c0d421101c140d000181014021400140782d0b03034090 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 831288857 1250 831287607 831287627
    0x60f03030e15030405060a0b04060f030803070e030106060201020a03150e04021e041d1606050414040608010903030507020d0903080d0203070513080705030d02010908121b0403050c0a0b0c0c010e01 86
    0x10400403030f82c03840d052502c0342d202c070012590314958500d85050764207203092a210302c0c0256907442c400494850300b1a00c812038540c000070b01d05410010411100e550640f028003d039401840c007a0005601ca251024001e401d48005a07160b08100100100401c503a21841029a40181c1c0507100d0300c4103500782d00090248140410039160300a4240307203886840d0a800c40c01c40360b0304140401135607101404801c50b03214807580740c400c680003c0c0080c04107001c12041d41440958508005100050380303583e0b00700e6a0f084d15520481580429540c0040200f01901030141ea24682040d282c100a1b2504540d40c0440502420f480510040c1d800300000794407501503000c5914180c1c4c4048000c643c01d6440480c1e6565a929005440c061f000c2c11140c605580c0c014043e0002c400d90201c000740c10404100100084080007c00c09203078422007003a80031115003400014000f56008001030a16198250144070000c442c82d44502240a400c2003000c2d078001c4049030000c0b120800340380201c034890400004950003800 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 831290107 1250 831288857 831288889
    0x212010603080d050708040b06091e0a060303090510050f250f050c0301020c03121f06090e060f0105031b041503020910030903090b030a14070c02030c04060f03030e 72
    0x1038240c001c020320403035070041c0400f01240c079402d011644d503c10084441e840242ca004007107440800101d03040b0b2501401440e07001c0e4500c00003e0700100035030b44003400600155148000c6030356500303061060650103803540c800340c0b40c00e541d00c0301d03e80640c0c44c005081d0b110305003504080e801301040d0720040d0040d0014060580d04003004850044109040211405101100844103886084040d208508041c029100001d44c0840a541070081141e90780008010043c03d200c03030b00101813180049040d207804640d01510070340d07440e10640c0f0b00b00407402020400107040c103403099072030100c500600e030307071140441e98003100e1120050007103010204170410900454100030070b25815911800762095041d8082d00100f00112010205085444016401c13500c41a00240025008000c24482d0310b14440003981c000c10311600000da0600e42d8100b003040300c2d07030940b400f00000311890651403d6250401400f52156000c460070407959191408800711000103100007014406c214803181300c695242c000e003c1e40404 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 831291357 1250 831290107 831290111
    0x609093007050d080a05011202040e03090301140708062d0d050f030c01180b060105070503121501020606010f0203030a0b06070506090109031202090a23031c1202090a12021201 77
    0x751a140403a1070301d1002d0101c500080001000944140701800303454102e230925075a41c0181c4881d5001d20001d02400c0c0c08000f4584810030542034240c509100e044028248217860b40715038142654010021a8007405c1d0a2050507841a0060300c0b4403000303989920044030b40c2c0049800041c076004283c4070550110050018080c240c54030004031004801040d60764291802040040c00e006050020080c10000240400c0040c100191955020b5001000c50718021000c990411030079003010040f001e800c840c5d2008044003044521280d58040082641001d024200701608100e9800e0080d43c0b400b00a04410025442c3ca82c83c0360075860b000101c520050b0041e06881c00e515281d0b4000d8007900b45080200c000420038080d0054605140c420343d010002c00a000305134403860322480d185450284484403641c1081c80750140c0283c2d074200f0162009041140388081c0c0c1c2c42000e1000740110550b4410040000d00402449482d40d54815036802541c0d548040b030080c684103400854540130601d0b80300c0c041d543c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 831292607 1250 831291357 831291367
    0x60409050a03022401080c04110f031009060902120a0c1b060b03070b0c0303040803041703240402090f101103130801060501030c0f08040501110a08060906090930 71
    0x140d02013884034440d40945200b440b5195030070841c1c1c06508003449010385540142c1c0c100c81c100d00c4d058200f0350002e4146644070741400c110101c125000e0f401035855020b6161400e07420004030790240503210041c644488110b0030a8014413038044a410b000301001c40c016034810030707000258010007112048040035516403016020f24500f01004005c5040380c58820f103e1081d00140111301001101d103443c44071400745040d5200c582d140815900094011035107240d0b120504015142560043c506c2122030681e80c4182e1a10200361101000c20f801c01039004c0c0d03004009041c20307512041c02040c0500300030307100030104600c1d15000f1203040c02c000e05065803d0100050034400480700c2410740050350300c403d008002c4140e41c4d10056048603c2e41c181d030800b01d045084d09072a01800b136112240d10030b014200100703050840c20302903401c4c0d5100001d0000400d008006000b05400c080c011654012401c2c0c0301c9444070308002004666400c80035010040c2890a00c48002040400700c1070000f442c04420003050b207070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 831293857 1250 831292607 831292613
    0x132903070c020906010516111207060507060e0316060507030c111203090c040509060f090d08190b040c020114010b0c060412050904050c03011502010c05180301020f07141603020303030f060409050a 86
    0x209048c0d801e05449804440400c43c41650701084e174408803400b0743ca0340c0345000e4895482c03030301600c914111388203036000a000c800b20342c014400301c20100c140b03ea00c002a2501c0c24400240444440481d6841000340c0861742070403c100006880c102c146c1700d41d1803191a9600d1f165a14a42000d02c241c05030003074140414081c04020005103d03000d0085019070001c26582c8403200b0f5502e0281d540e441c000906582c0100c0d000309411034103000150424180814a80242008201a94550f0740106d0040c1e650310403612540d0340714031280b4054402101e1040c0b8140c2030000841d42c448000d40098140c1349080d200341c004c2401081252001d00c005807041c00640b0300401c0403c5540c02c00d104212902c003c2c102540d60b054030612446003884034640b02c0a007402c904050704e11150359400c04080d00b540d070800c00215030051000103406024461244a41d0b448907905500c3c2c10004447e6904000000d06c0d142840141c4e404020389900000d485004100350b600c0308001800740443d1100508a8004c0d10316400138 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 831294964 1107 831293857 831293873
    0x50a060519090506101202030d1808010e0304031707050d110f060c07050c0613060e0a030209070c1b1a0f132903070c020906010516 58
    0x4012425500750300407a00c0600c425034881e4490410040360640c607542030b10142140d00c40c5e5a035218140e60200381d460101003001c6007032000000b19980c03c40902d0400e0300c0140300000080c003005003100240c03a00c9600500050b00c84011031030307076041711107909012100e115601c403000f402c2503a040c081c1140c110803070480c408200c2c00340640c03c0320441e0301046140d0054107e90740041e0364211710711f001c41c03514483d040c2c114014403051100807d40700d0716400540c100d4419040ca48030382c0b010400051036100c0da035000254000e400f0400d10041c160310007a0044100c0c440c0c440d00d060072480000504140590744500c800040811040c10348414605006d0801d101c0c81060441c1010b00c200e112403040566600514aa40900c541c1e403111015000500030440c034504070703490b00e54240040003c0c125445800f01a0152592a0114010f1303440f400071070350040c6107400c0c41d41034000245010b001d = true := by decide +kernel

theorem cover : BRFrame.Cov 831115107 831294964 := by
  have h0 := BRFrame.cov_init 831115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 831115107 ≤ n) (h2 : n < 831294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
