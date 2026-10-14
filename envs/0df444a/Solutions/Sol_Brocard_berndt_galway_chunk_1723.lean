-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1723
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:26:16.710986+00:00
-- url     : https://prove2.me/submissions/c8b42aa4-8995-49d4-8a05-cc24d2345a29

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 309712230 ≤ n < 309892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 309713480 1250 309712230 309712241
    0x20d030c050606040e0c01030f0e0303100509090d0f030f0b101d0d050d050a0c0f15050916050630040606080703050a0f02180f1f0819020402070206030a 67
    0x4490070700c96640811010700d0300d4051741c5041c0c02040014901010158011006004116010400c9994a082409100307200b40000c621030340b002d88034041d4030307071810090200c4400300402c035100d140c20880c0182000d40c2e10590000c5007915524001c10a0896200e80c040146100303051282d028400682460386250410b64407041d40b0410510982c4059115050000201c000031008140340c0101060410041c0030310050041c65403640351240040885503904c0c001c4000400702500c9001a0318050300301d00c01d1600526510000301d0010f41001e8020b034800c00041207160191910a0320007085c0b0860145010001d65105032100d002c0302c0c200d100c050094032581c01c050703e0581e429401c0c10340201d001200020302c00100ca42c800d0003000a000191140d03910b8654541040780c2c410a20444600405082d0f010180540c4002c0c2040c4818144a26403580c04c034103c1c00021810342050700200101e90020410349500500c0c0c10000c4640002440003400a102d0950025441840801031002e41504e56011 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 309714730 1250 309713480 309713483
    0x1e130b01020f0a1e0f141f0b0319031103130504060509060d060b04060308031f08010606170907080f030415030908160204060504180506060f010503041e020d030c 71
    0x7034501c00ca0703071181000e460301481d40002e13010469208400c0c0f46195101c0340301c04050b009002160600529507100d004440310700900d9046540140102d500c00c1d001d9948a0b08840701404080007907521681c04640c99288003c1201c0c1d0423808692140141406110040aa0001501503c0c5e99120100c00d4140b41d03c4c0c180100c078001c52070858042001d0900e80c54942c081c0310001c0c10f03a0b000209541d50403010306400b6450f5600310f5110000040000e800002035802a601c440c0302e144007100350809030858500f2075110124580c10100d0800c980ca400503040e5541024490038030206555408202e480c0030a680e20060b81032003142140c030140348010000d401503c100d50307102c80d4000e154810403000d0321200d20313000d40079030000c1000e07008002e03000d01d404100034030241c00851025501c0001504a651030422074600c24003800c605130400c001405042d038045400c07950560f6076030421000070b00e0742c0402400141401d012034a0301d40300c2105102c05941c200c1d4024a40c1c3c8110426103001801803803076660 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 309715980 1250 309714730 309714733
    0x40e010c11010e06060607080d0203011805090a12050901020a0c03080c160b0a0c050a150203010815010e06061e030c0409060603200a0905040f022a0604021e130b0102 73
    0x21070880040060290f0000510654020701c0b5945510040101380e52101804688256080104200c1049980045c5000f89080d1040750704241030441707084191361000305003c41c00d4001c0c0140c040021505092051300c240146401515003444c000147d281400d400340c0502a960b60440c00001c12041c000180700c107105900c150303481c3e4aa01141c840c040c4107507006900c0c99100030f02403142500d00c111190002e05010b50104c540240180d01c0d020000040341c1c10484480c1d070000018004604204510816001a400e440c0c10b15850030440511441c00074080900c20000015640070b05030040c400a01e502d588554011364900300305414000e00d900600c642103404e0704103000000c000d40039100349007003e000e60054400c074040d00e2015180310b1744400d2a50302409104007021403191510301c261200000034540040e0380740580e54000105648461404601050307412000d5200d03000460a103402580c15103032010513200e400b4280c4829406440c2c103e41040500d8440140441d90f03401011080c8001c1c4c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 309717230 1250 309715980 309715997
    0x4062408010209040e16061b080319060605090105030a050a15090903090e06031e011d01060906050319060207020105070f081b03030c0703110a0203070b03040512160201110a02040e010c 81
    0x5c5c81e540d180c45400540030140380c2c170311a04010b803030302400218000807168a1030b159003009a0b51050302da03400c241c881136611040f1031940080c400300c0c0e10468000c0c00203410081d041c81c0c01d01c00001c1c00f500c4003c202c4201a07450340049095004190499688100c41600110b05652601d005500809980c030050340028200140001e98080d0000300d00d0080e50080c002e0088110101100c0480140c1204001c20b559607444001170011600d41303008a00c0c611503000820910300d07084141c0c0a03920700340c109a1113500b01140d40e610348400120350f5122075500c1000541c40e1020340c00140c50b0741c0640703200034041481003120f0f40304004400c0c0c0241214140f410822452400186581359a80800c031050414000d0800199021030b000b450304160000c01c80003241c0e40300b40294040303410466258000e00001c0d002105100c1081018412000e805c3c4918913080d0030800075134603800b40f840d10200302034107104260303071206042e02c0180301c0295510340142043c0301000020100351300a007400d010b0b000004d412203 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 309718480 1250 309717230 309717251
    0x703080c03060603010302060901110105070504061e02031e16150c08070f0302130810020a0f020115090e1501080f010c020109020f01030e0a050a080306010e0d0b0406240801020904 79
    0x41056902800d0040c041c5404c6a003180e0900115038402d000d56414406412500c020446c800d00810b40f0455a80d0768090f200c42c6001c030050540b500451340c00d04500d1020805611781c80c0d00009560030070a2500fa001508699030708114002d00c03421003d000142c280121400610000d14000c19001c803202c2000c101c00100688100c0c0c0c500c1c01543d440c400610036102c000b0700c1c03910030380252203918490940d07125405d50320b403040c9180c1030701d1440401715950045a031036040c070b8214040e055104440d0000b84103e011b00040302c00d42250303a004d903a103000c0c0c2c0c3c1c00c00c241446508102c210441180441010b5107035031101801030307071000050502c80c10340d03080591140d1a68818043e5056042d406400e507690100e08100550280c2017484d0f5058180c0321b21001d942c0814401c10007038000500490701c07203a490410b200010122890604001d00920200c800c07540050911280190300603080100040d11022103000c0091842400d5079417001101040e901041162041d8000c0410b04401c8604102c0003030031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 309719730 1250 309718480 309718501
    0x303090806070f080606090a03060b040e06090a020112180615090204030803010506031305030a0806090114010215060a0b0a08010503070905010f0603050601170a0c0801090509031818010605070308 86
    0xc880d80400180f041d038081e9519401400d88a4104400814403400d00e05060b000c24803510b0164400e80300c4640b654003040c001d0900b4482d1000001540000d00864034080300015a51080031000a04202001407040e0303504915500c808503219102d00103d03411221402c0c00070140c1030b00d0310003110580e0203850003c0e5064841c803c49040325406500c00b030231271f8644030800c078964100070328082d11485c0d020450800a40180010000e0006603200c0c0c07801c608001d13080c000c6c0114140c02601224155071010520740c3e800113942c06a0304172401030200c5036540c820114180710f195a2184600e44400b03d4045480c1e500300007024140c90f0142d003101c040740c1d40e45550100352482841008142c100340001884211b1180c0c04c120390108040c14410305491540c28030022010080b240061800c0d540e4011406031644508030074014240c540092040381030400a40d5200e205100800c0466584640181c80c96240c500742042074043c6030400e074100c0e40e52070760050203592141e074007100007608010000305401c00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 309720980 1250 309719730 309719743
    0x801060503011203050d0b090421030612060903020c190602010f110f0307181403010b0d030f1d041a0a2108030c0c011d0c041a060306060403081303030908 68
    0x684812488000d9504c1c1c40c19207440d4000150390a080d61900300c03080d06c42d00d80c19102c0d8025031007842c4200d1a1130060901c1c541c62600c0e4108107042504004040180d004402c59002c0d006810240c00140e840c80d51406a1a0030340080c2d80c2074104103042c003200005500c48000008880700d507002400340e0f110401c001d400b20f0750003106040c0ca2200a06c07900719542000006158824001e00742a8583d40440b155004485540c2d8004417580b013080d2040a0f450500303000c1d038008424241e9070303151080c240380e078081c0c070b01030000300e201e42080091910304a820020040340d038150300d40a08100401c54100115940b00c003005000345002c3c0c0c01e00800010b442190b01c558070f104000042c415062140140d4411000da40007400c00070101000303203c4080351440030700c0f403120820554001400352101c011981803c0140d81c14a0b1031003180fa200808400c0c8088942c010010380f002c4540682c0c0b55951070000b1030750700480d0005090a500801c000c40e00402c4900c800041c0da000b51200b14180b03a444054655480 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 309722230 1250 309720980 309720989
    0xa0507020d020a1a04031704050d0909090b010b03060f0909010203040615030305040b0a0e030f0f0106050d020f04020c0a08040909020108180d18090c02011505030d020601120201030f0c020d080106050301 89
    0x40d184c00203150902d044050f43d42e0400d2081c54a444042485c503650012103606076020b035000c0c1c00a0a00b07600040c0c000c150707000140300252013800307443e02980b218581d03440d0500c00c251031040d0001c00101e0a1756501d0304180c04e008003c0c0030030b801e41450003855000307402c100c60845605180c988007940c2810043e144108483e407682d0f0b00fa10b4141003030303107901050300725806001c00d112510100c4c80243c0e83c10f201d001c0d0a210f0b41e600034030300246101c40840c00d48a056003c0d60044000c1000c82c00942c0f01e084005004000035a00540d45420711420f10740fa0041c0b8080c041e14040c4081404181480160855140079000341c2e644045a12000c0c0e440c40070003090800907000f47c0c400d030740b141b00710390103100e0891001003040c040110603907440032128183e1302c911078080011b0359280455602a2860480c0e40060401a001801007581003540a95141018040c40e82c103040580c01d40811603229801c44850161600420300ca013150810029540c4c0e8040700c0303604041513180d400450070034460002d0328100c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 309723480 1250 309722230 309722243
    0x3022d03152e030c09060f050304081201180c0302130e060a03170c01060f050f061308010f050f0601170c09060c010c020f120c0d030f0b04050a0507020d020a 69
    0x1600c4440c12401094408240d407504007803449484030180a401403100054142c6002c1645a035001281c010221040000d000742070000218040c0b202650001c402d070504101070506941e6502c50741841002405410b14680008441030000f1480c0d20705107150120703d540005051202003940c120990071b074014403040303602d01c05031b049080115502d01c000c00c54010101400000009850f9159a0030100d9111181c8440b8003002514101c40c4509210306002044582041e060540c10300700001d074076410590744580715503004100303a002001b40c0c0c0201c4c0b000300692402081043d105a502c140075050465959031084410702c00203840794000c40c4034075494460242c881010b42d480c90141441504030950b406c1d04100c090000c0050460244100c10007d50650000d20900c0da0007086036141c201600c032203020310b280070f0002c94504400004c00e8240300c00c030b504000c07501c0d0143e000381ca401410754201b1251b00038240011301c0600c940944c0901c0c041d0602d41d080c0c0d2880081e000c41a0b9407441c4071803004101 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 309724730 1250 309723480 309723487
    0x23130e010513090602120a050601020f0705100e0102160807060f0503090d051605160512120a030f0b03030d0617010905120903011d030c1e06070c05030c0102070303022d 74
    0xc2e480d61103110042d00c5440c0040c2030103031545400a41d04401c8598051040c0d5440078041d06680400014440344e240c20b00411103c0e04100100e091841031100801c18000151918111a030080c06200d00c44090751410240e86a1b850303040c207694141c54403428010412000002050500c52800c0320310606401000b4a140a0307020800c46083e88030342c442c3d01c2c0826100c600d041c0091800d01c440554500380900d0b4480c018148010003420110b203081c942103681c070a16100b0344151142c4282e403c1c44490b0305000514480c0c0322172000c0074000d03198001c0e516000020340c1161a5006a0000060710100d411850f00d400003404510308a035600300b000707440c84d4081c1c01240444180e0800034205000f0150021445129003000145015119402c0c9a80d44c0c001080c4d100c0300090400903010380b1010000d0040e00700402144258031000c01800000802c500c2e0b480d89000c0c03280c10800c440708140e184000315942c00603418001c0c001d4001400c08452031000c23085c210b03020030458448600d00020307410814039 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 309725980 1250 309724730 309724759
    0x5071d010302180613060306140a0227180718090216020409060905030309060403020c030102071a090f06090d02010f06050f0108130b040f060c030c02030d0c23130e0105 74
    0xf901100500d910742c80200c544000070048400d008820056124034000704036400554111540090002c204104207031040c40b02c86c140f600c10000c4807401c51a15180d441500201c40c02241d07045c2c00401003003412541c600c09202c4400d9000d91104803520000c2240300342151581c130014164400d8045a804000da004c03040809840d259000580c06031050f900040c100b070091b079070142550800c9a500c002d94020314100410715405124061504900b20001c515101640c1c0d2083d00080c10740c8150201e8071115070001d13580c0101000901c10040f0110201c0301641340070703c1026941c244040e0404015403c1000d0002e007000c1c6d500901d0b0035554010074400c9243c19400044030080c200402c4a10801400c52030b04010400020310035000f94000d0030303e04120485030501d081542e1208042408041c80c00c803d0030180c0d503010041d544850010300d40803418443c2c50408070740040349400407000c2d06124142404281072400000c0010a0b07030402c50540895480203140101c0b502449425040352203002d06a0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 309727230 1250 309725980 309726019
    0x306041401061e05070501152907080703030e0a06060f0801021201060e030307060c031a1801030b130c0f08061b0409111603030b0a090b180703090503030405071d010302 74
    0x14903011860b0150030021562540350035681c3c012150300b0482e002c00000d0007007125620801000c00c02410b00d0b104227030b00703081c412036003803207058409005c005000ca0200c04044c4650001040b12450340101d0354048090f04000700207242d03078801c180700c141a4540001d01d030720041c000c1d500e44a420302d0b01507c03581c0c47c028040c1e034080700038801560705010412040001414600c1a021350780c0c515940021900d600c04c085584c0184000d81051144030890200300c80d81500c002c1d0941500d07440b100107510341d22080700004c2c1718122800300801071001c19801151509050480b08100d0301070340c003150410744a090040c2401c0281c0d130344130812008204010300c140e02242d0010701e0b1a043c01c0a4549c68052046400700004034240d001301c0029455003054509440c01d00e00820280c9100003040000740420000200c1c54001000180046d59044000401480c0240e100e00726803500a4282c0c0d40d02c5ca801c2c50207544408075409664190700015040703400d4444d0307450b8824144d07a4090122102400d00d0118003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 309728480 1250 309727230 309727277
    0x106021516090e010e010e130b13140a0b062e08060604090612061a06070b09030f040608101a040504091b06050915030c040b030702100c05030604140106 67
    0x40091145088000403900c90520f40c00c1d00801801ea81070503103504040f00304040c140b018100b101e10f61020705044001c240c800d11a550055241429500d141c0020300d41462900f0a1941c5080e80b401480801014070059480140c8a078000300e480d01d18103441c08143c007040000200600a0a090104202da80c49008403242900300c8402400d013401d1940d178158000644070380e0341000d81500c1071a1880f0003000701d103005400745038546441064116030b0807000b04846006412014081000d40c201048111106204941405010150007545c880c0c6405000c1d01d40781301902c50307450b0203080450006101d4500c0b80040300765043e10090924192030001044080c00400000b13946084180d89440708030b680c020303441401401c0d0740d1074540d01c481c06d4600b003008212412076441444074040040085214190303003220142e5004104150716900e40c1101240380003603101103e100c231f91412031520725160300500550302c10102181c0900c40c24055040020342c41e5400e210340300104244400b0608506081240e4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 309729730 1250 309728480 309728521
    0x1110705160308030f150d1a0f0f0a0f110310240c02130f09140d090506031b0706050406020304060e01020702030c01050a111e1603080d0b01091d0f01060215 69
    0x400702900364440000741d110304000c50840701c060540e03812208020149104a44c08072003034032000749c58501445240141500200b030701f010035079142440000f0505c10790204120031044030146071030349024a050a0744484500913003000e410f0a40d40349290070308480c807481040301c903662754190140302030b0709100407503c103042800081ea4840e406044800803d100d42e803040e5019010782442410316810460078014100e07103000401c091103006100755180c100890360000c601100910710446002828546c500801c04d000340064141418001401110b402850286000d01c104018070240a40418200d03c5110002034040e000414400015030042020380703018030f018204000c004090310b0034281400099203042e401055103030742448110100308088070202c2c042454136902c00e403c584803041640110f5480e040c80503203c1000c003026901c6004010f0042c10009041c8020204800e1650b903186e10442d140e403031410304000000b07505440000d001a18050f0070311240c0054035000c0c0c10721a6450110711 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 309730980 1250 309729730 309729751
    0xc0c1c090513050a0b0a0f051002030c070b0301080c060301061b05030c1009051011071b05210c1c0206090a030b090303040605070203040e0a020d0e01110705160308030f 74
    0x54151500741c194909040301c0b0000007164500420000100c0d14501c02190082c510301c2d5007402034205011704003013030f5a4100d54000c08a032090004a24602c14100d07020b80c68010282c1c0094181710b0380020354140c42c1c282007a00c4251410b0414090345020921400001490003507900c44103a0a0750304008466002d281624034109810412030300d0200702d0105804403035075a298042c1400f1062180880742c195404050001e0712032202040b841d4050104041c1c00781000c41c40d0107181c2c24075810000018000070740f0b21000700c9402d025070000c150002d0f40700c407110302651034811074030301c0c2c200c644400405500c0000f01e40300d4295000d0003140c4d0421140580c010088900201c081005900064411602c2000942e81c030324040c41d100054039806450701e42507500500017030000b18060820180c0c00000358000603190401c00841c034000c0c20410340d0070042c41d441c089294410b00b02800007811658081c000b190b4025540b031522810000f040d101c05004044280302050b030f044d241c1c0141075048488400b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 309732230 1250 309730980 309730997
    0x307080a0b1507060f020405030a14030d050f07081f12320708030306060708180a0b1e0306060d02070c0b1c060b070b0106030b03240601080c0c1c 64
    0x20602804405a040071002c5001c5456000c002c0c0a000c0d80c1e441e031455003010b506141c5000c010079610b00c1080c000403d02940d400005032115000c1040c0c40c4c815000d45000e0046003054125080768031000e40381c24000803d00b40004000000003c3c2c44031946171881e4640d000b00c0c5c540102c0d8a0a0706125904454191070f809803104044c0c2c51502e402d0003118920302000c040224401d502d440c00e40c3d940e0060035242c00a01c104203a80d65180306070364480d900b100c81286d94210400890128000c2101c001c1c0d8020300b562000b090303042d40300c405003140c101c00d03c040342c003030650741d981026071303408101e406c0c541c802001c0000d103100002580241a41a20401d040b8121589881c903000d52604990401054501c002c2c001c41e00b5000301d405048024581080104c1c80c02c0c0301521520702c0c04005008020501d03440340400b00c050b4604001001d040c03107660340000a4406a21145000765000352047c5001134200320118207500d003c14101c8480c13198036001800b400d00c0b4086100300390602c44000b03800340800710307 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 309733480 1250 309732230 309732251
    0x30b07090906090e0c0d080d1a0301180c050f0307030f03030b0d0321020a271206090b0c09220f020a031e0506060a0c06110408070e0901110307080a 65
    0xb8041c2c50040c202051000c5106022103104a1800b8a0300341042e100301c0d00ca000c0800031510a4086580546490340f0208166038904c1010340000d10880740b0b030350150b10708048030310f814405802c1c0c3d084181c800e0240b03026a03030f030312420080604501c100459041c0c1050004000050400c810220400c0c0b11f800c0106d40720000600080c2c1c0c0f550b0700e07101a00410070424070055a40100c0f1440b101300c1144900441c100000c5078401055000c2c41e54121032588188108500a00c440d0a8410010072000e49281c1e500c40d26440c0c654060140c4920031105241c6a9020401c58103042c13042e02c40a400241081d200100d5404403420003018005240c0c160942e10026211403403041d00080007401703100e4602141c03400c1d04c240c2e60328402c1100322449020078604418030406070703240012116046d100380303802501140f05050082c0103007102e4a104115007400540052505004550082100c0402c02400d249550390100e490907a6404c0342d800c04032101c1040000e4005000c3c10740f40340c016080d41d000140c4020b44 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 309734730 1250 309733480 309733499
    0x7060b040606110d0302030112060902010212031023011e110715120b01091a25020a1208120405160927020a0b090d06050f0a0c0c020a030b0709 63
    0xa0b800001c0014018680d080b05050700300a48001d44542c0e1408526642c908410b22442c0003003104001c1259880c2d410880c190fa108105030081c035150840c00303690341d0800c03000c80382003042c8505c514280014010941e85a6041140b200c024221040e100c40108900c071021410b41c81d40d0200c5150b040c804500284403032480c00300704080282c05003134980d01010030034030405084000d83e050700035030322420041d0101060741d0119080d01110950044c41079070b11207070036244200340200900040444005642d041e12000d40e5030098141900075280030500c5a110159204c070400c44180280003e1010058501d00f018442486030b48280118144c0e00c3d00c8000a807200d001001540c0001c94041d01c070025800800c40e03035190440003400745900f5501e4140980e000c613244508510401c200c020020070181c0036a1200c2b10211545584280104910f1401e2204480c2e6040241e4003101c0642c5840803910b0903a010f060ba6022494006041d0620302d4590b40d1403102c034410081001003000700006000172260381 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 309735980 1250 309734730 309734741
    0x70306060e04030e0907021e010b030a06060e06031203040210030f020a08040309060e01080f1314030414010c05060f0402060d090c1e0608150d1a07090e091207060b04 73
    0x81442080400c0c245403c0041511000d403103114407400b41c2e40c09101c5803a4001a41d08104601d21800400e00000054094010001012034075054007401c90030a0810816602c018240c804080e1591000e403a018181651000c0c400d800c240c1e00181000404c0241c40d29448040f07103034219203404540003400646900a0780c009031026000b146643c01801300700b50b0020101c1c00682039034a0290454a01400000d00802c0c1c041c00c042e82d08a1030f00c0105541d00c1c1d00da25850f400c00d03003100601a201070342c100c0c019540c1d0701070b200e0585000910096010158803c04074019429008002886103864000c90140e015001603c00c9038050000c00000914103102e000e030301403c1e806801c04108240c5468000d100c40e10b940728554450a001110a220442e009901650807415a22070444c01180a50104213040000b031406440b00c00040c1c041d40241e2100e18038036105985964840000540d01d9518050850066403201d803c2e130003296522103540082e07405003410f64010000492400039074000b10301140c8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 309737230 1250 309735980 309735989
    0x11e050409060b031b030a061d12040608090705130c17100e0a020c151801110c0d0306030302030f070201030b04020c030304030f0906020715031424010201020712030e07030606 77
    0x191643c4081e030551605100040742850030300003440800c03504400103034841a084100810540e966124011800b03807450414450750540c4088440200350060b400025811500c6000005450301000a40004d070110701c54007145c001400e404694001461980c001e0004119050300b00502040c1c3c0c07041b07288a00741c029006042d0050000041401c00c0c0e205142910001c1c008601940100301b4240042400624440314a4502010500c40d4484240740100e40480c20300706001c07503080502010044e81d04400400c19407100d981125841c54001c001a01030b06d00301d110107005600b09000e11410403640e00d0080462a20501d0000713141600c00300090100d800c449001d0700291f0001c010081010f0304940c420045e005070341010b400b0f251074500029540c0340640100e0f041d5101250300f102490740250000d0551041e03607880042d09160032241e52010752010094441c6c80114101c5460246d401813003152608c0d03030401c000d01d00130001c0b0001a8054400a09000c50a100788100000410101d219850180 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 309738480 1250 309737230 309737243
    0x2003060106030e07090203060a03060209011b08040f0519091e140603060705160f030e040504050c0112203a050f13030804050304051005030402031b0603011e050409 72
    0x5074480b0a113858a006900171142152040091020716070b20b5003101d1046079032103c00541d88018560048803034101841c1041c03003000c0c070f44400004001c14070000d0f109a5403490384290000b035940040043c000001d1907504c00464a00800b409090059046113822441401030b50444642c18020740c822600c0d0a40707441c2040b0001402c0c0096480d00740107082e000100740c81c00c5030800e491586c0c03108524aa800f001406c03d00202d00c0072040500513404200280700c02481004203292905005d51102c0d190b102c00342c00104010290720401e03241e0310665016140064015054040d46803020803549d110150300f105201000410a000a40b03000000320280d0b510110784040482c40c460034030588401030500c500f048400030400c600785036044c000316155905032618400035100c60401034110310a41e00042e410102402e541420140c1200046d4011403081d001c880c14140415a06900b401000d500c0c2c6074807100402c01000128015142480c10340140f0120070080b565800018044540120048442 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 309739730 1250 309738480 309738491
    0xc110a12050f0c06040312050a0c080f031005040203090a061a0910060305130f060207030c050303070504030b060d0203190501061e090b01030b0306060d080c06130b010f12200306010603 81
    0x800b4041c05181c602050554645040606594906401c503070b04890310000c001e001300300680b05034814820780302c001e90859692070352140707851035012650b403044443e00c0e08102121000621401c1500c03c0706c0c072600250300600885440340c0c0c1d602c00030309030304c45c0050340045408142c080c0c143c0c0d41001090045040303280d070581c564a004d9001d410b4480c010251098105141640c0c40480c00e40c404200140344d0009005a07101814a01628610b0500e14080d29030321000c4200710401c4d0700800148180c074040d1340c0e41002e0747d481c0703800c0041084a481009405070806180c0556090401e031050090601c101d00100740d2a071a1107442151992000b03207032410083c2100b041111000358802d54001c80da00b03107001d0240d9290a404642d0f207810192282c0e004410300c0c0b4442c4148031610b0141c800110110041c3c07407a90411088002c500c0f0745004007503888044031000061551030700fa00da20700311040c0d81a000604440358440301035085038401e0021046501035101d02c007507a01408803c3c068005510300066 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 309740980 1250 309739730 309739753
    0x103020114030105030307060203130f03120f0b060403030e130c0804120c0b070e0a050d1a0c160305090a0e0f18010216120908070611060a0501060c110a1205 69
    0x41c91920341d000580c240c003040140300644012044400c100e4000d20003580e6921250210784010701c2480c8081d10070f010707503442041010740c4540340030100706051105000c20012030200d001101c4c200740106030b00c100204000c00c00240503409511511400a2004446401035101d107810b954000601c9400178000c0000c0000f0000c41004030540b103e0b10b071800c0400c5502507030b030700e507504400504490700b03002d0100d001c04502d5031840958409040080c00d81c40c061822031406010006103235981e0240100040000398150a805041d00c0180380c0c10004011080c01d242c9096480750f00055070a60081c29032000410030036085181c013401401d5035080c41c01e0a1425428070fa60600ca664500307251030740100000c0c2c034158004003034038a00716000703800a8240380c42800c058500380116441010280030700c038800101c0c5030b00a440940b08850700d0382a518560b0340c0c450071100701da000340902804038011103134960205141120706070034540c001d41440c080c207803150044584540c002e003046690fa40011010803 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 309742230 1250 309740980 309740987
    0x3091924031d030304062705100f110301060302030417040e2e2601060b03070f020607120e0a05031b0c09010e010b032503020a231902100e01020301030201 68
    0x49814180c480342c0641080c2d2040003540b41e120140000e03103203940b186c070410300301070903002010311080700e0ba0070119140c0704520301591104403498080340340c640345c80380000031680c5e0750003101d60006007940031a00e903a0808000380c00a40024009441840b0302c1d80a00c854040030b8001400500804074240c481d61916104e5441d2000203861042c0950384040d03429500510442c91100550303030800d0002c08040000c1c198491680d51420840550b5030a102000031440400c000841c0242029510004034019458003a65504c80546940d4009176095040b590070084950206044644940c107039004d9034100e480b03c40c5560402041001c0c1c0f1004e80708074441c0030a00700f01000c500e040035900301c0500d61416075068065001480752003254030000001400d402d907448001d8001c4540a103c01001d8480c0540040094002d0f410540104601503a41842031151400e10640c013400801800d243c415052450000410380e0030880d41548141c1c018100800410302617a003840074a1000140c50f58510300004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 309743480 1250 309742230 309742241
    0x6080a060f240e1320030a1e150b0f0d0c0f0e0d020d1b120809040c1d01030c0203040906090509011d0312040c030203060406060305070f080309192403 66
    0x1405001c240b103104862502d0701400e40e520031013010350000d130f2240c4880c5203003c0054201c115151242c0000104942ca0701d581d40502c512080b00f46440c5540e0440c01e599008850b40c8017800c0c084280b203000e00700b1141159400a01300b01107085403107030600003802154016a58541c05075000f0840869901c82d2041d80516084e00c40d4004071403e030202100f94020906024502002030203502c1d417640e2a11714040c0c01d80320f6100528882c505200e04003d035041c40e805940100c10898400c07810203182d00c00071403090091448a4100c880303a42281046c400040d001401002444c1095020030701000078260785901c5004020611800d02041610b089100642100c000503048120010170300d028503641e00002040d2896100758800d9086281c4070350500c08074141e8184e000960610840c41084100541038002208a9100748100c1c2c800304d03140c448a261120140c010f03a081076100b4800182c6a00c1d007402c00c054101c07a680050070a0729280e003c0c041039101e0f900e048000c1020b6124890b8046985031084 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 309744730 1250 309743480 309743549
    0xc08070c090f151a09030609030405010206160e0d060f0f0f0c021603080d0f0c02010902090f0c0a12110c0a1e080301091d100c08090d020706080a060f 66
    0x1000f1051050680740100c040391301540159941e41c0c40c011842c0c40c400e00449014010040c00c603415468044200b681c7c95002d402040d006000300d40110303589074010180314080c4901511180d0141114506000c83c25015003c156041030315600d64a6030400340b0700c24514260f4a004003c2840089203440c030041e154506404000c541c45141840d0740c080840c0030301e40580c1c1d480118582d0312154568602c02818000d01c42188542c80d02c903040250980540c020702c0b5091080e11841c00964505001181c7c04c002160b845c20010820490790501520407801710520350424080026030000d03840c0c403024103070030401e640c0c4c4403980403031604001d1040765190781c40c01c0b445d80800d0b00c0c0c0d040c1c03540d03482240070701046c071a0168564a5000c0c00c03240022854400c2c42c68241c0300c00f00e91105002e24200c00107041e800ca41480407600110100f4400300d0040382e184580d07002c03030b00104240c52810808851100c0002e01d40030300300fa43c418000ca225044143c14030018900308070300d00e00322001d00008100c0e6100700e80c003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 309745980 1250 309744730 309744761
    0x7030b0903190c060e03040b1b1203130303270203060c03070e01030e2a10020106030f02280803180d2102010207061514100516030c08070c09 62
    0x200b034802d41d0072142d021810354030301e02e050030b104a02440e1031009082203540d0080d15000105000c51201090009011400d6141d000366522080e8121001e41761440b00060030003204c01040060400d0320040d1204002c02d00c03d19000460029a000e051100d008d4216452200c3c803000b5070344800d528003003000390340251051801030f243d800c1c14217014148010850184ac18141c84012550046a003844402820b0b002200034004905000c00003030a2030b465a0309151140d60180040b00e0041d10520410055075400f9502c480800302640802542740c41d400800c01030595650340009603900c01203581002070940030021905c0d940c030809041c21010080200f1170082c1686a17035403020030401002c1480c0701441c01c043d000e000c00205802c81c0684107007407026041d5801e08054900b55012811500100c481c0801d441c581441000c0403c2070941c02c0102100002d5820300020105246602051000314440d017030151980389680e50f6584513070000300041e2180c1000b400c08008541160194aa05902c04c19 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 309747230 1250 309745980 309745987
    0x2060d061a03100510032702031b0d1506030f080307030b0d0201120c03020d1508060c09180c210414030a0906121d160501080402090f0a1b0207030b0903 67
    0x1c3ca6441c074000140300f441c0c0b0845048900b684c450b4007a0b4041c075078214524004105002054054043d051410802240244113003102440346c4000e00501486401d00107010b5440d00095032500c0c904030025801d038031180ca41d5048008001a05401d404403510301c16019241c59150054001d002c88924103a0580606e06400b0300500507039101c00500401c46011900207052640080120000e02034414044c1c5c1003407a080c0b1030a038640b02810914110348021044450f90b43c2d5054481940340501c603c0290400d0100a8815407070940ea4400c981c0700c0c822401003400c04007042280d26005c844400020ba010382203106000c02d100032070000ca89180003a40065151004081d8018003e052030b210702c4082010707050070311504105070b40100640343c03075148000d0640214100d4240d114041c4148070003031002c2184000485501416001d03218a8004101280a555005914403003180c01812200c00d10b980320710041c40180c170075190b08280c5200380d00a01d003140c11494040811070019240124031341c01030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 309748480 1250 309747230 309747241
    0xc030e0a120308040627061b02210d09030305010312030902010f0509190801050115030e0705010e060d0501080610080c0d0609050a05120d0c0512040204020901090302060d061a03 78
    0x316140118550603c0e111440390f88905001e401007042000070840c01c0b00340c045410700c11508050040015006079004c1203032108228141542560703040c8a0000b42c0c05c501c0b40644405d43e014003003405180c0d419815450007040f040082d0450700d07000d20481c0400c1c1d80708018024424410580120420b45080030040d00d5419000600b01c28050340000003080400250041035860b82e4082c0a115000d8580541d01903490b804418007030442401416290300803440c1000c1c100780b0900840702c80000f600301403c0028100700c01120011080c00900e50401d008005028a0701c2941c42120b0080c076080c1c000d440da60500b540040c1d042041503200442c554884640140540e41b030080074076000368000e200146004113842c0407400d1110030b00000d45180240200345425080c12801010843c052030010441494451000e031002d00860b8151043c0800d103074005401414581e004002ca40d4050400e0940035a40b0307130008510758880004107850640311801040250a18600c808105504203170b51350070b51420 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 309749730 1250 309748480 309748499
    0x31a01021b060913020c0d02070f0e0c090904031d2407020d020904060903020114091506060c01090804050405010f0810050411100206070e120c040b04020c0d0c030e0a 73
    0x5207105409082081e80300c8588581d035500c01c842016501420303400030f40c513409034000000e40004051700018051314100d0500c03d0b20210380c2038290b41030f02000e03d041908204402913041001040001c82c00d03000c10000e43d8568034030b94054455071080e40c4200c10082800710b5405241400c8206502400b0380307101b121034950040e20729468050810002c0741d11071016000080d512103050306e010390014140d03002d000500045811402e0f0b980c0c009c0d0000d02c0085881d48200f4405c4404031082240b40d0850f941110300418103003201508003000a100314185485a0313006421910f0501c422a45200d0010f02045141460b0186a00400c8600301c005071203440c0441d0140c5079007010142c5603010356550001410007054480301c80d4006006002c4803499955540080d44d12031090303510101007450904420b00d9494920340d032280d0244000d000d003000c01e609500303000c0a40701200c60300d0707803103a007e0242c00a00c8004010b140c000000507500d00250140074140a0000e9100b001d140e40107250a450074401c1104 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 309750980 1250 309749730 309749743
    0x30421021315140d1703010f080a020918070803030703140f0103050a0f0f061404150b031903050409021801081e041e06090503041701060f061b05070801020406031a0102 74
    0x3528500f6915110842d40001c114261158008254021070345040011012000165060301c04001001d01c030700d82c0b1f030240c0550340c0004082c000d6000014000241c20440c0c0b4907441d407040c2c0d40420440340032580300c0281e1411500110f50103400282d64241e9001c41e44402c40c00c480d04101c0183d201e801c00e50454807440d480d052808005020301551440110800601c00003008115410040820001c0d1400c00301920181e4127681c01d550000c004400d88161512034880c0300d02800c3d00600400300e60761504455488000c80103001c0d070500809200019850180740028510481045159080f200910380050000e41e00504040201007500300c26050ba0090341c030100340c006070006551062401c04040e48207100040401c0104070f181854a40320420100101a0090740c0f20201890000d0f00c0e444d00e018200c62a030b00c5140c01d01141401d00300310441c0564080c0c5000300c980c26682c041400c003902c1c3d00b03103041e5160340400d290340e6000404010030741d454803d041d21000508100714588007030f200001d64404 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 309752230 1250 309750980 309750989
    0x9040c0e2b030f11100b1305130b0a09052b090303050a05030606070204090507030605130803060f060f121b040612050601110d0e1c02030303150102030421021315 71
    0x20143c1c400000b038900500304000820051000c54520a51140c0720b94060140600030038010011a49019038045035401407610440c00204601c2684072580c481c05401e280140c0031b0b10806544207409c202084d0709000c900b082d00c256010492211060100500501c1482900713802000b040103018030000ba0b0100031102d03840d441c2d1074020b03200e480e0f010010f01c07244a9404000d600c145007940004c10080003141c072104480c042c06c010015035a60954040d00d40e081201c008141460810004070207141080144480d928060240d5080070483e04039451113900103000400c0455900341081943d011100d00d64481383c2416030b05e5801c051034042c01400d039402c0b50450714034280e281d80c00201c2c0c031b0744505030752540c0d0070042e8101d845003008660003400c00e00408450501520280461250340da035100d4030544840e0b130280c021440c540d501000030484040212070340c0e04601081000040c2d80b041890214005a40031014118280c4d13188108015040881a401c41c481c2c240f1214000c0144064440f03001c0384c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 309753480 1250 309752230 309752237
    0x30610090e0c0904060e16020f06071220030c04030c05030a0803060d03020f1b120d05031f050306040b0f0a0b09060f1512041b0305030703050c0309040c0e2b03 70
    0x1400940c001401419558000f00c18030841182081002c40f07480c01c90087c481f18540036034a02e009035040301394580d038084946501040d590b401074003000d40154081d4900300e0b10b0011004602d04410008051a402503410310300784500413038180140412010f03880c0050100b10020034000d0595501e04c041804000e0502e80715088824540741498024850001c41c54603003000d035049035070840b000511450170365100c140500d00c03051440c80c1d030034800103201c07a028038a5110f007411603503191000d40c40c072108900b9174050301580c00f01c00512a2010410300e030040b4814440d04c1c0d41403410602c0c601e04440c00515444245041100754501603c6481406d41c0002c029550001c2c1801a50041580c0c03c41d0102d1544030741e100001c49070301034a050880705001d9171044110355401904060040d10b02c1405c0e00010f40540c004001c01c000084c000c03002425015843c1d82542c5c2044403d50000f811180ca0314030f1600825100786c282005450030b442d8800580c000c1c0300000705820400390040c0c0004e0413190004050 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 309754730 1250 309753480 309753487
    0x51306090204090203011d0d080c1902030c03070302030901031406090720030301080a050f03030f0c130e070309170a0203041e0302030a0807050601090b0f13060f0308030610090e0c 79
    0x70754559421280000350050300a01444228442d02c0190041c40720103402940600c5418401091290711658040c9a903021800e041c034811130b50854119100c0120031f419032004003d0456040c0041c00a0f040c01130082c1c002e15100d0304004005000e4030100320312440449103031020052a0340d61542140d4100c8080c1c94000000c42001c6105110305024155812061101000001d007400700090448102442941560140d01c00c001c6890b549010503210300c483c4034900400150b0182c0c150000d004c0d0104201070600029984c1d89503074402c23940503501d4400081c0c44000d0f580500901007050440d50030a0f80c2468a080060500252280900d004a541408803281683e1540107420b950b03001443d001000d48400d5010b51802c07002030b0340074038800c40300341c0907101c0005103940007403140e028440409044024841100c00030030189885174941e515100b580c0361000b01d00e0b007010b019824055880707082d01f03595900f000c1d400c03ca081d0a0941e480020000c04502c2840004002c8200c1c5405c00110301d10f5989 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 309755980 1250 309754730 309754733
    0x4060f0902030a06110f0c101103040203191703182b030b0a0f0b030a14010e01050904030207080d03200c03040b0d2712020c01020c150d1a1305130609 66
    0x71140303e504046d0a810300b01140d01003e000010801001d20b16400f07408005c1a044610128001e000c1100c0280d0b042d00160341d0903d048110041412401d8440c01044920200c41511010140c20a48843c461408515500d20142c00d08002022a030806501d002000a00000d0141c5a080700840d20f10f0406032114002600341c2c44111040b0041e000e07010340305003c0354890882000030703041110003581c51424000c040002c0c00c1c100143c83d0695030742036100c0c0c80681c00c1c4001c2c000b00110180044003144103c0c40d0002e0a560b00f401802c3c0700444641d004161441001d2221400101c003000c50451018200500c04202600000702c604503000f54800c90781303032070302414114020011500c0903840c03402012000c4c0040a0010341076a5441e200308036114000810f04000c84e515080081c080740564030081901c0e21902c1d2242c000c8041035040c9006602e0a10b02074020000d03511601b1808401940e64400828140343c0740809084845800c0c40412091400841c013841d205400b440140c84241d030f805a250 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 309757230 1250 309755980 309756011
    0x209030102090d1a0703020403050d030b190602011e060b1b07030b040309062601030b0c2502040c020f0615060403121e050a02060c0d0b1003020304060f0902030a06 72
    0xd003072242c001c007640d103480369a0410000a100b4a221042c2d1200c0107000520814000d1080d1415039070010001c001d20407450350b050b8010640c02325415480003030030000d03c01c490b00407042c1c240604826400881c00d03402c245010a80b0b40c1300170440d00c40450074440300303014050249003940e0140f21208660468401c41000c95410681150406000f26041804003c18035820803401c0003191420b5580718107102c0b504240c0a0b84100d03608030181074080c5040108041000c1c0203410f81c000c4110240d417450702c4100e0540840e0045c01c20104d5070208004c1c2601419443c0501c200800350312240017a241c43c2d899013011644074400103111050800d040c0c101400e40b0748039401038174003840c1e001d0140e662220483c100a8034000c1b2102111000c4002c090720403030007521403002d0f42e20103100c9400510310f40d2609020030005401034561035202c1592007501c1e156540d18074500c8901e80301c10b514010398904240c20080c0a5800c820252411581829170310030049e01d002030100a51031300043c000640c1701000c00d103103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 309758480 1250 309757230 309757237
    0x31118060f0409061809030e0112020c030403031110020a21140a0b04150f030803090c0d0803090706030c05040b1804060801020912070303050909070c060c09030209060a03080d0209030102 82
    0xc9010400102d80414015660750084d0251555841c1402e5441a40540001911020407000b000030780300c0c4e1091411075000d88104082c00081e040c01505021815804034596041644140c00258140c150b0501550040c450f40800d0003610005529102420310f01078001c0742e10340050440f8020941c10300301c8014080d40019203001140c04114502d040ca0401500608081c10540344100d00c0c4c07268600504c1c2c0000307580c0c0201d50070345601c071105a1440e04c816401b508000c010662500908003495042e503103200c0e00c180101d11981310315403a0305003041c1c480c0c903104583d00400d081c1464078034002c01c0290004140c80c112983d200005075154020014017804844000e803894001e401c000c404101c040301034018100d130450036105540221106100340303644e1100c620007d130100d0400c01c011640b81c20400103484e4050302c2411300c07030300c0e200a03070751403104482d5112040000079424000500461800c0c5204641000045030300d4403000341543c1315a100b43c807401d0100c4a032143e0004000036103440a406a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 309759730 1250 309758480 309758497
    0x3040507051002010905030a0906022a100905040903030504032705040b030109060e10150e04030e0303040308040b030406060509091e0a021f2a150b1e0a0603111806 72
    0x1d81c2d8986481c8c0344040c228101a0042d10050b0050300c008844005c40312800d8005900029040348800c1200028408110369051018040080988001c210f42d15a4011000a5403203a43d00040602e810709000f004080340190084040d1041400032149440c00c490000c1511002c88001503420300f860006801441d4050f4002c02c2c5a04048411501c2d04001ca40035502204040c0c0500141b0052034402820311030602420685000c00404500030038424603413034054080203802c0343c3c82c054a0761107450340354001e5800712105500020420040040c903000c1c1100600085e51102200c0c186842a1500c0e0842290103441501e21054181c0b15640c042000402c803d80290001d03112075100c459443e0410ba207021030701c022070392005802e48600c1801641e6000d07000d0007071002008003840ea0740c50461200c040410000161500090041070b0341c3d01070700482c0325000c91808130290391414140032621545a028a00341031900e2014a06030444c082220a0b0f41c40c0400000803043d5540d00252150107080310 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 309760980 1250 309759730 309759733
    0xb0a0f032a020a0201110d020a0b0406020c0601090b040606111b04061a1b06010b16050111030903090f27040501090b18120913020a0e1905090c03040507051002010905 73
    0x1e1192882d8021502941c401e000381d0b034440f50610b0010742c59550301800c0c22160016840004c811020039000d1108a402c0361041e140545000201c402151034490282c024625240da1032903a0310092405203e8000100b103541420f4401880020485441d5030399401c00d454442000200790341c00350354a512410140c50b800c510580c8550180d91417242603040804130382090045000305820740c0301c000030118101c40194410711f191001e0140b81b03040c3c105047d0000c42d110340d00e07141405d00e0040914051482208284000d54694805074100300c601d00440042074041c00d0754000102c4e0b1b18845111400d445420140c504800ea03c07980f410500401c820320026009100003010b101107035000364030081001e00f0710402c6911043c00d80500c46002c0c40f806594039840504551842844c0301d494015140b114070908012040111070350204006049049060a03840f800081c1440030345071046290303400c0100108000c2c1146419034520386d6a404034014179200e095070ac070f164003039140b00b50410f00350241d2120 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 309762230 1250 309760980 309761051
    0xc05040507020d0809010b0f011209050a0b061f230c0a0605060907090e060418021002031308031321080415120507080a110f0403050d03060b0a0f03 65
    0x7800291521110b41181c0c0001e03c020300407030140321050040c40000b100c018001403807032407000019138100580382401158a03440300c40d0480841c0e41030001810050058150719a01d01d040e000708802070180090100f03108034095252101258014110348151482d488114a82c41501080c0b80c0240282d000612540c0300f00b01c0001c0400c20250450748c01a08142c56501c41519614801e81d004c8003680201340c05d20200000003069132400741c000500c4058095440384201d00c044d0042400d0003031505041d400742e84002040a0200d5108000c8002411400051410050250340d50030380102107101301403030a04001d02c80c02010b15001e403034150007948070b066550381d5130799940301403809904007440350b010401804421125080038002d2034800c0c1e00325903c02038280d40d0b062042d4028250800702601358002407281d8450402c22038002d00245000b0801006d00985160004003901e9460b040031040383d00902019540f0354004d03040300c0b204640c23410080f0350014910040a51590240d09001260b101e00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 309763480 1250 309762230 309762241
    0x10512070e0105071b03062909100801050f060918070e0c041e0e010e040f120302160606090513020d03080703090204180210090b0703030203060612070f0e100e06070c050405 76
    0x30310382030b007140c1c4034503000e210f010480164150b100d64140e0800043c100440250301c2d4901e04240271652114030350f441e0401080e1111106402c503032084805441c044848814081103103850000c030340c1c0c083c0340002e0b010b4100c154107000b640c0752100c900c00c82445820420214250700344160541d40a41130284204c103180398604644805203c0702d20400344005200000880d00707044274070150b031066802003611490b00605540d01403050b07001c0213601040660a10244603007240b0982c01c00b0b0040d0042d000865068140720a600840307501504490072003003200c16000051b05c4a88a501100f601070401402d03d94031044140c0103405452802940300389400364040d03018a0785804c404035540291100042003102c03034800c1d15440b54074050b80c80750181c103100340e01c00a4030940045510900c0517000302e0510f0815002c03d03425280590350f42020a21003442c03028050b500100103c0140e00440704007d44008400001d4540000e240349030380905800283e100920000510860007003401070410000c3d80380c80c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 309764730 1250 309763480 309763523
    0x203060903070c060314070c140d0c02040513050d080703150902030f13030e1c0813080f030a1d1f120e070807150908030408010614010512070e010507 66
    0x124002c0f140c40c1000071022808a00c80c0c0300700b124001140281c80c90b40c0c1c5035400180d426001413141211000b17620300b0040c07008117050041e0000c641803901c4901039020a0720401051700c8005102e881c01d003050001c94400f141001569a041c58007074103203900251541300084014040f20105130b03141354080000080d00c12203a07401944556000081c40c186a11490b0341800c1c9000d200703201800041b00c250f003203191894031010280110a80006440c11000550384981c441c1c1c002c480d158074003840402c0d0800c14504148800d1088200c00c0f00039524111130101e004c2c002403444258100612000e00040c3ca80d0b45036455040b0398410000b8100d081240a442c00500f40920944010078243c1040c83d10141036600107036032000c0c0c4500c03030064800241040c0030f80c52000103c810034800c20907580f9001a00c00c00500c018005004074800101c2c0d414200070010040c0a604c049450410200704030910300650000402900208545031201e0740c2102c110040b9000d0040180c0507080e84640749002c3c004020 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 309765980 1250 309764730 309764737
    0x30105241807051c05070207090e03040909050a0b1303080c03060604030b090105040c060f0804080901020304030c060509030607140703030902061c0b09090102130e0703090b070e0906060901050702090408070203060903 95
    0x518039062000142c060b11441c1170745c0b425540d200c00759000340018048821030f0b070071680030100d4980440b800c0c036540b0050a030550b0744584080d141c1d900090f66043c05e0180c01900300741e200754138030748000e008610380da0f00030300030030f40241503032714403440070000c101666604002c84008580000740d80c5094104030501034020310050b6003c4a000f50b8143c80050f0050180300031b02c0901c540c80d2581c17051940e5941350030010b603009042c1c00e81140030800020000803c6100c82001400055441d903860300c034000309040c90688007a00100511203050103070300309418417000312484641d140c80d001c6000466440822058001c41440c160b0301000000c1001818200e54480d180e0f04100711101d62103900c03406241c4d401c0788208030016075076084041c8203201090740f00f00a2a0000c64610340090690287d1f03d0364004007500340d8014002039001c038401c2c0080e1070074401040c2c01600441e40309140c0005800080c00c40c5c410140f00034001d130080030000d014000322605a4036200d4002d02921000c0c50300d809141c1c3c5030b50 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 309767230 1250 309765980 309765997
    0x60e010c08090307140115180b090c04030f030905060409021c050402010207032006030a05010e15090a1a040c0504031416050112020d0f060f0503010524180705 70
    0x18a00692a60030034441d0460501468051014516260301c5441e48400c084402c80c02600030b44d01d484045001c0203165000c0c000800c0c44200e031411141c049210802610791180d85603200c0c1c4400001d2018140c84a01201c0c1100c0d0700405a641500091070b00b80c2e441c02640c0d00503940715802060010320113141d50010f000c400d4150303001102508280100b81c0403181d068070041d00690041400b4130010380d1070700e00142811400118420800c10103c0003601a03031080b1045590103444900401c0707140d0003003030940e40003040007403d480782102000100d41c0c1750100800714050303103440d10510108500301d03c0c100c00002102a20500a424810501401c0d0350700030b20044414014869030310309100408550105400e0810b04142d41440c54880115a030040c48440d081c8050303401c1280e514148070600c10054080c030040300100b0540e2401d03154074030b902c0b500c0c0e1100f4000c0e410001003011038211500071154003545002240b00d40784203c40071036001d25480c44916001b41900050055090308000544040c9 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 309768480 1250 309767230 309767233
    0x12011e0f060e0f040803040f0605040f021002033a230601050309030702130e060a1b0302040e0115110d0302030a0615081b0c012a02010b060f0901090909060e 69
    0x115698801000b200314222200b01c0d02c070042c01d0200300090511002190045e015000f01049891152154400c45030255400c032400c103d99401401103040c411100c1c030221285001850034000020440c0410344605507031035896543c40b005040b642c46104e03500b2070748156a40f4007001400c2507200d0110007488401c3d20341c0700341148000011103d41c80f94048078460340d03856020f941401d145900b032007560703016a2080500c40d034a0351071181c08a641088a2403042c52021400b181d82500e42043c424440c4910000c0020180108002d01c0300d40c000c0d010f1241144d40201034080c000102c59000c44244a113440c940b442e84c000c03103203200d10711581900554002d0110702000c02480c0c2e6200c98640d201e102410003d00818401c20000300046641a8040c100484854002d480c010a441c1d00ea404c50b8041c1d6065411083d84000d210101543ca107422210900c450008104038800c510004186020310b0020f4100180b00296442ea0307a4424001d2400070410120705000c507200510303244029000d2035411803002d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 309769730 1250 309768480 309768491
    0x9050f0f0615060a090605070816060f0b040506060a140405090705030702070b0403030e01030506040e01020a090602060603010c08040b0406020706110301090c080f0106120209030a05030a0f09080c12011e0f 90
    0x240c94850704130350f611940368079850f054619003201603170141c10a001c142c55890302884036000d0308640060031108a0301c2400d00140821a9207140022100080d036024000d51502c41000810b0300e0340000c550a510303142c1462103ca900e0240100854030480e00b00d0768000307500409208541d50050060341c044ca00580a80340d2007911040000414021441702800050815232040c1d159406540200d0f0400c2c0064008940b040b0b0000405084e40d002400f076200160b440241080426414488581c1250040703000340300a40100200074925040a00301501091145010600304a072590445004aa20550510500c0410501801d484d0024407410340c0c00d6091054042e0030520030507000d4494400d000742c0286d16407c018040302c01e040c8440c10007000380d80c01c001c4c0c1d070425039042040400d581d114200855843c250050014008201a0888010f2204541c818002000b000c81c07689403412041e184411540640c1a9441c090706180c0343c00c00fa070600c0359013086d01050b0b03d500580e07112104031605005 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 309770980 1250 309769730 309769771
    0x102060705030606070605180f0c0102070f18050c13030f02151216110a0f0c0b1606090309051008040506071107090c0c0c2c0c0d09050f0f06 62
    0xc0302e21080364450b911042c00c004200011320b02e03038089a0014201c2000300030112100b0600c502d400400002407507554000c4046c6001c2c0c0d0b03030401601d405041c3e01025000d82c68940700c0079400c0700c401c80004a08071510307003002490340d85940050329a01c1e020094120215a40c90a05132102d0103c002e00ba4000c4254610500b0365000301070480381c3c407201c880c040510640c2e1b1107610161540054949000300001072002c2c0505000402c115000940560394041e0f00454610304030031200d00345e51001402d8041401400946801c00d0b0b020840386030000d0000c60090320610301228140d00d00d4016561107115140380070400da5100f600f00303120754410405c54070300381c0b91442c00356094140c0041080590b8800e150901001f4041d8200302982900c0e420902c0200c540c9a68031114410309030400740500b9084c40c0703141c502e4005544c3c103844050f1298450521400c16500104482c481c2814015015444500000030400d040001c8001103218600761062995800071941d140c04094481e10880500c0352078511 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 309772230 1250 309770980 309770987
    0x1020d050307082e08030c070501021603080307030b0409110f01050910050708070512030901151208033706090501080c01210c0c030305070e1e03100e070501020607 72
    0x20b00408454030b80e1a01a80c07144440e80412134a01c02d14500200600360450b004403540c2000000380150034051500c418195111030300c0c0c0034495005504546c07040914a2240040b1001c0708242da070441201c0e07075280c2c4c841c0010f5002d01020541e1580107031401518600340081d50189e000204411140d0101d08010800116001d000340c9560750351140c8044014140c00340201c004002c040d208030b0203103080c2507080d20b9180c102110b101550315030180010030440805002e10030540c041c0c009017110308162707081856607121008480c400030000700000001c60350501c181580c22a400000d00d500a10364108492200c201c610034981d10000142869004508510140a0281030b60401e00c010240905141e004503840039000c0744060403440940e183d20030104160060000b40a40c41c0c64280e884409850001c00b181c000511070020042c40c0200140701c0d80c0c968040c1981c3c440720a003060340710f004040003e420071580908004c0103515100c07584810580214016085540980070380344039035120f00056 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 309773480 1250 309772230 309772237
    0x170f090a0e04150b06030a0c1e02070f080106080304170307060903090614091305040f060e030909092e140a0504020906120a02010804060b0303030a060311040c1d0f09010b0901020d05 80
    0xd179882041840021030421a0390700c102d1700c2101600e450b188030084210380c80b44202d0f0f4840a000140c000031014018521507954200003000c201c002005803503d4403121540328012400740500c00d01807201400f00d41841042501c20380c6801500400c88040c1510300035004034018420640440c840950030009920818151400843e0240c00242c04c03d030f0705140480146002041241c03022209184240400e1040c0309450711550171400841c3d035106044100010344034001c0c011505903009001c041d034820740001d401c403001040c031120004424201602c59025010500b60704840c259035600300100c0c03401e0b940026000f64000d49200e081601c4010074407182ca040c000340070f5810740c000400000154801c01c09558418003070035000503500d201c0c81c0042d00355401a124885040d803103100500911010380d5024545090840d8100580800303020054a078220300031070b680100249000242542c0c50b0482640e0030309000501e008482d603140e0700f4880f0640c20480c0c030b25006101d201a410041030155088 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 309774730 1250 309773480 309773501
    0x10204051c0303020f030f091203041a071e030f0f0203010803030c130e040605040302010c1b03050304080f211302060702040e0f190302010b030703170f090a0e0415 72
    0x1860600074040707101d600d003012110201c0c1003580c01c0010300b031880c01e00406503000d1800100ca0082e00d0030135645040c506801c140c1d005010540070030030311000504004012280540348850540316980e8613400f55083c541002c0c07000070081682c000f41c159541e255100e0140e202c03820500f0094071102c0780c80c44080340001d0060303160b00c0e44200042442204000c02400140e100ca03a1040720054842041d038800a000381d50803a501a26003090000f0550203004583c0f1008142c1b4100d91280c2285030181103560750088081c08dc08400408103090010640407914407540403481c1d16502c00301d00610044449031492440c1003140e144000c0f4080a400c5080302580e20b40040c19141440203030f40801005003200c4003030480e144140004503209290a1003000703c0c0c1c520300c0c031603195040b40908000c2c0c00d40d0000e1020a119401601d0144001506044000c1d407022400100c291524071000700321903a4403442c001c25601c600020b0b80003d5100c6221205442070b449403400c10421840001c4d00400c0d5140f00c0306 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 309775980 1250 309774730 309774739
    0x904110301050a060f15020c060c01020f1306030e060f06010f02150108030c060702160308091f110708030913090f05250e0402030a060b060d050f0a050f0f06040b0d05010e070807050301020405 84
    0x44230890340c504280a409020b802c00c000603c1e10b550041e00f41071036030001c00029100702170300104020140e0117114200400c3d4440c00501000e103030004400c07240c52001040720381480030304c904414103076100f041500304442510040c6005035071219106907403078004100303d14551255400007403015202040c5900b050311401c4181d00c2240c1580c2e100350194101c40398172500126103016000e00f607a800718408424841544688ac0400d40080c00103042c000780c0d4004030307000c1d88200f11405003911100520701684522900005444a1a20b0600c4032a00307444800380c083d101d42961a00c00000000c08441d11000401c0010401541c81d9402c180a90045401a50542219180f840425415001640a018000c080c14604800ca039407090440d0400d851004040c20054200400304c6660b100b0503070010144184181685000b41000500c0f01004060500413034032000d07507410540341d0040711000c2c617038054000d103c4403001d541c00d50741d640214850074006101c6c024000800341030601c200c4041e03410240 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 309777230 1250 309775980 309775993
    0x24010509130602191202130306050a0b0a140112110909040c0f08100c05030105151305040c020f010516050d05060321030702070e10050904110301050a060f1502 70
    0x8001280d50300811007141c030324160075881d0016040d840100b54603242003c11a50b03541c400040101480300e00350003140300501c10000a00c000a070f00f0a2030040f00e40c840c0010a0950b11a0700d620054008105a0b41d04005030720b0303003c00d182d60840840a00340c2c00a98a081c1d03102e003a054100146d44060381c0d00b01980004024500340c40c100502d00aa11a01841e04224215a161441c00c0700c02c190b54000c41894022180c8140a404180125103081d2201d04d005070440d410030300007450001c17a4000b154188080024038101c15813200c400c1c1402820001c0041141e041508030103074884100e044032900070b528003000242c005800303c00e080c00e20790310766441c0f5061412a1403441d0081102505056051090010980708204148401411044644081a12401c0072840680f4000041e000308015107071620800c203200448260000455104840364501600c807400c010b545046c0d00c4000b1a015401e00d03040154240740381d004101100c2004002e40449580d84035000034021140000c1070042e04000e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 309778480 1250 309777230 309777239
    0x3030301031709191221050412050c0607030914032e140103080c07090c02030d11070b04210302090604090509070e01030b150303091014090618032401 66
    0x120090004044003404000131441c00d249068a041c941e40d220301c103110601d0741c00c4010030031800c40d0a101c03004041752144007030111000140042c00303203000e0301292900030800750061204c10080c001840c0030140070184c1e81c00319403d00811842c101e00928818844144409925040000f0000030301131b66801c4000400400c0102d080703607075a800c1c8041540d01d49415401c1111418441d9090080d489404da00ea550300e200c03040141004d00d03d0b48007030469483c0c142c024006c0c0b5008011a001807190380400110003001e800c83c04402d024603a0058401c00445c0204810400145110b080c05022681110507114840c0c404030164407501c0c1d54650000c0007803004020106c0140c0100d5048403043c0180c07101c0310340341d08118240700802d0f40f0039510580a00c050046c15141d603c0d00603e2154242d0265140c040d0810202d0700c661080c58509041160000e07105009140000940b4041c0e8002095181d50300c1402c402c07220042c14440307900c0e2203030240046424101840011807944045080e0115031b05a281 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 309779730 1250 309778480 309778523
    0x111160501050336070e04050601050402071718030f030a050403110301060503190b060a08031c060801020406020a0c0608040b0a05091e0d0801300204060b03040b040b060303030103 79
    0x582060340c001004000311191020f5088450003800141810812213015020039030300d0300d80c2a07805640c11204050074400401d4001c05d00c0340c15244140c801603612030711032409160b12540520310712444c020105002004024000380581409001c50480b81440310054a0355207a104064189010070b00c20802040003a10000000c0c2100c076006000090706035982c008203041c501c0c13040603909004a000c1a1000308070700902501e03040202900c0381d01800c0d0410011a81d64810400c1343d01d0020490000d510b03000b440d42e001403024144c0b0800035500d640c3d50f080007960ba400000c1c8101d88070303003050310085090340c42030380c0440c46581c006980318480e0321803a04180c018400601202424050034148400030201003032120080076050b00103084099241000400103c1c068010494892010924a51103c0170302000020f40262000308013046031280700040040209a00c0000b402e1004000c002c24005001c554902c180c0c0a440000e840c0c1d43c4030000c05403288004d00006217000086031054036000780 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 309780980 1250 309779730 309779737
    0x10e0d030b030c041517060103030804060905160815130812090a061103060f0904081b0a0f0b0117010e03030708060d020904080c0d02010605030c12240105011116050105 74
    0x4042c00b0780e90303039010200114094907203a8411550201000c8810000007001c1681c812441c41100301401d45c0d941940e40c02050700d0000707032019240548034204071051050504c01d80ca07a00c0c15a10000c0780700c0e561901e4194850300a40000380340d40414000065000d03900b0201010a10f170f10042051400065641c4211440070182002020f8030480310200005a81441742d00b04070700c0000d1030181c42c0d21b0709208018803114480c034400d0080c4903107000c2c00005401407007902c0c0d1101c0c46294680b144240e42044c03610340405010050560061002c54070180403a54041d941030321162800d0310005552880c0840c240c405000c03000e0065801000000c03082480303002290b0304030f50020944a81c0e4161900080c82d00354003900d050700d814100003410740c4c800400304040320052090340001e2083e40d286c400041c1d120008a800306010381e04100840c0422102841541581860310b070078a14202c218a1512810200902400c0d0204044240d40c0c3e66180e400a8061106000416041c100318207040045400b0b40 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 309782230 1250 309780980 309781001
    0xa020a09090e0a12031802040c03090203010f0501030b090303040c1505070203010e070e06011d04050406090506251713020402091c020a2103080c04032909010e0d03 72
    0x2804000c0814485468050380807030040708401422552200c0c14401c81049840c00c0010a040ca000401082e2180c1007003006480c6404580c00104c1030051841038024018044000350705518000c81080480e5040e40140d041c2d90140030400307580c0c3d0751000c40507900e01c01664058010602807a0801c034103042c4030341d203091007a602c1c546242000c01c65030109082d5021190b2642e074513044003605101c0c02c032202c111594002000d107008200c000004c0306d1545c011800b030741d51900a07611030000030309120440c0c00c14071440394400304541e0f4910b030074801d6441c6401d601007014040076055914100c0c8901c1084103d8541d031a401445280d0b40711795524054521400d00102c1e0025000d022440c410ba0311080e0200c4441d09111a0645000c120300c1001948526a000000d0200c11071941103900031030840c190032016410309100300f0f40d4403803100000d150b00895000519900314a00b01d60707020301c0740048540d000c031003801d041c06c41525402021400d030f136030041894405604c620351429007107201e5000742d80a00c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 309783480 1250 309782230 309782237
    0x2250305030c2a0607111b0f0d081210050405101401021204080309090a02040f0506130f06050c0c0d0201020606060708041e1701020705101a03070e0601020f0c090a020a 74
    0x100c02080040c03c00f00000c030300c0a03101c1d0000410003106a400c429501c000c02141c201a0001d10598600200f60451981c0c0990080c4003500c0206d186448404043c0c22050700720342070030b8403442000b400300345810003103480c0d0121107a808400075071801c0c1805098058400b9113907007001181080000b11440311003171296811445502107000c8203e1a02d001400680501c801940e510058542440110040580038182d450b2040208000c14049109174400342d80040b00d801d641c03260301d9021019140c050f034200034070311912001d001510303540010080821000c4241a01c000401190400400700d1b1207400103809030b001079001840b2460003030000d0a003a84a03200300c50070b140d29070500d02d450603511410405180d01450081c459905040049001c80c00080700035440c004256980035142da4400780240340207601e0f40501d41b072100c1c40441220090401604a942090f0313500c02d0400124419502a0301500503e400141c800c0c134046251001c0020160456807942c640300000702c000c0d8030503004903081 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 309784730 1250 309783480 309783517
    0x60507020a05040e03120a06150503240307090f051e1306023103020f06180d0807050d09090f0e120f190909050a0e0a060e01020d020d02250305030c 65
    0x8405001c5100c6c0d0003142e40e0240060514200000b0003a15102e079034800d01803150900401501001c108945052040445000780040754040003003071601d201c9802504184d400d100c0140b00c45d641c0f507845148501c0c901d4000400d007699001c00d440c03c184003a44e0002c000044100520040f80140d002040b4690000000030311b410072039004103443c0740c02400b8080103141046801c10a503d090207241404282c11902185410304203111034070200900b84410b03014480320110b00713040c04254010385441c19001426644500c1c0b4121000f0060702c51030098105840c07419190032564003180c0b0400804241301c0300204509103c0340029044c2d500061491002400200700c8920008840f0012460a80341c980781d051016090510102c1a588000c01c0d803580140780180582800030001007181c20950081400a0038210750034a0901900c18481c03168442800050780304012089640140590200502cad20481408401d11030490031480c1c10000e40010014030100e19440c0001c8010039421179202007940a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 309785980 1250 309784730 309784747
    0x4150306020711040c120c0e04110c060106030e0d030b010c0b040629010e0609060d0c02031206030607080609040c150203040602100207021503090f100f0507080f07141303050a0c060507020a05040e03 87
    0x10b80d450300c0343da2b62006c43d02040c0018841d108019180c050119803c082c0070041084c8151640c0b20001242c02d01011b444690342649a409a01c920030070303c0e00540c450b150361030281000740140c0340c201c4440380c1400707050542c8440320b0400071000761400341c140d6514400d9a136513800c0140c0c58111011055004904020048010722688151045008260095a1134591940c0040740c6c2a1008050b503000303400000401034042c0c0d2042034194000811036260450740c46508040f0200070f41500310b0300f22100c9403081b5800d8035400101a00c100c5205500311141d002c0d40c1c607a4038080e40184000290400d00300c5906089080d0140c0107198410944001c44202001082c207840c0342008038095460741698562110058407001c0c040c06500000c00e0420302c0d40c070300f8400102042420024504020000d190600d00501c1940c04200c1d40c5040341142c4507201307180c0300d003004c1e612415100400c48545440c5000003545078000c60599210355001019500f03010324040602025000c0c0300340082c0079000411906e02c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 309787230 1250 309785980 309785989
    0x21042907050d090603110d18050a140c04090c050402090616061a0d0b07050a0c020901140a0608100303050a1b0605060406080309090c0904150306020711040c120c0e 72
    0x2881400703030008110154001c54040c11404180d00450100b5040002420800e0240007c41c2c40080500000007403524144548881e88906410010140c0c00340d0700301324007808098034001201486c201e01350307500d101c2c50301c08001c2140c03032491005001d404813100810142c90030742c0c040c0ca40e140c0040c000314035101a914195110803044002150540d507030355007072002d000300006140e10020092b0303420464041c0d503440d2412110300051103241040380000e00140c107944608680c0d00d41c1a4094404c9030306584a0102c075028055651445014001c4198000740691042103903c1c0601c420108600c01c10341152012106030b4064038000c001c2c490f99902220900300b000e60140c010034090310300066181018400c10082e1442903000881580c028030540903e5a218282541c01c60000f41c0b42c5550303580d05401003809005180c4400c02c1c0840344900010a12400c0d80080c100a842041181d504400710400c0000f1580d8203020400018120b483c3d80035565080c0e0b208402e013543c5810b02c0c40b1442c00c1c2c5000038 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 309788480 1250 309787230 309787237
    0x1d1e130b031e071707060806010c0305030f061c030c14061303080601020111030f060a06050405150903010e010504050a06050907060801062106060201090c0b0304081207090905100602210429 83
    0x26013141e48001070030401c090b4452406900101c092030304005000d51614010090b0001402d00b01261035a10080740c01d035580c19012120910344100541c0034030316182000780c08004040000d66401a8103599a0324200010071098071800c8420751900300010f058500300d80424006240c181559078402242c01920f03d440701640c401d0110740514a0185070201c140070450030035901050603c0070500c4180700550381c5c1c07160000c0511944400c0c684031020305001901506580f591080390354600303170510003030100101e041300c8050700851003840103450700c2805940e075110622441001801c1c0c50010b016981c411821624080c003c0c10b039040480140b00900000c03552a0381c400000350395201c03821002c01c40b0403000103004211a00c40345045240a072100ca4151180201c003c1c8603e407140300060450303011b11060300151000440c2004a481c0104e42050445542c1c06a440580b00303074450a0a014601c5a03d00301825030140c8460400d40f90000c0700511100040500300c500c00e40021325855080c9080c0507 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 309789730 1250 309788480 309788519
    0x80a050d021204210e12011812110d05070201080402010509040e07061101050105090105120a060533010f08090c0306040f301d1e130b031e07 62
    0x1c2070100c0c189403918113055002c0c501e9550007166811035401405401c810080041c14054413001001c42c9a500c07943c0c0141000780c07003c071034424521039840901c405c411034a01b80d40d260b5161109094001d6520503903c964a00002000440030040d84005500c51180d140d0001c4c4103040c1207041103e04030025054030050510380c801688030300d5040080075030100c00caa14a00a00000b00070139410040424540321050254600540440014440c101810440303004440e820610400190500340420520b00165544016072480500d02c6005284941401c50f072917441c0585490034034404075030058449080080501883e03004001d40303010306031002d00c10306119901c21070000d048403450b444e015001d1245065441d072501c5d0001c0000d1a100c541c402d00c0e907012109820011200c50f12606a10340907281142041c0e00802c10f170f01c050742c20003824815036840c504129210105400c00c1c0158904583c100060958190b01a03022003d81d100f041144c04c03003c0280006a49200741c07a4544100d810348400740 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 309790980 1250 309789730 309789757
    0xc0f0302060a151a0304020d0822060306061d0301110d0212180a030309051207030509091f0512150702101808040e1f090c03050c030105030604080a050d02 68
    0x708010408280300d9070701c4401404480d0030106040801e106004c4501c2c940c01070b108040080480c043d9510503d08090403a444100159a18440c0400d18510620b1001c0e5540118044402003074090080c059071090b120640d44510480e1800903826413800001c030103d5401d95a034110415040c44060010213010300d89001c0541c3c2c0c0d0540078121440d02c3c000500c08003900709040c104084c0e118010030080101601341c40c3c0070400c425582411400c00c21a107120440a03c000600e8004158009010380340000003200e84070615960310004001402d000300e110481d0404220050000d450580380d44101036500000704c401c4100140c0400d004020141c0c0c0050150740032480c440703522885070185840c101140b10007c0340740460b940d100d05041c001c82c0120303100303000390100241c0d80c00d050040d4000c0b4034040c920f6080d0301d40e94071222f070f40007801800d1003140081c2c10f11000410706140b0780c0882c0e04a4001030010103455999072540040c0b80c00060502c41080000c06c0091010040c0740060304041c2c01c1d80c80b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 309792230 1250 309790980 309790993
    0x11809020f1c0e0607050f040519080f0609101d06010f081209010c0803040501141006020706110d0c050a0f0606180b0d03030c020705031c091d010501030209010c0f0302 74
    0x252062216400c0140d00c004500300410800c8900000c1070b0304e80c0201c1c841c14401d45508002040c0d0085006a0300102d4001000e045665000030311000260101c54180c0c042c0c540041c10034440503158079048035100c00c076502080ba9020a020b01e40c0c090001281c060740868144420181200c9c1010004c0e07200c0892000c3e903550510500c0740620a801c441d01da0240c5080c0b8102d52030001038040c5507540e0300035109040c0480000c0509c00f0030742091900510704a00c400c0285010360500c0c0340f9030400d000343c2006100300d12004c120325000d18000003490f030221004041002989601b21414040c1c440122164003c0c010341c0e20015011800d1402e02074070407000821a0390401c110303142c1c40c00040743c0e100041401c001c0354500c5030701d032954502e81c400d401d45001b080072122184141d03d00006c070350100e90907214004888080000c1408400f901640541c1d42c0c520307140d40c46299070301c6070701d0b41c1003594148a4054010400d03503010b50700401d2620030604007891030741585d45404900011317200e030640c0940c0202 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 309793480 1250 309792230 309792247
    0x52809030606090207060627180210020105090c03011a0d260a0f091d0c0c030c070302040b09060306071206180509060a0e0304031e050303100315050f06011809020f 72
    0x20f0203810054051855010564000c951823250540034034030920a2140c5e880c0707462540c07400b29041c814101038002d0514501d260040070000c0c02080103c4421155015903100d00d4110318041c0558080e03211081c40c01980c10076600104130361001040811224082d014141d020303124140c0c001c1c0784000c0d00716000940c40c0d01c81d240c0091b042c240155080d104101c842c03c03040c82613407440f1120441212461810340402d54403407501e00c8651061300e011104038800450310203940c100c00162142902d2081d03078244205203d180c107201c82034070306036603256041d0400380000714400e1240034850035010a00d200481c1095031914079504110741418501c072410380303a00030403448950403c541c0750003d030700c40010000120351084094580c0200d000c000c0194ac00f8103042000281c030a03448481e02600030702a2503480c00d10725082000300340b0754032088961300784050030504440f01e14800c240c481c6100700c600ca082643c80100442d0520000c1100d0116141071400109a4a0039031000e8050f01c045030141c42d5603031102 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 309794730 1250 309793480 309793493
    0xf121608060a021c1e05010902041403030c0d0804110d030809010506030d0e100201060e16080916030209041b0b0c0709151208040e09030a0f052809030606090207 71
    0x40c42000700314010050302c40700140b0b0910f5080c0302c8a41031300c00a000c03001007101511a1062041400d01241000e0002c950003002d0741c01081282c4004400e0311200c00840c0c14180c40c0d00402e000c600da43e41000e14100c914030f00804000d540144503081c1d1700c00440301c440c002071415030402c0c0241c002410013001c2200352002441003a820840c21030041c0303200d8402c1d12000784000c0d2a52100790050010072411284207000750041000b4000100480708286051010314007040d10036145203000034036002c0461034036080424440d4102c244021410201070440d024000e01c0c10000e482141c1c1014003450f900424003c80c1507810290100c40c00300c0b41d6418852442d20310b0001d058000c04004d610f060040402e00700030b8401c1d442122891046004c2d4980242080c1c600f034050b650201203003421070010061804c80c088000d100c19403058440b80d280c2040e4031422a101e01480c126222880020650a8600c95102040c101c080704a0300d07040340c5458490f038170f40069034016884101c1d6190042224010002e0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 309795980 1250 309794730 309794743
    0x1002030a0e0c030705060a120501091a0a21140f070906080c090103060f0608030a05090307060306123809120a09090506011e080609090102040605090f121608 69
    0x9000c004120b210000000282c03601e245105051050400142c8103102c24020300345c400da09071785400c0c100415a0b4903903880018000400c52440845591000b030004c0381f410280d4002502e030055018040145207807a185002000c0207020349031040d81c20400745549030100719052416030000d024200e90b40c90b06e107944040d20540d420015094201150750f03c910b88910102e0750449800020200d88600d006030404000d10051f005903c00d8000020750895a0f85c1101c010901c001c0260b003124082c82d0b440800700c08444140c0a250a003103404081d500100743e5250340e20f111517040100345424030040058920301c03605440f0045401d03011020400c011142c00703000ea10001021240468030b09146504010b01000d0680221503c00e036440c4049031159110303e281410074000401005030743c1f98184130140451904480480c41064044006210f0301c1040c001e40e012505192076190814070b40004100c501c1040309212034007c20742141034078030032000b000307005c07207200c44000a6880d02c1c0c20301211505010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 309797230 1250 309795980 309796001
    0x40222080705030a1b080f0a030906030203151e090a0606090e060307051002030906040e01180e0c0f04020f040e161b030507051501080f070f030c03030c141002030a 72
    0x108074020802c41c68030301007401c13071001e42d0000e21000e0103206540c0c800c3c1c04600c59000b220541c030440d00a078500c0321000804c1c0c3c800078003d8544c5002999610000c5080c0d200455584560482d00c80b2000e000e414107071101400040d8000740c0160000710040070883e40c0e2801c44071014515200c070f0040000c10740007401c14001d030140c00f22a0001c3c2c904900440d945038164441c10340546941104040841c0c03083c001d480074008020803059813190303980084200e9480c203000c1c4400b5103825000d10701c1c4408061003502c0c01304d075040014044510821301088089003208503000c3d00240c0800004a084100744014070280601d90f046040301d05081c601912002418901c81060011071300c4940240180300c20700d46100b550625100385d6500440c90405d00b403540c1a6102003140824a00200f803148000c1100b00d01071104400300c1c1d41c1c083c0c3d60b00d41038440380e0081c800640341003150201400468810075118200c24041c0310344c0300f40c0005200c003541c44c101ea507050700c07041c035903002c024400005000e0007140e0b8000c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 309798480 1250 309797230 309797233
    0x2090f030a23032704051e070518030106030501091a0c03061e04090c0602060702011a04020a03020705030c0a1b080d0c0c12030e090703020f0a0f0e04022208 69
    0x6100c9580e810914032014550100c90324401c0e0b01d078401084100201e404640760100a1491045043e4101c030780450a4041280f1403810000010b1000c4401c240d03130010242600d496170f903a80c58480c4195155449201c030140060364100001030b0b5a1424020b010046204000005051026040c4100318594281e07000500301818818070900d051181c06494101f2412120705a00c40c00b2043d400030050620030450740c2040c01d100d82081031001400503403041b501143c00307031103059444c2d6804a089440300840f01c014521950441e2140d800c0c01d50140c0000301540c200145481410f0700d40501d541c0214443c9901580100300c07000c00c011094441ca0380c070031600300d0b00202403418890110340b00c1c80c19048071070420041036a5402400f039101403081c0284802002c030031008030f2905008240f07a002ca4002d038043c8070450003003800f6902c2882294041030b07080940303504220588000f102c44e0104601c44204000104121071201c1d552840141000b9040c403880d840c031100780c8500000c40034416032003410035 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 309799730 1250 309798480 309798493
    0x190c0306053a0305070312140c030406060b0306100305090f0f0304140f09010303030c0311030a09020f06030402090402190b030112030f0206040203070512101d0610030203121c090602090f03 83
    0x107134002c01515106a858181076441000c01501d0800801c040740400d11a03c03a104188150034035600700071405180144d200780b00301611105211031a10042d11040c5c0c101205403000765245210341d0005402c0441201580e1130301000d0000c113480d152a4031380d514000d4200080130400d006204601e0551403000340c40c9145025107210008040200510000d024581c80d001d034000440e22a901c2002c0036800040099120304000319950024020114200d000d180320a48204e045c0ca400c100351782c0316a900500b000c05681d615428010700b03611880340014190800034010900d445031001650191800c1e183d50a4111811304009205ca1503010400f410b40d0054024000580c8000c25160191941600c040c144911244e5082c0d03d00700310b8108000100d80b84c550625407105111507120030100c003020440d112502e81101130810b0010b9448020f40c1a488509000036407404600507009104407001c1c816101c040030312020066a0400d40101c60007a80010441058500880c100e2420407054004103136 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 309800980 1250 309799730 309799733
    0x615030b0a0e04020a0603051503010905030310060c02030a120c05030c1c0804260403080f0d06050a0e13061b02060f0c0f09280902120f190c0306053a 66
    0x13118503403800748104242e160400640e0041013603039191072002700034000304812215820195142c2c0c006403020341d400311600c40c000410307922440551010a0b00200a0400101c8581d42c04500d10a48034000003481100c54006020035000d1010781a100180c00140401c40b545c80c800304c1041c5100c0c40b045062215803c1440301013107950500d400f0020f0302c1e01080d041d00380d800d00206402c3c01a54002003581400050b10b0210a00241c094a290b000c496000e0110988502c10003443c480300d805aa581c028000c800103051841507941c07154020300a02d0300090b2041035403800c1008408004107400503900450610001c240140070310f6501c6a21f4a001d00e05100c00030402407050310554242601c50207140010043e0b184400c889000c61210885914088031394980d0002c000c0c1d08800e14034020108031030006111403018040051049030052040c0700c8584104120308020150303061800200f66407011b020545032581703400704a0103401d4031300034480729084800ca9020020002403203220005c100001d0030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 309802230 1250 309800980 309800989
    0x6050904030f030c050c07030501020c013e040b04080a02030d090602120f0409060f082b080a0b0405070c05241602030c01052d010e06040207060615030b0a0e0402 71
    0x101d010380c3d14004c101511481022601c90103401d442c4107281c0079030080081007040540c0201902d801c41d500a01170756000c0075102c408203440320080e42840a207c0d8100340c101d21202e48100014068102060505031a95140011508180c02801c43d03540150b01c1c4109614040003903140d002d044c0e1030b0018099040c060000d403583c5042e840c8074502d040204082a241051505a40203001c0800d003c100a03070351003245031005100380c1305a01450040c4420301842c01c404400940c1c00e000a0746200740096148042140c03401d0004003500740390303035a030002d200c941c2e9164003c01c2d002e5445650380340c208061a0401ca424040c104c1c11400301d03480c000e4070303007031601d001c101e00700742e100d050220718840100261000381c0c02d501c6012a4040e0369442c05080100109000c5c500d50a0350458128000c800321482c2c806d48505002800380740540141d031030024250f4074054009002d06445600e0124003da82e50304060b40c1840f640d1061700c0030a4640c040d4000c103050100c0c01800070400090201d4050410b5000304 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 309803480 1250 309802230 309802247
    0x6050f100b0702040207150507120e0309090618070f03060b1602190f0f03060c0f0212090604030218090c010219030302070c05060703030f0e0a020114031f0b040503010605090403 78
    0x100d6141000c030b100e105555440d416580341540000003141d0000356511a000102011110480800c00041100010103054400c10100c60032841c001c41c9840c22010070400000c130000c1a40c0d030702c408003400049100c1030152080740520031507120b1040300e501442c40075060701c0c1e264003c0442c4004c240546008600c40e9040c540195405460780d42103061810725002c024941074102180329070280b240000c6281501d0100b0b021280201400c000003030400004550b02c0d14500d500c0b50069120809580c1240c0c00c003801000c0f1070200a10303007841d2580e6507001c2500415118000000e440c22901003180003d0148948001004241701a1500805101c07002110f50044000582056800308640c010415207030f00300006818010034003030300d950041c54008d0103030080003003d11400b400d003000080f02c6000007070041400b0760305843d00a80341440c41c104c0da1035500003e10000b6100350000400c0c0c000590100c20740301a10004070b0481d9a941800281401c3d034545511a0b40503803480c104200100307038044400d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 309804730 1250 309803480 309803489
    0x15070629040e0a150b060310030203060703140f07030608100209030f010b0306150409020402070b04020310061a130b0a050706060503030f3019050f130308090708070902030406050f10 80
    0xa4103440c0c21102030000017820304500ca182c010300c00000340082d240c00072960408407031084040302e060340c3d034400080302520b400b01c940402d00d40101c40803c41c9030f1a40024075a200c0003910300001d415030f45051051a086c5d01e0b00c520007265600080c4540315040070304c4151444a920700081c41000310940c04030361f948600906045a114500310f0f04e114030f0b41c990700072801c51500180103540f03c046c80d0801400c4410b065408a100e8801c0d05c510421141a44c05120101c56000c02c00170094010305003c0e00250740300801c103040301c01ea500404100c00d503500c006801d05022587c0ca141d1100054900302044410780d400540c0300f40d0090002c0456203260302e00300d681111043c03140c088036001d02c00c403100c00780c20541c5000c003644100b10300304a940315401c000c00c0500c04007658280040e8440f0000c00011902c10b070765421041440717410060100c0d0161071000e800181c2d480c2101d01c0d041d600c1150504046007500420079140c1c002090100340b0280c1d01030b482c0c001000302c4050f12a0304085001d00041c000e01c0c0314 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 309805980 1250 309804730 309804743
    0x60327010c0912110301060e01051206041716020405010f0e09120d020c0a0f21090e07110a0b07050316020607020c190e010305070303110a0302060615070629040e0a 72
    0x2c4560400a28004c0e450460801800038411651101c005000d8500d090160900511040c40030b05a20071000a0b25809950454407114841351800030712132040d07010444088040240c8011180141c403a40b24860081c009902d580c1095410100d0384240c5880c098141e040da540080c00c5020051078060407207070320404c0501c0042e40c801507401c0b500d06201401c0700c0a40b0480b0701083d1134003881507806018a4548084a170b00b08180110a001d0b100e40015009a800f02e000c094000307485075025114075030300e200c40201107503640300c0c0c00e503950550040111350b5440011804403d00c082e070501441c010b80601e0040c00904800e2920400007941c980900c8402440f41e600e601d42e00b01c5c500504d652600190a000f0440e422668580c1000e07135990200e440100c0c001900019000b444200c040313043e801d03803035050707002e09015140c4004208640c207415000b201006401c1100702c00060042c460101e4650f086401c0c20b07000304a040c10001000e5480d240580528100348414040c0080450451030036548143c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 309807230 1250 309805980 309806009
    0x1403180f0a06290613230a0f030503040b0c011104120302011d100c0e04090606050f0307030b01030f0c0506031504060602160b0f040f0807030c050619030b01030b060327010c09 77
    0x36810140841c060f44a0b0b0b0942180c1e003030034003110f0307030b0480d4a11b0008000e8801d04003d40c0d030784101e1009080d0740d00c0040c0c0180c006001c140100031a120042030031050900020980c10300601e6400c11550080c3e001a42c408a420409400c0580a0040e00c40380f141119800300c42650415440341c40d81d0b80320076098006581d60441d080074600983c4901c40442000c1c0013041000d04030316240004100900900348a60140b4483c100117141c001452000e42e6803019000c401a4a19a5048000322000030100c1c0d08803418500443e954407407002031442a403036111600780c00e1070b400040c0811690242c02c610115080990b0140792015000b01c2d60003224500707002c0076a1403402e000001d90b03900940e00300500e503420449000581c2040090703404181ca0040b61200c51065550b010451144038080c50030310b0543c01c040c0340d1282d140c002e40c440340b81e8040604012818403004000101c2c0342c0d00444182c510701080115035403a5088803c456044102100000c001c10015544003400c0a156071107101c2d80c401490 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 309808480 1250 309807230 309807247
    0x80601020a0506010b04081c0c080c0111270a060807050d06031b1e03110609010201090b010806091015030204110d052403030a1403180f0a062906 64
    0xc010703004a40790000c0c161105941c4900d4055a2640144104400391044420783d4015065003020388046540d507403a078400c02e41d841d82e1050207542100300c54403240e550701c10721000d481c56410000c010580c001d80b03080d0283d00c400c402124104003426021350080c40d020000f40303c12504240e940c0c0d044185070621940380c544040c2c51030041c05080d0401814450700841c1701603005982c151400070390301c80250446460004210040034220a440007821101454000828904198000300b03070f40079041c1f001055111454407048042142a4400f03d21a4008000c101d9041001e210400d842c0100070700078005130205841d40f000041c8203000292180307903143d05032810105458215040d141608030b0901052a00e448800c440c4102205144280b40440f41000e00750b24001c400c80e0641041034035031040c106854141400c50303400c01030a056800d0b405c201d440e040028100070394402d5004c0744000f044c502c2c0b000c0c40d00b1016162140c40c2c444070071034211021411580c1003e007981030144240c800b10784a0348603 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 309809730 1250 309808480 309808483
    0x10302101706090a20030703051f0b070c05030616080105100c020402030a021b070501180b0d0b03120d0f140c12070507020d1a0601020d0f261003031b0c0608060102 72
    0x10050001205d20302c0a00e42401e51141002440c070806682d282080290360303484c403080c10500c1e401c82c84003121003480028030294290501809005004a45c2c1c104225141c0010030325014050700c03141c5140c03d02d80142180198409a42d60140005a800b0701c80281916400744c800450441c0003442644c0220001d04151a5036060710052600301c8040d548000458101d15251562409290f0003d4180300f801002000321000c82d804444441300190318000c0d1498150008202841c49903616000d40a02180303040c0c2a02d000d0044940741d80000604910305a200c402158855150203e84800e004d08000000c83c9030402e907985074a075a10007101c61b586040d0100c1d5540b15005000398072a501d0001c01080c4034024241c030b4200ca04a40d40040f450300c4660040e0ba9944011055a00203000503401400301c902c00c2d241d40c14080d07481150a404119400c0b11a904070300100d51903058614480700030004d15034420500c041d4400d020100700820740403a118030480c816640144818040b01001203001c5910 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 309810980 1250 309809730 309809741
    0x606061e1b06021308070506030606071506030c0b0a0e0a1208131a0d0506040b0303031605040305061f0b070c090b130c030e010b06030907140d05070e010302101706090a 74
    0x52000b4110341da48041c405124183c10a4040c000e00c6101c0c00c2404255418144c044074011800184050304242d0f0a65400380901c0d00c0403602c4a0454484c0400000203580ea400203000c2c0c88028489030300da500307030311005041d4440c0c0c04940348210f44c884c104001c1035500a02d041c4000780c01800702c03503960170703040b115401080055000e00340405202d00300741001c00020300a800206200744080c0541c1d12040200401c2d10700d142c60640d4180c200304041080006940d07807107586051207041c100c2c1881c3d640d44461741400400c50b041d504c803c000da42e258107801824080798014100c440d00e40f5081030600d8032544c040400314010444040d07a207920140c0d465580c05072102200c405600203202d06000e070b16008025010100e00002d2960a00031a59401e00e002e505a81c82000140700808038a440d240700820803091146a991b0042281c160b00d802250041c800b01c00a0054080b01981c29459481031085140146c400403007000b40c0b46000100d0207c691415030307002041220044030940300c00a41100400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 309812230 1250 309810980 309810983
    0xb0d020907120e12122503140604140115020f0f010e160303020d0e0a090c020f010b040209130f02090907020f060c070812040203190b1f0602030f070f060504030206040606061e1b 78
    0x403008100c102c0702c5541f40c0c00416000c0070700b550100150311850140000c2c1c5d00c0b00402c18103421403000c0140040590b09481c01e440c03030600c0c070403990000d034000c0301c0301d05004243d5085a10359440703070300661046804000640204d00702a038a1a2298a0340d10000d4580308000c2c00c400401800700c1c070b100181c0c0c0d0742c0400000589280c10741040243d40449019660302c00c0544985101e500300307440d000300c600d007900c00e5800c1c408018210421003c9804918801001d1809940500e00c3e801d210000c2e1549846d040301d0f20403000b940040008841071a4503902c1d01200400300140c2c8202000b10b0300c001802481680c030401c1d100c80c25400385440d075200203803e01e19a14a9090100c010304542401c0c01050000e00d030040c60078440d0551207205415001407c20300c40e004117805644100082d00c8039404040042c0788083c010010060640190350340c103000d07203909a4080d001a4480024442800150320070000140000c0c20041a0000b40c184059103602001d000c1034248a003221a00c0e03000c448010218412a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 309813480 1250 309812230 309812281
    0x901020703021206101a0f090301060e040c1805060a0909020a08030a0f03060f030b01050d0f08070c091a091308190302030415020c030405040b0d020907120e1212 71
    0xc3c101008419034410085400c18820340315600001411180601204450000680303c58030388000601150050f51181055075003542da01c000002d455081007000d140664400c81a030b0005a207003103011540181d00c0c00381e002001e480c010038002a5500c8400c103604590007424046410401400040c1d11030042c0d50286480b404000b440d045c1141d0b204074040c00501403038a08002003500d4440c00f40f0b1311041c07408024240c00710640180b203a880c182a016055034480c09406019044c0d943c1c800f0141c0d04280000c8810984041c024400c00001d400782040500c6040380e51041803d03640c0c002000d18101410440300f8244a40c25902813207502001c44100c61b101c918440b00102c0c40c03002c0240294811581500d000e002c0f00c0354800e88810900031101c4100480009504043c2007804000040c90b000c2c42e000c2d400a08030500c83c0c0180c1342e0400d140d104039113544400108a00e0b0307c0700380042c1c4114175145d40440e00701c6240500c80d018140c0035201000361103a0200015642c8400003e0440ca4504550b0443c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 309814730 1250 309813480 309813499
    0x5010f0507090602070302150f13030803041203020c151306140106090515090114040e0a0c080112050312070e0904050a02150909070c02040204091a150a050d02090102070302 76
    0x51521500128090780d103070340e1640c50160f6118403ca88492176400002d5004549110f40d107049001e400140031025440d40350146030005d00225501006401d510031100c0d03840100c03c00c01072100081001403031040a0034254a00000a00780d0381e110107001441d001c6220081001c280c0d564004104031069179401901000800c155071100c1d400b0f40800d01c0b1712000541496000305007406d01000c0e0202d102da010314420f05200303003040151094405001000014072041c403000850100540c1c209018050036000024032800d281d03002442c1020580044d0000c0124a10000010300d0010460350301100350f0007842d141d512540b5003102c80e0010080c07019403259204040c0828820085000440d4901c01c8441007a000510400c40405004004c482c56000d12030600003803140f802a641d9140c0c0c90720007000149820744032110340c400c40e80503240c03074260b20745002c0504e070150600000e80016104407135100e030f081a0400000401c04c0c400c0f007580580541d00490500c6180c3d00030031003100a03641c003d054600 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 309815980 1250 309814730 309814751
    0x190c1205060f07030c0507060e1f05060111011806050604020c010603120e09070c030f020114090c130506060301050d0c0803071410060303081321020c0306010e130f06090501 76
    0xaa9540640304020800342d03040216240038000d101e400d0203074000d62074150602456071100801000309601c00802400341c40740083c1800680d1003610b03d0a0f20070203001072507080100c001012002290300e9038005078905401c403081c1d280c8500020780069480040410242e032140b0101c0d0107030150a05101a40d030820b4000301c100100107000702d1103509603076030b0004c96801080400c065683c2c140c80d880b0201d4000142d40001c80c2c840ca102ca00b2000e81d600020034006004103607025140811100303655150460540c01049140103411528000b550700030902a6041c03820002e4a14031043c801c1c14410442c0b038805504020360145003030010041c41e001d0380d031685010708040d01e15180940c0003900901400020030f03815003141c800d410550303070590782c0e124041d5030724102c80c105c04d0104501a9a540c62074150002d0b40c440c104c1c502107000a4076400b6240309400d89081c5842c080c03042c0c0011f207023070318480c0400c038504d00d011085041541c1c0114002c40e00e0081801c1c081c008260803030f0040c08035424540d5406 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 309817230 1250 309815980 309815983
    0x204090c090501020d0e0901030b09031204110a050102030708040e0712090b04060b040c0e0411041a0a1818020702060904020a080f090c010e2e03051e0405190c1205 72
    0x400c40b002a003d48600d442c03904001c640322001c0c4030300d0541c04401c450050001c960b8501c00f141d88952400c089900d0140c110303003210f40d10390049a00303d80b400c02c4c2d9003840c80b05007040180d80d40209400e000841c2070006590b5120704074065400385503442c44800b0005540c062151104031801c10300c4000404c807489180c2040001c0d03d000300d8040e0359050038040010010308051007080c00640303059036080c0941d002c000400000c4d1015803240078040005010120f85002606042100442840c40059503100e105402900340700e4001500c0314070683d042c00c1007011944c4003100101c920071440c1c0042c0d4800340d42c80024960f01441450382d400a1010940340841074110307000314016498030010b000c2e00d6842d0920741c0e556103280c500c0c041c00500c040580e48a5400e14080c4100c0c40c00403000f01c052001c80744440a5443d0707041b400c081c000240c0701c10500945284002c00c80c00380c0c088071104034103a8070b081e485842c0d549a003500704050070928070729050140000504082c0c050702c2000c0c071410581101d8105103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 309818480 1250 309817230 309817247
    0x7050c091506120603070506040303021b010519022802030601060c061b08040606050301110d020d06090e0303071b120c060b090a0609060f050120030403060935030a0f0204090c 77
    0x250203440744110104081c54230b041501c0459034554010f02076420459070468080515280b4581480707414020004800241255810302c00025801821140b4807541071400c3d80703000308850841c0c0440c00e100a0003603140840c1c1c144c150b03055400d20f01100252803406400818105050602208a2841c00c000990f0b0000f1520b0003a07010744003d010300c03030b1902c041608858515020070043c55082208402000c2581c0251001002c0d04030001007890381ca40c440c0041d264006120b40c816000003081041d074941255032004600204154031244c040d0079964040d00a052240030300500c48005881000c000381ca4006102c0c050025001d040c60f07003814407070b030405800d140c045e00e5802e500700b020224a03040440b000d8822504140e640304618511754800044000e03c5a03201c10040c001004084007240441c0107100805103e194131541204401400000030341010952808104e40326885801c130071640b20980f0b0300f100311410000741800c2c1c0c01240b003000b4440c591000740b04500303122480281c0c40d00300c0c205 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 309819730 1250 309818480 309818491
    0x4060306060809012c07120c0e0f04020901090e190803090f011a12070b0703080402090a0b130b0a030b0c03040605060d0c090c03110d061a07050c09150612 68
    0x2c035001a03c2d840002400d07526085075103019685807035680e082c5c0c00c2e4281d540c0500030030590107940c0d20350780b03a003d105203202940c1015245010701c05000c02c421090280c0c05035103e0514070031004076042c1607000450920b018860101da258468100c3c0040741d00c0dc3c002241e4444500c1000c0b0030290035860409200c0e002200e044885004591082c440b42c0302c103001d244282141e031000c0380d010710b881004003c1c1e0b03800810b441100074031a6006c04a000d0500d8401070400c2800b03030301e58414a107420310401080c2100207105201440c280390400b901c0c0c3e2101c5802c0da14407601c2c041c020076144407000c0407515000141e4009004005480c0034880030820b08001113004900407171040c4801e913a10b07014070014050340c140040c070316030b41510700b0010ba041c46e038420301040000c0e00d40440e042c080c448041c83c40b6007211110600c107a40d5030b80e04120300007644031480b94039800061a039013015025165241c07104040002d1a0040130b0003800111016100e461401d110200105650b880d40030a4802281280c0b040700c2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 309820980 1250 309819730 309819737
    0x60310090c0e03061303020f060109091b0509040b0a1b0c0b1302061b011b210506010e12070b0a1124150d02030d050d150506040e1302060406030606 65
    0x2402800188203820b150003091000d00244402d440c1c0e4440c01500b0b0070350540a4045014030303c60003035480020711245000701255440425200318900700307600d1800c5040845d00032480c0070300c0c00304003d840311203031554016080424603550380d40301c0c03110b180a4101a428004013200c1c40e50a04580c03034100e41c0e1040e8440c01641d0205840e580d00391803002a448140d0042c0d03004a062120900589103c0524900b04c60528008900000e05d901046500120000503801184810403140842c440b800d1007001802c03401c0200f4800ca080440000e80900307441388a1a000d5190050340308044501001190000d2468110762070b922051041c0090103800d018906804500401c0c1e1b5032184a02881038000703c040d8100c01000d22074543d001c008612058505440b0b80105240d40281d025a80510500a03040900d485265888003200c0010382110000701d40300701c0c15200d04005000c940c803090141c8080d150b00e101e00d610140c13181504c544840956400c001e5210a0009010030300541c10b82000c401c4500c641c8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 309822230 1250 309820980 309820991
    0x5010621020301080304030f060e0d120c020d0e0d02190b0301052e1101090c03231f1814031201080307031d0a05090108010c02070b040303020705041a06031009 70
    0x40d181010391000b071050401940c01407000744042014805441c500d94880c850015004800d03480080c108a284090140880c0241d203241d54000a940035014254210b8800780c0000744020788050305041e042e000ba84c1c080c802198440701191510f1a159010440d2104210002d0f6502c9102050650090240501400c6810801c004183c0e448000050040f40d85034404130501c2d1070381c403c54214213500070522a035034170744401401052900c942d903c080c5000c0c60140c481c0c440704452840d10268201e800c01781c940e00c103288402c0302103020310901c0205011010042561900440407040445003907002802d070010303c01c400040b020001000344007140b02400d04001581e42d0b502c09030f40b01d002c1e02c0000b034041034205030180c5071100400c04900700410700400c007441080c0c43d90b0209450301c000b40c2006580745c1d0359041406190b601000302e00010401c28007114a4182107a500a4a4413041d110f1a070250b0344910076600c811601c50003040240da8040c02c02612482c2071487c50a02044074402d8101c0146050b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 309823480 1250 309822230 309822287
    0x3150a151203080408030606040302060c100c0216350309010314280219050405030c060403020a0b0306030106030f1b090b0d020d0503090303040f2c0106030513020301050106 76
    0x103030030010401d034040e1101481561142c498401980c0000d20050b40905c00701b1011005aaa81010b0302c031075940d00c1b004059800314000c0003c2100d039840384050542d440381d036a09441d0713199101410103035030f42202046d05d07003503013582140d20340f0310b401d07030200c150036245024a12160300000180c4200d400903038051085000b11303107010554100995440c40743c07107200f880704c1c074a03060140140819440304081c010301d0100c2a07011009050110740000c400180e00003410403280c90300304003081d6003100c2226020704d0a0300c0e6500207148001d15100e8005140408000a511aa000c0d0700403401150030000c00b2901d4482c900c1c06040d401c0c100702c602d5818400054000c01d03c403404d8400c134049124041c01e0700c1f40d011229001c0120444084504441d130744001c00103142c00f03403000c0c40074000426852500100c118203003a0500b00010460a000119a01503005000441c07007c0c4416411030344141000034141e120158407241d03002d10500c01035019070070300e0000101c0030f500800020040415016074842d8a401 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 309824730 1250 309823480 309823499
    0x90d1502070501110d2a03090c15120e070b1c0b060f0a0816021b0303090d050604020901081b0d03120518010b120d0302030705120a0c030506030312010b030603150a15 73
    0x203006d07503071441b410307000079480780303207020b03902c886512170203203915008051b40d404103c07019428083c1c902e80054812400b00990008030b0049000c0842c4440281000d6814100804440d0140c0c0d0271182007036144a212165a440c160b1100b01030140140c1100d60303640d18400000340c150b001e2400a400a480c9400040e1701d0b2180108040c05034000341c0c00340011a4581c842d6400f01a0004001a4180010054850b440e034403240ca036055284180e0192250385840e00400c03ca80b94140d1048103a07400c50821030420060780756100c907503810200c403124440e039650b05080700c41c1e40c203038411040b5135031415050002080180c2900342c1120500c000900251120206101d03518041a000303080981c090301c00301d05414003e40155034003801d2403a0035070034584a617502e00101e10341a00c0290440e030352400307440700c1329500d40078032680038500307400451601700f402d2010010f8100c14480c40745440750110224140399010700c0b107902800b0b01c001146840b400c1008880008140b18100016040c8050030006000c401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 309825980 1250 309824730 309824771
    0xf01030b090703110d05011e0b03071403040606090212040506070203040509010e0a0e0a0b0901140c0a211a1002070b0d02030405012d060506090d1502070501110d 71
    0x141c00700c03405440340d240580240100c01928828080305004030f00c414001ca1003228001c00d518010000700040284401030020079641100301d0b562000c1080224407900702a054040300222401c00e035403541c0302c1c00d00740b00401281d001914480d0000a03c65401c0c0250400140140d00481c2520259243e143d0705a03600d114501c40d6981280c81040104804003128849aa204441c491f01040340b07442400c005040c005124801c5500c0340c0b4040a12001c2c05007445070303018104030020202c15500f00f00c9003202c003a0250142c18800c1141400023044080a10140030490b8202440140810160300c224841001c00d001441c2c4c0c0500b009020043c0c80300d1000910408681d2811043e0740b60111840c00c06000c3d5100520a40e51592209030f64803250401c0d0364000144a010513030040c8041001c0c00c12410344500b030340001d102d1030080c0868451640c07007a490101d00c0750310001380194032060944c5500640201c940103062946051070b03040c0d1303d10032500108416102100200240b06040310b100c1d40804 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 309827230 1250 309825980 309826001
    0xa0b010e0f060d0e0a0305030f010b07030c02100c170702040b0303070b040f03020c150c010c030b0a05130605041b11010204120b060105130611100501031e021302030103030e0f0103 79
    0x61124035406060704060004095800e90b861010030b2030300d1134804032803504003455011800540000100900002c0c01b407110382c05481101d0286107802442e840052104140050192240d5604043d90f0411405060300c0403140c0e51124502c000d900003501d4040301d0740c0101c50306074001d50034414022010300c0c000c0112117005500a03582290354955403500405d400304e1140480552107003500c500751964a42e884070703019144400c189540e5100d40c0c460b2900303560040c41400149420322071001d04076603070f40c102481603c03006d550041113070302e01200c19005040789a004039006031400c0e044041000300c03013002d098407020303d8032100c100d65074607060785080b44524450428138106070041d19001078105110b0075045001490454100a09542d00c008a02c103035611510204142c0345070711032008428800015011071148041005602d50f840703140f040000000d031501820701d4080204115564011880c000081000f41151290b8403442c0c00f80c505228503586520032015038001d032042d50300ca0f010740010390 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 309828480 1250 309827230 309827239
    0x6312007021e030f03120a0c0e0d0b070903080c0102030402040605060c060103020f18090a170c070b160b0f0105130903020307030f02030405030a0305040905010609050a120c120602030a0b010e 84
    0x2440c0c50b9805042440c072030b0301255050059400c00d030301c880420400b416801c45070954035a05810102c00c1d60741101d160600f03401c00e0080f10380410b0459030321501d24001c2c1d0364100c5004c20103951818002c0711a0080d03508010005140460a0a000c0c201540a58440d9200380c0d02003240d9a1200100f2106000e84111204141e101034014001405c003040301a880c5c00010b03000c0d07403042d090a00b1300c404210089904643d10780c4440700607024000e001c0f51840c12210211107881c0740c070031444580d07625911180203460750a500001c024062071000b860b0080403030f030801d0385d58a160804a000d00c1e54102d01333106403489141020780207400c0211521503001003560580065260210326581655040c80090013034081d07000a00000480703803414440d110a85129a546036692800e10451008131441a085a402c0100c00c2e0020700546c0c550b0100d403026a014444051440307025441c02c0a5064115080031684650f050941000c01001d900610b009003005182030001015544c01112160026140607620 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 309829730 1250 309828480 309828499
    0x2003040b0408070f230d021c0512131710050103030206070f020d0816030f06090221010f05091918020f040c080106030f0b0303030f0609090d080631200702 68
    0x18088505c20440100050301e241082ea00c0d83c1c000039001c0109000491004406030540340801409121b00c4d07120b070002085603424040d4104540014117414065540da190919210b07544101041080c1d6050080c0c022050083d582c413454001e4550030142e6a86010800020100080d0350021611038404010380e030b24000e455440d02c042c2a03003590b00b95071b0101811b0755242c101c0514209030242501903c4126000740e030710030100003030100f80c0d003811721400351052481005000b68011a03e10004403001203078400b00c69101d2904050302d2030011815403090034900b415940c10404108280e911080c0200c4041c2001704002081c0410b03101180018400561904014010580a5480b14803415004003001a10001c0131012038030f16441991341c0f0510300003120401c040f51800c0c019241c1e0161814001c2d15128080000c003600000001d08118400c225a2100c03100700c1451044040b00100c9014600b00003100d10031015005144903041c1801100740d1901902d01c20616808540b205a4094043c048 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 309830980 1250 309829730 309829769
    0x1120f0305091c080c150f0c07030203130f050a08011b030218030307080d0506030a05070b070f0b040f020909030f0306040207060213060306050a05040c0804032003040b0408070f 78
    0x610b9400501142d03032081ca40d0122101c10b0f003107251450b0000344141c43d00d41d5600b06410841d40f814081e046170000c410898420450240e03030201840c5d03005940c0030b0310142c0340c2c61146416421405130104110034031040d040000343e09011400b0000c225281601c0c0048400c2e254009a800e84004002d20301e030341c1c09018030070100c0307a101e0b500401200c04180d4290182e400c2d58400203055034000c0c00150360012001c200d0a00d0300703400b44200307a00120110014a84403070341e0368500b52190001c0c41400e4918a0100e060002d110301c0b202e854400e140d100030050802c2c501071074400b810400ea01d03401c0e40604042400107081d114000211000300c1790b02c100b0f940c02e6075103480170400a50b1025a08950007602842944210800c12002e14083d003070640b0013051440c107000030b000a0b048030b03520041c4240c0c1084041c1c0c4000b0b4010709142c0e0800d4152500920701034040c189842c0c0b10041c00c0d1040b05030f100c0014005010941030307000d0025652130809031010300740e03a1a21002c50b5501c0b801082401c1c01c90a02d04a07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 309832230 1250 309830980 309830987
    0x60e04180b07050f04030c0f0501020102250206040b03010b07050f010204060e090a020f031618030f1104060510021e0705010801180b030a030903051c1409011101050a0b01020601120f03 81
    0x250302960303914080c1d184c034210016a0b940c580080d4000c8607881450740042c4800d90b00d5542040c0030304028070086041041883c601c1480c4031391082d01a0003804804401010345d141c1c44101c60181112a00c034507070300c1d6960351440c922580040c20643d0300e40104c200b800000e41c0103000312421650b4994600600001103401c020340a48050040b07020781c3d0742000030510710400076014500c13480c0c490f281407050b1030b2441c40c0a88100340440003125800c401403814070010703103145415040707541c00018008405d100c01d0f010a00401083c1c0180e035100800d2034030303966030303d0740018030602060318020f01ca87c0e5260742c0121641c4c0d400042c015140403c1d07610300140702e0704812500810300140c2c00c8030b000c21500c4031500440d080a81d18041540061600d6105100b0310004101c0005042007040c0c8000001e25401c100414600070343c2c0280c004004001000300301684a107114164500d1000d00030006400d03d585050000c103170041c40517001d07004910000a03940010320460400f01d80180e01140c40c111540d4080703 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 309833480 1250 309832230 309832253
    0x905090114030a1211061303051207050903070e151206010302040b06041a040f06020d0206070e03100524010c0305030a0507140a020106081009080409050a020909090601060e0418 78
    0x1034043c070070f00c0c0d201c0300415210184603040f012a82c031540490602d20b03c01c603041c00c00c010403e01921210440c0c840000354003004070f0340008140c0e0f13681100c03515180c0d805c0321180700b0301400315810701c2407100201e101d051a030039090040700da01103c2101c9188440a009240b00038160744042034010800400250030203030480400b40307030004d010314605901c90300c50081b60f5810300086820745002040a0080308402074083c00988954002001c1c0c1c1000920001c2d903c0000510b0101001000791000809480c100400c0c00c0c04102400c0520940c505207080408900c0002610000003001185140c0c442d4000c0d0718414503907425944103850750380d0b248a80e03006008090240000c1110181034031840001d42005450361003255400410880d1801781200c0c0340680d8002c646140c0c0d85042140d07000194a01c1c11941140c0301004041440e030381e96102c00d00280600000c203a0051040403c2200300782d000301713205043e135110b61a505002d403140400c0c081200c150201204030b48841d4882c000c00b00b89200010b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 309834730 1250 309833480 309833519
    0x118050c130b0604090204090b0409050a12050c0d03020915030105010210230f07020601230d080c0d02030c0f0102130e041103010c0f1b0b0403140403020a03111009050901 75
    0x205000c0400c00c041029130b0311030f9110b003101c80e40c0464244410002c0740141402250103ca080c072201200b40c9900d501d680c250704008129014000c6128040c90041c015501000341034000e840f1760402201c0c1c080e010b075210391a00d900c2801c0c1251a142400c02c25029a81611010303030043c104074000c90001c20081448040b120a20f802e840d1450707000c440020242c0e4401c0e11180c21070101410328140180c541a010303004000c0c01c00c10f400000c4034451402e0442241c000c004ca0f118862052141801e603454850103501c92a035018103000414181e030004010040348800c8401c96580e5158841c0031801c0b40605542d50f00e219119103000c000601c04403182c0c5402a00800d094054001a940082d0864a00b0501360000c2408008544861500050140d2014000560070f61507040c00740c3e1140c00d0080001c0c8000c00b80001185001d40c0030080200b51009540d0141c1481440d640724140881d0080441480a10460340a400043c42034030604e00d5404035580941600708036401d0002400301c90104410 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 309835980 1250 309834730 309834769
    0x160303090204050709091802013515011403010e16030b031f06050f090609130b07030501090b03010e0c010503150607060b151c050612030703020f0118050c 68
    0xc40002681d5203110b910f01910813074507540c07995850070446030f066500456090040301d00f51003001001d44d8020f03100f00a80095000142920004044074684407884040380500240020b03042140c40c9180d2419409904400d0b02c601503980210708030002c41d032200740101c0d031a1500260124803000f0501c90312042c408410306010840f821712201003407505c6900c0e4600102113403611050201d180c01071140360090101130314840c1418040307101107948610003400c010300480101000a010111160700802c902ea400000041c803030800300d1009025060a01030690582d280130041d4010b4641403140e143c02d681d1900145c81e110300e80000542c0d03d504020403003604030000b80042e407119a83c090080260a11924000401c202a041400740000e40d842d007201101400300510540c2125000003e16441304410300072500d955482e010400a483c031030540d031080d100c00304903641090b402040e480010081c0314008c10030381028000d529441a0b03c400c0207445900600a40e074070780d0038621151983c1601046 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 309837230 1250 309835980 309835991
    0x171e0d110a090512070f051207030c080a0b06040504120f020c1002160509222103241a090a2c071d040b13020307091e030503160303 58
    0x203525880030354214009a80c408060143e03180a6400801862400c40206111414044070b10b1410100303018203441020b106d0324100c9010020090140030315400728100382601e0707454264558604105000300d849170650000608107044c10700c01d80d8459a00300d841c200c90554000340554505007083c216500b14014a5030800450700da2000030006000c8543c020074807055000c01030311201c0303400d4111601c05c61919041c002c06032180b03581d2210a81e0030311a0112062014038003d443c034080d00c580082030803558240100c515803d50701c8509042c002d4400010b000d44040820154003000f03004424030012460610315640ca414001381030000d0000e00038420b8640c4400d00c44403684010108469861120340c046000508400d01094000008d81401c241c10141c10405c04203c5200b20071180c0610790b02e00d0903940507961070303050902e080c1c401d181c21541d030b0614610007000c0704160b0003140300c0401405050540c01900940b0300040325000005142822a11040c0c803e5408907484243e00701600e9a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 309838480 1250 309837230 309837251
    0x150d09050d0c060501080c03030f0a020307020910081504032c03030301080303040309210602070303021c0b2701060c050f010e01020a03050601030c09050f06070618171e0d 75
    0x801088070300a03400d8851408040381803070200c0039210144c002080f550440c804525441c0c900100b0b13105840d421140d900e4481c07024000891850107042070107035100030420f007440606441d48120300f00340c49151040d54a05120035484480043e429540100001c8125801d5608512078040d80d900d00f549241d02200f0018982c0d0019140d500300703811468044c1c100000b448101600301013050010148001c071400b98000c20004589100600400500500e4001805d54109032003070b8100c2d2140b8072900d401e80f0480798442a900000c1060109050007150412040c1c042c0212662080d04155210961b0852580c00c0ca00101c49800083d60110303081d1082e946000800e09080c018040d522074610001610b1303900301d0000400741c58010701502d0606291141300034400d544101c00c0d90aa48055403050903413851000402c0c95881490300241c1001c0c5403200303002950312040e0201e0800741c0038120313000c100c450030042c0e10082c0c8210758816000d801860003c1402000d90006002d1102c61004c001500e500c49 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 309839730 1250 309838480 309838483
    0x515061605030409270512130915060206010f0b0f09030f030c060412050f071b05040f0f052523031503120301080c151605150f06150d0905 61
    0x258005152540c0c0f0380241c04100304284001700d0355200e0591503100c0d05038803921100c1c0c40e00c017005c1d400102c0e00000205000400741245040c0700520290a0410020a403940c102d8460105801b8101c01802842d00004071a84142a00810742e1140c412840c54202100409051540f10149054150241303100c3d00700030003000e00c05815071092020142c0614a05031524403c0c1c10740a510310002c1c000c0601801c0107d21844c0260f80c480c1c0e50049038070381c0c00710744641c0da191700c0c41240d800345920030304000c121089428142c2212081c85145403040c4000d841740d8565002e0000b4402c0d003480031441e100111070800703100740501000980210340d200280e51503407400005070303402180c04002e04080001d020b01107040030000c1110383c0400180d01c40c159410301c1141d90710351412000c41440788403c0480300e02a0050881144e811151554400305072245c0c514007140c8032801605030074002e5003002c000881c0301d2020540f02c0d104501c010b01024644a08480344442c90b00080b6081300920340e03c000b0079001400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 309840980 1250 309839730 309839737
    0xc0806040f05060a0c080f06180709060e100c3e01021b0f0f37060e030a0807080d050a020c014b0501061206050301051506160503 57
    0x207840c90764164621420280c1c41d21030050a1110410702e00f6401d181e0703990b88402c1d0355800c50b4000d0142c456a45a007230010703002083c5940007058080710311051007000381d0007030701d58411108292950040c0c000b1102c100540e984111071030741e000c80d905540b240300144181c1500a2039090301000c01a504910f603500118103001d041401c2c0040c0e01024004000c4d41e010407110700f801c1046200750a882011402151050007003d0700580100b01022219510b81d1b242c0c0103c10480c0210780c0200b030005001744d05030306046207049400c040401c4060707020442c14420003104d65211340240003000d00840c1a901c031841e0b503100317410a403000503042c001c07030049182c00d000741805502e883c0000368442001000c02801c407080206c0010b443c50b441d080080d0b25030001100c180954102c405010300c500d184001a503240c070803c942020241c0d18100012641540001541d502008203400412a0603110030034035080303520950300c130b814400d82c200f824231507498060000c1c40401c90601d521b0958400580d1500d10b50380 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 309842230 1250 309840980 309840983
    0x7091104080105130218131211060f0a0608030703050f0a0c05030a11010c0c05070902030619080105040308060d1a060102010f0e060a0e0a020d03050304030216030b1803040b0f070c080604 82
    0x400e240ca011041d0705d004500e08500300c030406d880c200030741024080008000c82d0346d40d00900d0600c0b200e6180350090301034032003c80c1d42c0900d042520360030701d026485146a02d60845180011510703281d80400d071110300005486203554580c403001c0c5098918010507095401034004d0104018442d204200050b4042c00a80903180d000d46401005c0488041310500b52003200e030b455800c000e0b02944203008286d00117441c80803a02c1c84440140e40340c0361100422031401ca0f034040443e500300c0d070410000da00001540101c0c400c9010b0382d24205551505c00400c00304420569010f03110040d0000c0c50008100c80d0100310b034210350140000252103117105520760a446056038090026000303042086540101402601c6046020802030500085aa4000307036080c040c20a0140030000080006000c1500810030484a10f00701012032074a140d888c0341034540c841c1e003141d0b40e60025940c100e0702c10319000f0020944042d103110041407824030b410390740d81f1021604040c0c001e0b074040e80319400004403c030046c041a0f0156 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 309843480 1250 309842230 309842251
    0x304050d1e1728020a08090406030204050112050c1009050907020708011a090a020406020a030f051e0901030b1801050f150a200601181a181807050307091104080105 72
    0x108084100d4a110104101d400c0448090020380050f0107640402c101030350b0303903000320b4041e201e08044020900402c030980001390458941000805d141c003600c00b800c1e0038944030344203d81a1200001c14441c01d6881000b482c00491081b5005011502e4030380b04241d4007505603c11290324a985544590950f56524607000030400f00072240b020074189800d1b038580c405002102546040d00d0000001c1d500e5400710005002c11020881c826081c0b03120f0000c03155039003031148038a14000f0610204889039801603c4443c080307490141413007800d003000400302445045010440072260721782401d1041c02ca40c0c1208181e40010740130070069001814101400070501c1d140e0315056600403803212a160310840407010003155226100402c0310450f13601c0d110f460100d10540c04954a1095820500301089581d505a030000d0850758442aa50300c000400d0700c1009001480e01600003003d046035190661400713007036050b0300f041c4814010108550440443c64021005440c5040c1d500c5094030300711102680c229511 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 309844730 1250 309843480 309843487
    0xd0f0605011406041511071509060f08040b0402220218210c010f050d020703030c0810030305090d050304080a0503070b181b030106080a03030b10020304050d1e17 71
    0x241c0345040c0103400340e050070703102540f4013410880000070242c4030b601c940c404c100c00042c03401b40c600414440f2800034442000038000010310420301030b0180d02d00b800b0720700020300a45c511040c26407152011740c0c01541c0012944d40d90b5210f036000e22500e00c0b40362845111980ca611005880c04441d0320051006182c142003007600350b030f414000c00041c051041a80314501c40d1542c44440030b2100490903000d01002420440b2950b808820169164054140500b920510129501c0141b40c0c042e0403d0007041c00136030f98023090b55640580041540518000a0002102482a21f803541022000b001007540a01c08032820680c0e19614945440c07002d10044900e9000400c00070200301c0714151040d000710300700c0e4030601703608044008140c0d90305915041c0c0b44c2d0389021900100854400798804c0c0090040e00082d2034a1070640e04015001e0644120003501a000f44800120381d030744080261000d03240b0007031808104000c15211200142d0041803210500c4640c0041d843c00141c40c1c2142c0c0090344112a4450b88 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 309845980 1250 309844730 309844739
    0x20309010b040b0306011e0f03050313080106060f03050c09060304050f0c010309170a0309120509031b22020c06040308070806090106020618030f04080c0310060509040f020d0f060501 80
    0x958101c160114040d904043c1070203510358000c64405c0c1994145191a50f200c404511903c03084a12503205420b100b005160100501201200038503e510401c4084001140e403006231038200d8425200e4200018100d07158242e095110b5007100b9040403a000c030040c01d1011040c0081c144e9882a03401711219400345c102c0802e900d00c107108502840702d0900381009003460540301c0351012403811203c1c0e0300d00040041c449030407074004e600c4251400e4000d800d2103143c0d030310360001414036804005198071911550b80a02101e8010083c01041d41a016126034170380a9151104166600300e601c040c2142d54090095001840d0100318244c401e0740681c3d18489070b0f003810780010b820040003030b051714000c2011100500c0500d0300001c0003600b007108613081e00481070729042c07034078214007820300200e030200000580054003100000e403000300084210160b81d110005c1c0445001115414401c440d0004a070000080100d58900c0140100d00d0000c0c006000c140050750f503425003150380e92030440300c443e6611700502 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 309847230 1250 309845980 309845983
    0x904060e0601121b05031e0414160815040f12091a070b0c03150411030108121c020a11100f0b15160c030b010b070b06060415030c2001020309 62
    0x140000002e081000d00810035041e80e994415501c4c142c00e024000021604240511010480202080484202d40c2c100b03480c0c08440c609040c48050003600c240f500043c800056005140221001d450080c03010005464201994850041c01604c076113112451032000b1a02414800c50401030303e60b40c100140d070400e0006c0880340400c0700000400c00081c400000098401c510190700710803520038080d165514144800c80d09511401241d40050a020300c0d100603440c2840610305075003201e425614085090311018801e40520361012407162005c42c3c8a01c181038640c2d0080c80080c6661404102e00d502941406140841a00c00c01e1820360fa90118082413420398880e074481d0200c100d50070701050081d80b118200e00d001d0000c001c91440340b141c0e40c0d5000c0100e02c1040b00d00465111141c44d01560b51801d421403d604050010384c0c0d104152030018409240c0101250107071f4820f0f00620380c0c504072001040f001416040c0081041c00781c0a01503001ba503201440003901a4000400941d40c1d04d044024203 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 309848480 1250 309847230 309847247
    0x103050705090c040b09190504020427050420011206081c08130305090a03020d03020f01061505220f08010605130c08010e04050c090a020d0506121f020904060e0601 72
    0x900c3d0303284188020b2090310750290444460b20300440d02070800003003264004d01e9012140e40120392040c030000740003515806021080050041011844128000c0c07412440c0a030f5100711070050840518683d40120300c00c0303c002c081071a03841850005a0301d02910b04a404640c0e880c0c1106290391302601a011100711801100d1001340100d1411841c10b00f071a82004a1080050300b00405112010499154035102d180c1943c005680050015007113120038240a0b440d0f002e640003e04040d400c00101056400000b980c2c001d2060083d84e0f0980f422100c05036004500b0f54041d140409081e00050000385079901c81e8424000d44141400003842e1840e180400142805000d018119070741020304403070b5080d81040b49241100c0d881e11038401c03a9961881d14a091004101000398801d907940e01344071070f0008981c003a01d4003c0c6200c40070401d42d100c4104002015280c42070f0034507184d118401d40c401442909001300010092040c002d810f140907003000501780c0c2c1c02500170705020800310080109071360340712814 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 309849730 1250 309848480 309848491
    0xc031605100e070909050a1e2003060105060307110706021e06010f030609030c0f0b040c080118020f19120c0608010605091e09040507030308010b16060c050c06010305070509 76
    0xc10030441d1030781c40b541d140c61151240048455403903148605102c828000300b080c0302d074441741c0807080c0d4040c40064880c0300590203041c0c0c1d034100105504c03403025a1035404030401402c000c0c02422942c0c078110820100754002403a807020480c2c040e55800c500702040045101614840c0c001d00740c0780b601c281d1203924105607407249850796400340004100c03108841c01324030b05494014501048500f4139050035511418046402086011822001014011181186801240304519684a0b542d50f55a81800e84019074581510f0140f050b503000c0052400388a03101b0501005000000c0c0c4191000c441e110141f907540c004145032030b00030014001c212114226001030811070038038407001d5043c208000c0182c021540698020040d04039981c00414603448040303200c400090140485160625040b070700e400d09880103c01007910100049480d8031602d0540d0074a1000029095209034141c540401a04c080d10300e60040c090100003001c4100014480d40d8081c5010b50018146645032100740500084018075 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 309850980 1250 309849730 309849763
    0x91b080606100e060f040b0a0207090c050c031b0c040c08100501020a170d1803030b01030f022517070b1b03040305030403030f1e0917030402061603050c031605 70
    0xb9011036402c90700f003042e007030002d82d0240e88619807403040300594416500618000f440208030074281980c002000002d45038044024024107400810556a5000d1214200025081840b80003082c880b004814103e000900045810002c500307404142103c621042030350025000800304601d00c0c0040c001c90300140000c0c4018014449582c451030064943d0b22400d580680001481c090036800b0360300100e00322541a00304800c01e62a62802900070480310401d240440d040003000d24002100c1d200342c034444808007003c07070051078503003150443c1054940703021141105217111142c0d003004000050104688a4201203c49007450504040705050080e0404890381c0d04000f0400001da201c420740350840e9140c1008900018828940c001400c0702e5000c0725a0783c40c41d0000150248425041500c0b25802030102c040c00e000012300f401600d100466001c1e4001d8010031052031030202c00b480b000c0b0010b000346412070500d03180307105003821640a0079515020080825514091100a000c01600c0f2030715200c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 309852230 1250 309850980 309850999
    0x2011d07140d050c100801030620180103110a030b1302030403020a020603180a0606090c1d010c081e0409060510020a330507020d02070806060d06091b080606 69
    0x415490055180d100440c024082c194502c42006000c0040d8045030300001d2841000e00195140100440824801a181c041c02d003007182d40548140001d55840b641c501d10003d281501a0381c44d0211014068075443c10036a40303202840940c8440c0000d04041130003558041501002841007014001c41407421040300d610400620001a400240d072100469064440a4603560782c880c0c21064440441d221070002e014180c00d003801c022641d405481518550102004044049101141e00201d0281e030316404400b0b0b0004102c8075802401c1100016102d19803e82c64407a540088041c043e41444010300d40c01c1c0c002c01c041c0442580c0d8040c44d03002d0081500c4113140c0700c11891000b50398110080300501000440341c8501c6060780699480108141c80280382c4c0303d02842d0104400003064101e036044018050184401010341c0701161900850b140c01008205540700e0504100c20443c0180c0104c4480e40e0b54040d1000062004048942e8184004544140103261240e042e040c01b8000309012b11600101 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 309853480 1250 309852230 309852239
    0x5120708060a11040e07080a1a0603040b100503030d0209030601060e0913020a051504030b060111060117190f030e04110f07050a230f060c0a050a1e02011d07 69
    0x6540e80c0d2000c204540401e0040c41c8003196032442c13040e6000020010502c808200b0b41d980c214003658041c3c0100c1800700040700031550f6001850f446055902da02c032100700702180105070080c2150740c010640c0d19400040030f41e1000000e1851740f004c0564503072603402003203c2d0354518050003a240140451306013181403e0b16200010906d04004006041e0441d554101105640343c0720400d0707002e014003803d1003003ca8070103890750303109405c00d100403610600003600040d065482000120f00c0503510300002c0a9990a0040808010480d01c00311401840f941c407100050710303050f209114545015482d10364070007c850400403e004480240300b40214145403030304c40814036084c00c40d150900030b1965030340c85108a06c1c1c544d0615107035100c043d285600e203e4200600d071000310780d07110641041c402100d00c48000b00040d2034845400301c40758400e210b428880d9031503290054000307101c044080c0ca0316400048642400301c03040030303820340e8140042c0c0d9a4514050107442545c08001e41303030352120080c40a05c6c500f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 309854730 1250 309853480 309853483
    0x50619120c06091a1803010f020c120703020a02131b08010801180203070b2a0d0801090b010203071205280f0507020a061b0501020c0604032a02011110020c030405120708 74
    0x10390520341041000403205c01c182c80c8040b2401c0342e4030300140207005102c01d988020b400394100c01c03401d00300c6004105100c441c0f0303407002e021a04141da0540203000700a5907034081108445486050580c0c140c0c803095007420740b1441c0d202d160402c075643e0301c0b10f140300c1d41001c0d80b142c21200840b129000035400c00b00c040001d0703980042c8000413a0260581c1c5a65a840703074083d9001d141d04108800c00d1000440051145c00501261328600074400d5a03801d44582c3e03840c0201d1080e81d6111408a01503041041464082059165114410726107410514604480c0c50282d18000c0a202042c04242e2040040b1407060f66000c619064912b4407890005d042048a80001d0303a0034031240f20b46000d0042e07920340d2001c15595110034403501600718000315210300d2840d000c01d8540004403403c400107044140314014094555070b40e8003001040d88803c101c1c4a04683c0156004141d1000710509441052a50b8912a030705000401020034208095a150352a01c010301c410031604244036030480c2c1020209201c1d6440 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 309855980 1250 309854730 309854759
    0x20105070f0c030825240209040e0309120a0f060506040e0d0c0516050a0e07030e030a0306290d0c1b0501061a031b0319050c030f060a0513050619120c0609 68
    0x16044403040b100b149001340c2c0c06c002c0c4a240013007500b00e0f0070310a007a1540350012026000700d03902074618100324a401ca090640b01c3d6140c0030010b0004450382d01c05c1020030525440b00b944000c000d0b1001510840c60302549140c0003402115200150004018104116080c000009001c01d40442078515908100010b003581070180940044d00ca8108009054a4484d8005c503a0168151080d41d5555082030b1006000d001c40d1b005d604030020406980b60340c2c6040c189165494410b41840d803909041c00f217071000000d011702d0141582049180520814146d28600808a001c0c1c171a100001e242842c041c0400001d0403600409a5000d4050040003505240d0981d0301050405010315507541350f540e0140c810703241048107520354405140404205458460100840c01161050781c00c9180d9620241040340440b0360b400313005c0d04420300e90510540c00072183c1000d508a14000c00794200980681200304580e05c040d8400e1118082d0010020240050744102c98080c11844c500f100b40b40e0309010080d44080d8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 309857230 1250 309855980 309856013
    0x130501180203101703070c0b0301063609150506030f01030209130602030c1b0715030c09030203060c0901080a02160f0201020313080606031504020904020105070f0c030825 75
    0x350000000f410030281c8001c0e0801805500e00c070101607142c025405a580d41141c4c01c00c85243c22800008110300e10b005068038121580303591501c550007904180c507514000d11840c0c5850f03107400005402c211182e80e4a40070b0140061000000c2e0940d44800090b80d04101603100c40d009000410070710400e1200180202d054a4041c0c5104125807038405684122103072521015050031f2020042c0b000c1668841d000f0039075803074190384a80c8025426190661074000901c0351544006403c103113159500c0c080c0e0801d40a504144c206400002e60f01c1d00428140b00c4101c0f503a800103000081c80350072960b0803d440f5600f054030440114207041501e9900304640854400c040c1901040800b1082168801c02c110351007040d14203040e45680d656114460ba50341c80654420303110b8090340c5040d00559001c08110391050b9001011b00c1070035121030300103541c554030098041d1162079070312105602181c511a4918019440390038081d03500d00b2110389000b10407109442b0706400e0200c0d2800750010070340035042e260301031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 309858480 1250 309857230 309857279
    0x60e0a05210d080105010f021903030b0303071b0e0f010f06031a0d0b220b0f040c0302090405030304020a0b07030e0906010905030f0f102708070209040809130501 71
    0x40d050000007042594a01041c45080e00c1030702008001c940c1d11124060407100d007070300c6100d281d4101d0a0f09036241c48062004010543c000458240403c1c82500141d401d45070260a5a18107203281e100d041101e65208044420313021032688c00c000c0d6650000e07a05034860088081500b11f54104003500d101041e0700d00c906004c01d615220481c64417685440350580e00e01009141c219482c81e030346800c038440e40b412501d07024042103640c011440c040e20050715006487c2c0c0400300c4c0300383c0ea69000c2c0c0301c1d90494002c0c0c07054581d1034048101000680303c092a26000b01c3c0294000d5403a454603204004442c40385401205009000b48080c40010340c1203004110341c004200ca2540e1a503a641e40125003070b2085a22099161252040314076000c0e401082c001c4844c0c460200342c8103140700304050391066407a0810441d00e04c00c03130312480755480540d480c50054203900c85c216103841c146260300054643d41c81070320103448840b40007501d600203180592001002041151080c0003961412a02800e40f041d06205842c50 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 309859730 1250 309858480 309858499
    0x50901020c13050405010506061903050c090a0602060a0c0504060807031a1c060b03030a090509100306020f030703200f0702030a0b13030807021b040e16090c0306060e0a05 75
    0x580c001d0114081c1076101505481001c803481c0780860250800f514180d80a51905c2c000c900603081800440c1d4038842104400b01214850140803030040c0002040300100c1002800004825901e03e600d40c1d00820071a8010640e40c1081080712003110f88100259003403000410080104139048200e20b03a02485908000a14070b080e2050502150072141400d944422001c409865084c24482c1021241e40204810841e6005000c1810b03902d1049511f5840407440442d0200310500d0194012580461142c1c0c2e14451a6078980d90201603803c080c81d01c1a00c400003100b0000443d90610503620f00161140e0403201138151104008442d00c20142e000c4042240040c21a003035442c104803e41145911542c041c0072880e107881e80100284a0701400c500107125a40410201c51000030007400c0180742c0068000f114114008010050031041e007240e0042c002c00c4440d55148a600d526240103020040c004521582e42e08002030481d4119045202403040703044200e11151102044801070310000d8500bc2c51 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 309860980 1250 309859730 309859747
    0x71a01080d03240b0a0201060b0306031905030d1503110303070b0105040c050f030a0614030604050d18032001031d030306040f0b0d0309031101080c0a0806150a030e070e0c0a05 77
    0x85154a8030083c5484014070390016010342c4060050145441c10390080042c15103407102c0c00c0d541c0c0700079a8040d0f407692040000104054903401407040b020b116004076490421410705d100f040e0f03001155000072128000c3c2003007090104080b00c544498500318083c51408060780c2d5450b02c2d0b41f10600440380030b50f94032906808194020740c100c0714524059010942c4915225080901602460182e45410701088203c8d01440c180061918000c50341f02c8098400c01240c100201c0d09440e440b00080341c0a225000000b002c201c1a050b040c1c82800140031020006102000250a9401400143c0b407030244031000d80403041408016203821020440c2e000c20781c80c4540b6507140142c2070130401c196219099000c003008154102c2c2200c02107078804e42c4054055441f0400558005d00112204e480d1510100030b4a48900d00c1011030a034802e1000f00750742201c05246292080a03081940c07000046562059076a5a011007005008003c041280b4515081c1c644028216541d00402d8100002c5c000d01160f64207 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 309862230 1250 309860980 309861011
    0x9030c170906040801021b0a170d15030302010b03061f03110d050f060405010f0606200a0b0a0c0306150504061d0d200a1a0a0c17071a01080d03 63
    0x10181c0200425058990f502c894401d8001d40c020a00403040b0140c028a021132590007042d0800010b8020030014840940c2e08064100d0358020001d21515696a11044069249024a04000d98066400000da0042e220241843c050006d003415072902d40f01030b0344409400d0703c64900c0c400d90342d100c01e82442441850011a220f180d050740014410701030b4034041d15a4100000320301d84514081c2c4028407030b0504424402080302d100d8010800090008502c040449190303160080c4101c2e40b18080f510ba66040f41c0701c102c114a802d036070003403855440f07440c42c5110950601646000d0007026032440241c00b0202005007007882036114610502c0f00d0380304842503488200c254080030140c050031600c1029094a4008083c90b860491003603a0015000b0b0b0b218982006201c280c259015680700a242451508204180e80c1100040300d0030820704202c1000014a0760020000f050400004980ca420131403919808200300c02d0300034100e400d2440010049858009110320802000b82000103035444600c24a6 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 309863480 1250 309862230 309862237
    0x60c0f02030a0302010e060f070806010c08070203061f05040e031b15040804150806010c08091c080d050c03040b15040e0f060a060b132d0b030708060409030c17 70
    0xe9414054440007105254064208040b20340c81c02065504aa4035880e206e40d2180056640e1030000320a80300141803540914000c500d00c40c082c00c1c40c603040250540c0000d2a00204880b400083d6000400c0c10861380c0c0c0d42480c1c0406007000711030074448180411442c0703580e4028078007a080c032420304440c202c0c1881341c02c1c4007c404901103040a00c09034500350501c0456540148200240410040418141c040c402c3e17034124002d8505a480c0400040207450300e14290b0040d0000a80c0600405c0304c16080d070900a0701c19040b18801e440c0e86480710000c0c6030503011a6401010381107a19420402c0000048509140e50703407000380c0c450900c080e6100d40380818020a0035042241140c800e070f41542e00c40c4400080c45a102c1c1c0c00d003a030b080c06455204c3c41040c0d01130007500f035100001c2900d071740207101c40d40d456010500008504148907a0107156004c96481d82116513100c100c42c00e1000050004041e070103544a42e01800c01c6d60280041c14030340e5801064038540c1c0300082d1101c1800c0100d40f0b003a0818204a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 309864730 1250 309863480 309863483
    0x3090f0d05030406031e06150807030e030412061404080706020315090a0b0a060f0c0303091106041805130309030212010b100909240612060f0f15110601060c0f 70
    0x100e0f40c07201c2e10f0366400780082c4090300d409044200644034110442d101c0707001d00b005542d00d0038041c071240710300300e0301c107442a0f000030307100005040d00d515140c105030030200043c2c40105564500b440500285007491021190b10001e0105420358820422000c1160381040310340c1d49610680c0180d403130b40c0d00c6001d91072600d0050b890940c02902d000c1404900074664000c5e000c4610102c0c0c400f107003030355500b1099640403450f40034400420040c5084131f01080c003a61001d00d0ba40d0080c42035030030881c51140081c031154481c0d00180201c0c110580c20340707040412445903d9000b84c0da03640482c5030000a0b207018200e0300c05440001e100702040d0000031100c1c1029000306014400140103032441078013100015010070024081c0b00c0c801072502c44942c4084295030110291032801c4403264150300c0c100b00007140c0c41c060307031000d0240c0d494540100040500201003604002c00c140c1827030051079424031000b000e0340384002481c0b404021414260300204400860355038110b442c2418000d11000503450600001d0084160 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 309865980 1250 309864730 309864733
    0x6120c0307030605041a0912090d060c0f0206100b1e120109020301051306051e0307270c0c03120509120f091206070c0f0c05032a010e010203090f0d05 66
    0x40042000007980081703005030710a40c00092011312a51490b500714408403442d45155020200d240ba10005d500020b14902101402e800280300103038446405840034010780100042c6c0800100207403035414410290407004e081c50007425540380501403030190080c0080040c40340917003850840180c00c000200c8031580200c0c0c2807180c2c85d6a5400000009410900ca038901418908041080101962241206076080104800c0030080c1b45030400c40400c50a91b0307501d8052080c50f1004c074405020011803880d0b0940d0800800c58a1f40099155080e9890034148500f0f00201c0b00381e001c0080d8002d0701d001148100d80e0000a0940c0e20315820a1408042004441d81043c000501e11384068582c00184032a000c1581c0c0c000c407500c45168043e58901c0100ea5560000e240c05c0c00e002e002812000710082e0690050b10403001d00c68407440024240640401d6484046880704224002e85d1401010700390814400d0034500c00c10080140040e41301e10030310314050310071100f200c00d191081d5143c104501000e50480d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 309867230 1250 309865980 309865993
    0x30c0c0f011a030f03030a09060b03031b010b0108060d060903030f150305010c020c010c0b060112110309060f090d0e2404090f06030c03060c140a2006010e06120c03 72
    0xca101e0080101454018420300d495a00c403401e07040018100a03400b40785801180f559482c0b84600009000204007260500d40f1072580041c0c1e6903041001e0030003002c0b44500c1c0e4900f150108003850842e0906501c6505100c0c1140c1000055600c0d45001800e90307401c10b00105500c01649002ca00501640390602140340c5003d50380d0480c58502c5469030b007581d118200030006001a440d081c0c1c0d41d2020b00070054001000564900c00181d000070702c1382c1d04070006040c10004440f002c003505e015100303801291000a8008010010300032001c0082d540c121900c0324880b101810310f510402e440b0500c40f8050414440f44003e041150380f96040c03944c40c001c41c0d5000708a81c0000d06d07446c440840c1c2c4a44603010340e540c01d04034002c1c2040c0c1c152044e6400c90394402c0111300c4c81844c0d651510060480c2103a041c0500400301106c03510b54080e10014128180c465880843c105018480c489503041141d100c000c060380031800500001c9040401e954101c01c08540c0c260801040340403062925854400c0740750140140c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 309868480 1250 309867230 309867253
    0x3120f0c05190c080105012d03020a12120c050c040c0216030302071703160311010207141c0c050a1e05030a03060905240f01030f05090615010804050c0105030c0c 71
    0x10b01c03140c84070b900c10030aa100d010f0744c9109040c2030725400e015000903400403080500200d0301c070941c201f003100c618032900c00c8a15030f40c0e00083d001400e1075100407103d82e01c06a40c80c0c10001b1000c042000350126043c40050741d10300e92a801d039200515640280140d030b40380364840380c0f14002c00001c017000e40a01c40144500740c503450000c0d1941003d00c110b00c005040c4207180540e034003012080d1090003074420013100d200c00068034100c1e14164441640c0889540c02c01880c2d01203124100b191005070941401445d014000c622a0200022851040340401403141c55940005001158144140d500078840781c0d1001400c0ca08022034a640c050014003601c000101c3d0402690035422050444081c0c43e410041da5440c804480c0031a00381400c80d405010b1403418440c910f1070484d00c100300c1240180350004405804120b1030b01260740076101d50345113a0080d82000010148071103107440c03985081c60140c2e100d0900790b4402d40d8031403504e0b100a06101c00440051462040c600a480310801d0010851381c0c0d2071810b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 309869730 1250 309868480 309868513
    0x8010506090a2d120f29240409110f0301180f020a0b040e04231203090c010903020307090f090609031116080312060d0516090e0703120f0c05 62
    0x30042c00f045181201030001010142c00c000d030281d4070380190082811030f80543d0340170803113511003072890740d446801c4034103101c15001c00c3c1d00c035403103820900d080e941030704640004120b07202480c0680500c91410729000d4000242c4a9030314580300c0b0790941d1510014613034440041c2c0034040945404e000c0c0c0c07046000c3c10007804100c0644a00090082d81e0a07c0303040d80302c2c0c000300e84a1007540149034030401e14001060010711118203030f200c1c039459003002c954640100802d081c00c04800390100383c1c90b114040140030041009010100301d58009007000d80c6150b01d55030100381c42d1b2070b0902c102c6c80120f0780d40d0004e0b81203001642100400d1a407048003004034100918001e89103030b4100c56568072510450f013542c0c801c1c0000c0e51010003074400d40360046003040f0410b1901050f480d40100410780281d0f000c0d40b00c4001800400410100c0e0703841c0000124a14189600c802c00c5580000e54507185900150301080400c02030883d4244030485031404490301d81400740c0c20b461202c00110002d03c544208002c00694407038 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 309870980 1250 309869730 309869789
    0x70b0a080a050f04020f0d0f080c150604060f1701060b0712030b19120203240f070e0a060804020616030e040e0303090d051b0607090303030b090708010506090a 70
    0x20490010460b680319041c8210348003c048800030740000f1510703c001401e00d80000c40380309082c400e24803440842c000e5070b5010401d4229112403c076a43c84981d070214940966110580d200c48191400c10110346090f06101581d0382ca441103541c4071805603200700c0f0484081d0041d0b000761001da045642c3c0c03085149403c03142a01d41144040c0003901e06008140c451030035610800c42e2018090350034004a0500d28000034080408004070313890b124010740401c0705ca0000b02ca1144c003d80030b9001004602d00b02540102c0180000c010508100301180c60380220703a80c07461103e05031015807034445026619403001c50004e10441a510866107000c654042c2016440800c1d0941d11005076828444d01d101d000940c1e0740c90100382c51342c1e01d40f500403d4500e407071644100301400c0d190916500040002c100390340b98a040540a80300c0000051803501305205150b018040c0c0d046200f0700391955041c40c03a00300c100602c0c01074180200d610038800060241842c0d0b50b031110b524080c095850b141080e10f0102180e0002215 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 309872230 1250 309870980 309870991
    0xa02100e01090b04021c02130903020d09060518040b0409050105040519021f0216120201021905100504150f090c1d181c0f09090e0d0c05070b0a08 64
    0x50034100400300985040c040c030075000c0d0f800340b60072009884950030409040c41000700c00c0c1c41a0700041e041009aa04c550140141ea500824005409540d80c1002800d048019607040d040c06402181003001690040803900702c4c0705442148501c060016000030081c054290303030300d5130050a09181c50240304040d4010b50045200b4402c0750603014040b840c4c0400a200c20b00003943c0030b100001c28a82c400100d0400c180f10585510503110f0312009a256481c0865407030304196107002000c000c00d411540c041105c04d01c2c40c4446003691550b084030395501075a69042c22410300c13101c0e444001040400030803a0140449100d608002d10038108102050710003000016016504c0c1c059032403000501b98150b903030700740c000d008040d40c1d11034913507803403020601c4e211540b55101118401e80300e41c20740c4140311005d060185207840d510b0082103010ba0380e0050900c02e55801c40011640b812040d0340c2c41c504d001800c20340300c800504000803c4162400c040b0b0401d41194030519405000186170300790168010310161084 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 309873480 1250 309872230 309872263
    0x6030a020c0c031f0b0a09140403030e1506010f02160b0919050135040f12091514071a1008120403031103130b03100e04020f060705070b0a02 62
    0x544882019941c46902d10a5280080881404e1807898842d070010015180301a0482c0b5503166140a06000c880c07200030348201042052041c00704040d858020180d25040440082c0205580b808a6a00818000e000c0c1418083c8500d54011000d0081c0b00d001302034044e025004c02c000d50340d90b100b90b00c61342c0110011446009980550042c41480101080940d001a074914080e4110703404041b207203080038640c003240d082e0109291a8500c402d886004d02c150710950708408040d1081c6448112000e40c1100b07032044c010103c001303203c8541c0004480380f030f1449c685825002840035800e0300740c041c070450340003502d01e011065452500d4414a0740203401040f17180e6140701c495036503a4a45890b03110345031600051500410003000464850746084080075090380070303286448402529200c01908a5108000c005000710400851207003c4440e00028040c0c4c2000d90b1080c50154001280e01c035500003071501c0746101003012410f112003000000064032140101301d6a451052402035500c00c040461040c12 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 309874730 1250 309873480 309873493
    0xd12020706030e07030b0a050603031e0406170f04030509010302090301020d06150801180b010e06160303050604020f030103080c0309030d05093a060b040f060509010b19110c06030a020c 81
    0x41c0f6400103044070849810280040283d01d0b1f06a166014003405000d042d031600c0148618890141700c025590901280d41851755541ea15224019000000010050380302c5030400c01080000307460075907c00d903c03e92510b4442e90fa6a00d00300160f0080c043d800503960198804034203100100301da54050400e50f0f07100b00b20300621080c540c000b26005a000d000700d9100002e004051804031846070048040b0b5001418141400155200450b4080d041041e4a00c0c00300c1c403144000090603007520031a5000407007540d0561502d002c6031307240c00e05440103110081603460f001502c0c64081c0d10900644411540040684203a08821b490040a030b8000080161088201e41c2e011040c2c038007141c10030b0f501c03d446a845207620302000414900013500815064401c1a1100d0162030782d55602d1003854070050400c2c0d0002192428803060000e20765050300301c512001010044103a41d41030501c1e041102d41c0303883c0303011001c89502d070301c01e60b0518504104054014102009000c80e26103140c015020082046007218030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 309875980 1250 309874730 309874751
    0x10b040203040309060e03030904020703020129030a290403020f010e010606170601090807120501061e180b060403140d020105070f030e0c0d0503040e0f010302060306040b0d1202070603 81
    0x3203201c281c0c1e00902044903103104000072030181000e031145180c010241c030300745517400340414284c1c2d0040350201c0c0141d65400214154010900181c0644803107100c08505001014010958600c4495000342c0340a1107580d03010a41400350b0040914180c0307800c060745041c141403402a5480710050305550f030341d500701421352079414014860713081207400b03640c0e032913503100001c00044001074400780c091030411000306000b0522540412501740244401007800654102038102942103507078907044603152050042c807180745005841800001e407228201c0b400d0030910107402280040115103076481e08414007090002c14031400d0200c45540340c0b14201550040743d202e200072402c84e2421a440742c0403070715000d16254803d00c2075210250008944d0b08441c059514040011080011880212074682c00081c0620101504400054006130504910000303941940d0025207117000041c11180115075408a421803903407080f005541281d044014824840a28a0000c1d26041e903400750707101080c00e2100404 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 309877230 1250 309875980 309875989
    0x50d180f030f081b0c0c0405160e041103150a0320040506030d09090c050c070b0702150a0203090112091217060f2b080301060302041509150e060d0f0905010b 69
    0x910030600e0740420074a1540201c081a669008880541e466106d0b14904540310b4403948181d5004039207800204100f001c9040c0001d0200030032100c0980030350300788096032a4035650a020350740c0040c20442c05c04861040303400420001c00701a0f0014142c40851803c100076052082e4445102510582e014045941e6120034550389044c0741200500040e2404420040c1c400f141d0301414401c0194a8094600f2800d0711081d1310305142508907090000c030028000f0f0861422a2140c0705071101030103000e0500408070f601070346902407031802c9814001d19030641025003001e68041d101060b03004c1450003065007615402005440c041c074000604218100101c2c1d900c2c540850a1884128020000454004004011000b41c1c804280b102c0350260840403a60010b04154007660291002e654010303281c500d000640b800c08040c000e01c85080c40300b641405d000031101888a04411000340c1899a4a14030322000300b20584200d01c200806c591400c64004001c031001e400c20f03006140100020701000280f0820071 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 309878480 1250 309877230 309877247
    0x40c0903020108130212100509010b010f080f0405030403150e010e0c0a06050c1203091b150a0503041a01080705090a020a1e0201020c0102030f09190c06050d180f030f 73
    0x19000c6550f40307000131210800003281c520480d101601804100c200781042c0c41c64031401010000420f5150070420403496401d2081c0f104d03159003440d00d0314406d10b45c0640541401c0e405080703c4080015000003400f8460b040049034000c40e400040021075070101d410590042030070741c10380640e43d4240361160064000004c1e070304694240060400920038500b0b0410b680c1980440748203045400740044000218503443d010b144200001406014101d10005616581500e4103180600c40e2410720700108410130003d0a59199400d107003080c035030381d132610305040c0c210414150901000712000750001c142e826021403024100c076419140010540c9910424006034040c502c90f6200180c1c0803075120039441a0010390908000e1107000051030400852440d40c01d81c1e1080320510b150100344400e1082c4c1074001c0003007900403480c034440300028a40c0c0340d40e5200182024801c01003002400300e02c5054a00c810b07030004400911b40c031007818840416207800c03400c01440c10700035404282024215101d01d030084064 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 309879730 1250 309878480 309878483
    0xc05030607090b0d1d030a02010b190807090f0b0406170706050c0303040807140d05180909060402132307090b0703050405010f120e0604020306090c0915010203091905040c0903 77
    0xe03a0600b00001c103550004d1100e60701c0101150f02459112031000d1007030000b4041c0d1147c0307600210b6220a000140424000d20760020b541c040c8100030200460032010070f40c1c50a84101920125407410303c00c0c82d07032000d04141c24003241e200f40741c08400502e42002040e1589165041c0081d40c0000f690b945080c1e6240c02465410840b54004100281c0050914401010300500c1524001c84090a201c503a9150160070300f00036020407400a0340d040d200466500183ca0000219501021440c4c50b0359241d4075594054002801a4000341da045060710f000c2d042041c0041c82501024003592070b20781404141801500d102d400328586600204200c12a107040300ca5041d0151030f0146481d103020011a00200365040300000c008418511002c288018041c0100e42e40c6440d000f0412740c1841c3c01014104100070f40a042917074014280803210351240681550720800020584c40c0d440c50b0500141c2c11840340040c1c2c40e0f8008101d07a0138120125100c0700050a5400a440420070017143c0881615409101e020 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 309880980 1250 309879730 309879749
    0x70812011a070201170406022802150105030d08040503090607050307020909060618040309270e03040f03081809090a06051605030c0c1606030f0b0d1205031806040c0503060709 77
    0x18044170703100c255080394101d48254401840c0c203480c1ca040e480414034410640801a00c008501044158100640c1c1e0918005120034140d03945008002170360303460b0f03160098042c4444c4000007828040280b051740c0c0e5201c80030744a80d6a64060f8580ba80d00ca41c80303540d0407485403801c44007152011400041c110f00c50103010380070140140e9101c00400d0b000d80000d008504000240401240410425640008004420300403800110110726927405543d5000040c0100344d0040c8810017042c00001603503001c0ba600841900d5407120b80c0b83c045c0301180c5000040341e4105443c907090245401c400a128400c160054808000e10386403154481c0b05c80c000b94042038001803007400441d0b0621125001048003492020032540e41c00401208542c1c81ca0450b03000e80003081d81c40354000c1d805c600601503044a450f0403100e000080c01039070b880742070500003100120104400400050000c051750201e40d42c40c0d012410813140c40740341514001142c00c0703031130140c180039000302e40110741040d000b11544026940c50740c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 309882230 1250 309880980 309880997
    0x20702030d050c0304030f0b18060f0601030c09051009080d0809030d0c0c0210110f1903140706110a092711040e1608010605121506070812011a070201 66
    0x14044903543c22900c6104814041080004001010520803607d51489a42182014648062440001c1001200428140d000701c000c0010120482014581c49802401d00140b0f0040000d41185ca030511a00025000038070100e0b1000760941007050002101c10501c21108900781500040311010010750303030410541e00c1800000c071000400d030002c00090b0001d14101c0800034080c5c00045d015510300c5c1807640480c01c03903c4d0006003902c0c18401c511118058100400407001101b00a502c0b081c8140c1c000381c00c0101001e1a2040b044080c411580440e800c10010320a0850704001c002242d4007102a200100d1160440043c0c55600c44110041031000724910b0700420411940e40005403880311051403100900308408102c0c003000e00784881c003405400c0d0849100c40d40b55140a0140c0c041a0042014401c0600410001c000902c02150f400000180409680244140844c40c1809007520052030341d540403400c148084040300d6840e040380ca4001d038480e46810000c4c41c007030803031183c590040e000a6119 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 309883480 1250 309882230 309882253
    0xc030f0304140411071a1f030305030f100503060a0b0301060510080a1d0d12230103030f0309080a0503040204050a1a042a0f0f0305190e0708191502070203 68
    0x7980070000030b06182d0300b19490040940c0d1003100c910701401b0080a009825004e0105004000324170460800d141805140300c142035440291403400001d1110049401e02030024800080d1030f120207000703183c080c6c100c1c0c01c18280303952800040c8c0215540d6900940c40c0110000b01c2d458a00e02041c00350005441d14001380d21111400d402230030341c0c80b108001c0da6890b00b40b8804182420001c0006850840d620391042c070000800d04019900c104180c81c041c900c14100c1d035000540480c1d107460440307902d410b094210713205100b42617020700036120b400f03032020801081404e80503800034001e503c110b108403003c200d2903039a513000c18221003d9403142909164400400a404c0c00c1c943e11010425000c0c0c00303a1070305025815001e100b2800d01da181d40d00000d40f0000c010400f590010700583c0217110509043c0100d180100e070754a40b800380d050a505880340ca80032100c0f403001d024010310024002c1c1ca0203a510405001604216001ba0713560101c80040e034445138120b980c0030520a59040340d50080c060120311050 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 309884730 1250 309883480 309883489
    0x30f1806091a010b090906030a02100804060e1e010c0c110d24060807090b010c030c08070c0803030108070b070c0302090c04120b06130c02122a0c030f030414 69
    0xa10011900101c00000c429a040324403030744940213000540409a4030310300501407004003000546107074041d52103810080010ba44602910b2406001d525040035241d69504045024190985c034800d014014201d05081c42440085040b1021805000071300602e5a081d500300c0d80550502000b4040118030160100c2a140c00919121040c3c0034107498100101000c0c10381c0740300c410007946170703a20982d50501000400000d01c145401400005000c02c5600401e00020740203814ac40c50040c00c001d1894140c2d010019881c040d81c004541005000200d140c44071102c0f130b03a9500a024140182c03040100c001079079626001243d48655002c280c04c444545540e00340140d0000181100740c80f150140008a85c448620642c90f4400e401826076401a08204052216551011f06042c1c0003505004009003a6070300016160140c2201c911629512600380c0c01c43c0618480e601500c150f411766404020f0315500d800102c0f00030b000b1b0205c050711080880c446000c0e83d42e200301e2241015040c0300b281daa0340d20303103070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 309885980 1250 309884730 309884741
    0xb1002060a0f0e011b0f0203070b0a09020402070f0b0604050117031801020304051810050402040302030d11100f0b2e050304020406030b0705120c030106210e1903030f1806 75
    0x540e400104007000f242400609440b4000000c4132041d0303200d4000501c181d8072940482c8680518006140f82210640320140011801010322070090707241c507039000031900d4550484d4802604041041c90380307251494600501c010541d402380c03041e414040080b070081c040b80030440c0c00b108690011031030801400c2603400c529001400307407410360009020018494a520b0300468417595000b8940c0b8192410382e41402d8055056000907002c3d501c10300041c0016180010080c1c90b1a8150500038460304542e044c041c500031070204403800180c10040151a04803150b00011107112040700c040764103141c070a1480700740034180000e582000202843c5c00900b240030b0001507030042c6c0060400b280d03c980300d4440701d80b1034000340c990b407000031400100d11001d420700a0199810600606040d859075241c03040040200501e41c1030a00c95500716110162055032650246000c1c40038141945d82840ca21506482108407030101a00401e0420240112801551060300340c0c0004445510f00803000c1e68940390300800 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 309887230 1250 309885980 309886001
    0x50906060f091003020a060f2a1506091104140d0b06010f050409091a060f01120b010c05150717060306010b1c050c0a0905030703020307120c0b0c010c030b1002060a 72
    0x580f00000440561601c0102e00003400583e01c900300b2070001080c000b0040045104e85641d1890700000103c80030034601c00700d0500329008502d00c0c2031480284c41040017040264441c055003446c1a2038000d582d44090040c0c000c46080d0040c0201181d10b00d002e0124a101540c40107050b404000c0000d4455030140312040d2051205140c600d0405403182200c000b201c1e01c0c00815103071040030b043c4040c0d0070300044847da6030101050b941d42038803803400c00c0040e145074401c03c0b004c003039a922580d10350b9443c0d1080c68000d81040c0c0110407503c80c4196400380c40c001c80000da81020000c0e082c1c8605801aa5000d100e0368091400a401440140c0c038007143c40882d5000001408200c1484d2200900031103011300640303000701800b2103056a07078000c400001d440c803401580054002d400003c01000036907800304589045030307200b281c0c0415509035860b20000c1c5090541190304000780108030805554015400000403044a840c10085e03002c2040800c1404000800d8145c01a484480000c011040781c2d048846545c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 309888480 1250 309887230 309887251
    0x30a050717040b1501180603110c01110703080f160507020f0907030605030d0f08190212010f09050a1a210a030806100302040e240901060c06050906060f09 68
    0x601d10035681164240c03042c0e40955000e0002c41c01e210500d0340348039200c0c81c9088242020031424400c802d44411009a501c40c1505065881c03501052220405045400c000400002003060b44143c0303144465542011900390000748a140000321302c01015030409011308a529417141241c840701c0011180c583c044a0200e0300181800411003103030321500d04042c096001e42d00c0102e074840c1000d013450310304048070020900b049010340f0300011094010082c60b411800d0040703038015130307440d00c01ca0401901c116000520354071440800004e581d5040d50240c02031b43c001c1e05040c001070b1107002c007a00c151008071b004000030003850708280c80c5514060094115400d2042d40240b0000c03070f41c100303140c1490a040d00030b801051401040100c18588030f0a04805401f0030f050440c100740c02c0004c00e03030f0054070041202221032015500e41c6840d160b1001e403904d003000001c020f4012580c54034001000864400011941c0394107000200d2088200803441034800e41c2c0180c0060360800d011000c0002c5040c0292074241c14 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 309889730 1250 309888480 309888497
    0xd1101030609020c030a0f0f05090409050a0b010305031c06031e020f090c0a140a1b0602070b0112030e1002060a0f06030206070303020912060105061b10050702100e12030a0507 77
    0x70b44050019010343d40c9810043e60b00c480c01c524018122058500540d41000b00200301c01d030070541c008080e98280309040d82d00180d0000b13541f80c541e10380002c401000c3c1141b13006500000402c000000140080540254004580548000e150341629220300000740582840307280d2402048001c0c840f56040c0340002c01c114245048117002c0b6220400075030f1500c1091000003100314005030001e2802c01014100d110513442c081c1540001495800840d04108c12040b01090040030710403103030180c403011604000003611f01d503035400e000d00c071191003914200c02080011561000625195501500948964010b801559159103150004240401310391500c0d543d240404000b40c1c80f043e02405009100741c0f00182c0c1d44803070204105190804a02d01c810320760003500180215160401544c40c200c2401920710303048019461201e051401e0003503440022403411040003903581e400a901c1e001309618000410009801160442c2c645040c2c40540707290000800100d602c60081c1c1d4842a803180d050300d00303200b1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 309890980 1250 309889730 309889739
    0xf061403070e0d03020606030c060c100207050a06050f01050108060102210d0e15010f080d140d0f09031e0e0d08090a030b040303150b18010c05010b030a1b090504020d11010306 77
    0x100218036044c3e0041c0c0c009010092181420040030184c2141101c10b1404c000000b04296610b044490303108400c1c03138005c502003080040400070912000c1d80580e0900052525030f4403c0700c159024401c450006540c00045412940040b400006c0c003100070700d44483c1f10840d11102e51441e84900710081000380d9424106a241c1c1e024400101905000a481e9400d940b4004550524441940081035140c02441c0728000d901c0c2c00c54007055a507910320340e40540f100c0340b1103441001070005a0075030382a00d050900901c1059400928210540d400008080025955040c1182d8803410207169170340101001207803030046110791002d80a000c00083c100c2d00a030382ca039900c4440200064070100c022944589401840c00d0b001c0425401502c54600c080d410140e20071061407880d542502c20742d052002d0315511006101c0f080d0480c410004000e811180305c02e0461a001c00140340c1c80244061000c40b442c4003040001303147c05018000c64000f05480043d05058443c20004072021048c981499501c200008 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 309892086 1106 309890980 309890989
    0xd051605160c0320010f020d0f0c390510050901051305040c0c05010e0f120a03020c070f03050c09011a0c03040305011401050a0f061403070e 62
    0x1410a076007070a5429503500d40000e4000092101d29a00300b01e850461445070321820f9030f030f02c481d5107241d039401c98403680c40072420000a9400c40352805007910a08401c000180101c075864511480c0a65003c46528000c0801500b5450800100d98a41c400703170642c80144415a40050090314030080101148141e80c2c5903070500030041403400d2801181c10f5488068000544100002c00007500c02810420070031038105d41c20f6090226040003004045404504180140010054845001440e81c40d540002c9050801c0690070300c118248071008000301401420b031141320b40300b1141903003021814241e130241424020150307500100b00b520200f0307204864290720401c0e4580c60f03070340e824407007070861050740e04c00340107903007480618010341d80036804540c1200c000b00c2d85003101c01e40c1c0351030492440219200c0d20740480c42d0480e56284081c1080029944916039240c02c2e18025100340006 = true := by decide +kernel

theorem cover : BRFrame.Cov 309712230 309892086 := by
  have h0 := BRFrame.cov_init 309712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 309712230 ≤ n) (h2 : n < 309892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
