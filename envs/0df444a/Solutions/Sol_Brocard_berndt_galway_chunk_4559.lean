-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4559
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:00:34.795536+00:00
-- url     : https://prove2.me/submissions/9766149b-aadb-458d-8b67-64b9cac45a95

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 819784172 ≤ n < 819964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 819785422 1250 819784172 819784211
    0x90c0a03051005150c070e0f0411060d0906020a0f110a1104060b0c03030103030e0a03110f0d1704030512031b03090c0409061e0e1e07120f0512090604030f080706 71
    0x2170907400c070b0340104c1c0d44506170710b50208160382c1c500d000e10400000c103010414407490701d06907250040c02e5074030340f030a4100c440d0215480d056007141c0c1e0039008510700c544140c000d1a107140420081c24031030000a0015a143c0d155420070100400c2c11099a92120813915298001c05c05003285550041e6215290342c0c07207650300c0c5c000744400c4000402210101e040741c1000e1b0484421a0350160781d612100030702800b0446606880300145801c43e07a03400700940131440c0300b1803181070402182801c0740d03a02d04604000d41005944090b0f0b0003050001c1041c030441003001040c00e5050780c0a140500e4030f0362a511425400c065052503840d5006082100580a0120540c0f14111400501c000148a549280b4071a42034076103d101505d006d8001040f81000c0c1c4265120141d00c8036401070980c0d483c83d444107500000d40384503110640c0c452030b9502c018402c02c90b0802081c0c042c1641011000e040020034000100c4500c0781e40001010304d650741041500b0014031800740e40d04c03d0b510002c20b01a44140c0c1d0300403084103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 819786672 1250 819785422 819785437
    0x1503110d18330507110601140307060206010e01090c090905013003170c07020d1103070608090703081602060d1b0e030c190803070b01080c090c0a0305100515 69
    0x9001200400d81e54078800b4420440001c041100e6201c0103886008540203041c010003100900400009a064080050052a01030200ca184280d9520b44540c1414034100c8290480d030150f6110b900188400c241030b074003070b070b04458500001003428401c0143c02c81d2074000552012005074202f4001141c94400000134800c01054521440340102c2021640c0384040c83c1c204015002c20100310306aa5049400ca075800e5000710003e08041c503001070790f40400c0c00101851000d840520446015201e5840e0501091000b00b07042c5c0742000030f60400180e403d80f1802c581c0320041030300b0300000d14000010311618134080c002c2c1e0002c115907207500390060700310017529400d14a40040c5450103030303d191300c600500802e80c2400001c0c00034142a200031052150a290103030300540c084120940002e41000301700300521003e407040469500c01d5240c42d078414a85140c0004140c0300d00350840c2000b031001021003d8601d602003a15000c40c45403075054111881c508182c00241d000100d01901660f50002180200f0a0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 819787922 1250 819786672 819786683
    0x1303060e071d1b09010e0409031e081602010203040507060c15020c06060a081c050c03070606150e03060f040b280911060406200f0d0903020f0a1503110d18 68
    0x4144420404624030070740081038003141c5c0c40c01800301035081c1fa9100c0c1654a12904141603401b18113501c2d503c08401401800002400344001c0100c945112151034440001d0384c0000e5046040c00ea91700703030b1566a64001c08003004441c8003400c0c203000030750103100484900e5000442d0388110272003a0b540c90741c008a0707645000f098000e5000451103000180208243c5182d41203501510010404071110741c071182d84101340340700030302c039000c00300e8010f11505000b085841400c284c10f034000d880c05000d070b840140149101b50015810042c40c07031252081d0316407060b0701503903000303403a9295982d40100e0340f2102c0f81010200b02108d030a450445403a0701c010100303401081070205a50705807042009078403460040c400040c0b071a13283c990680b00300c0c513844440d600c150415544200004071005203080784000c001c800058030720b041003096040840001c2d907900000d0b14900c0b41303b403c1200024074580484140020140d070b07920065070a12074141503914a010081017070094140c43c446091a900007903606450 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 819789172 1250 819787922 819787951
    0x204060e06030c030f03030a020d060e09030901080a02040501140a02030714100e030913020c030712080109050c0c0d120908030a020307080921090d0605040c09050105061303060e071d 80
    0x10750b190004401a1710041c84004601c1c680d075121012000c1e4110780c1d01d185500f40c03104404a0804064000035103d800240011512440ca0600040200c000604512605441000700748000d9910401c421086403103030f10140e541c0d06a50341c0483ca588104040500401c0b0070510000a80c00042140c0d6840d62080324140421040a0f41c3c0c43e480e40300324028194007000142410f4841c002680113840548800d0041c0c2e0f003010f034107449080d075401c00001501d0002d6001c0300140b104400c5e6104294200000c4801281085c65111003141c0c1d40e1000c6810300180300b0b1501d046603030b00b669034000302d2445a20101040e22410006131100103504252940360200344003100081c4000c03400244d184191391102c101c00c102030084d43c0361f19030b1a0300c0f014000f600507003c601d950380031450034011030b4000c034403e4400c0b003803803480c108550080320410f030420740c070440b01003042c19501c011079260003040d6038214100248061080b400c9600e0000c26500c004606514a034020380306d03c4030319040a100e05803c060028 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 819790422 1250 819789172 819789193
    0xd020706120608151e0106080105011e0518061e1b0a03020303010b03221109161409030a020d030f0311041512060b0415020c1503010317070204060e0603 67
    0x101602c4940c05031035000c0d440854500070011255078011341080c200c0c44400e80034942d2800c1443c00c20f0302600300001144180004000d6035134445907884c0a031400b5241d803251284c13001c800500364490308804010400402d000341002c1d603241c1c001c0700d407403000200c00080ba42140c4003030030362642c00401200d0400352003802c0c01c0700c000703102117241c6040680c151702951541e0b09118010b106500040e00d10200c400052005a4061030320303c90038040240605000e4200e924030030308000340ca420080020780c0e41c61013041907000040c0c0000140030b030340035501e070070340d0b1100840f070007292610340300200203035000e40b1243c02d210a1642101035118901800d540c240203660248000d048284a14441c07030044004075459400c000d4403418902c0d02d4070003d004003142480d902c1554002d290000d410015944449060501401d501040354202488003074a074200510380142180803d800f0510029110b6440031440200ea081010100c94901e9402041048915194440d1150b400710071036500d4024442c54600c81c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 819791672 1250 819790422 819790457
    0xa061715100608011a040503060411030609010b030705010309080903100b030f0307030c0206070201031b0203031012110409080708040305071706160f1103040b091908030901200d020706 81
    0x2520b001c0d0b124031065902e0000030158544180500801c4001d00380b0020407190740600069004d140a076150859508803081054104038001c0c004042c0c3d41e240403441c410944002c0750000444000b42800920903020b401c1034401485481509039040c090030050211061181e07020581921003502201d41c0c00b150408001e03a68490031201401044442e00f0310801842d10500803c241c0c0d106160114055203034909c8230800340c15210300d20015800c08030411038a009040411b80c01441c50007020074140020392141c41d803000300c0347d1030f081c0640d0329080c5140903c00706401303c0d103005600950048da100c1d40ca00307015841d11b9241c0a410804400b500b401c07012100c0000302c45024102c0c8184401c07440035000e0043d5001d4541b0101e000a0040c030f9010540603040a002410040550317001440d50b58400303004010800142043c208080c0c0300744034041c010400e0004c103942c040d070710130300b0710803058582c480fa5261501e00040000300c40d441280c0c0ca499580780c0c00b04a550440742d031500d03107000028030741c401d5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 819792922 1250 819791672 819791701
    0xf0a0f050406080f060a0905040b1f050f09091606020706120c1b0627110603040c090b060409020f0705010506150a03091e0c0314031309050a061715 65
    0xb1030001403201000714400c01d0001e0030a5802c03841c018141c90000c0da403888220155102224260380c0c00e604c11f0100842406500320f51460744155031032003480d4509002c00503a0b0018032140d07150240025400080d8105000c0188500514036408000d050565502000759107010a003e9040010220a480701c100e14540c046d05146007074a85540b0a82004890390441541842000740d429070384071a41e003c500c1440c0c442c850000c42c8a51804900403582e411300382504503064140e9400390008000b0480482d0300902241c003600c0301404046900000140003070340310700650300211603a600c009440300007100400f00070000c1901c524028011036481d4070070040402d00f180b0131070790101e071700304102d1104a209601c82c00302d0600c20103c40c0030740101c1140c4849280c4207648112440b110005c424018428812510266516458015031038080301038054a601e216074410b05d205561a03101160720280c11741c202d04040c001e04c1100103480100c03048076550360202010301c030080c2c1200c24003140004101050 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 819794172 1250 819792922 819792929
    0x70f080d0813061e0f02090f0604080a03080406090c060933050a03230727030209190c030f0612020f0d020607050706030f1d06060105030604060b0f0a0f0504 69
    0x40b280039882d000003818500710302c0311450750304c110030b0203115035075200703078540b0b04100000140c407802a482031013041c00400720501d11030300d818801000a0a400100e607054141d162410822030b4946150140c09030110381001481c1584031000400c0380d55101040000b200c0100c91080b001d1a600540b2841c280c0d005001604100c0c51115041d080e00e0098004181c400d850f481c2c00282241d890031954815070010800e1300c590004902070089450b031141e00310b080c60a400401e40d50400c044151a02694150301c8001d000300402e100141c0c12040341d04402d41c0c90868543c00344441c15413000c1c01070007403405018040e0000d117410380200b40c0c010a4218100786a82c00703042040c0c2200c40d4003c00c900000030380c0e000c983c400d0003048280300240050241c03500030f00300b0b03881c041012003918920f132003958200d41d5100c40c00c07182440d110b804548001341c41500800d081c2801541c2e07481700c20224010301069002821554000903030710420703505420050154502d2a510b891001652035401c666a124501c07 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 819795422 1250 819794172 819794191
    0x4090e0a081606390908060c09030115180f09020612010509070e01020618030c120403060b152719030c080a0c060f17150f0a21080c070f080d08 63
    0x103a0310500d00701480c609015034502421700640c2580d842040038034120302260908000d6030080761015242c2400d00500800304c009e10700c0000d8071030500f104c60303e05000141103a01c03400d458120003a904112a840300d01101d801806207592600500d87c582c610400070b00c103c0780680c40300c000040a40f03108081082450005901030203545c2c5034034401a203030f0742d940c07041414540010007134075250800401107009640c0b0440310403a1540d1543c10000b044076410341450340030300301c0e1000b40600d000e070400840d00d80a0720001180c01c69203003542000c0446a075112165044900b00454596100541c80f1080443c0e04c034040d181200c4d0340b155a855100c080b00d290052a5914081c01801100d000b642c1c40541d4083c0c07450002d005243e1011024102c0c003069900a40c2c0e0700e402c900e61240c60414205010b01c09070151000b10360645410401940708800000316407000072008a1202080b80d150b0444200700503101c1260340d05901e032440c0503a40c590612510000d0b1040c000c5042c04131b400750704405d10074000031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 819796672 1250 819795422 819795491
    0x90909030a0e130b0a060210181505041b0b040302130b011b03050c06012d05060a0509150d06060f030c08070e060c151f0b04090e0a081606 61
    0x140144030b164210f82d50001903072502c81300b540300d0540300c0f100071900424095000380301ca03910180814085840700101140c1c0b0381b080548080c04a06056082024403110800009040c4d85500345001081c001c140c0c8034011008e860400211504168041d00031340780208c80c4071400701c0301850340104445407507804a002c030701c3c00d00015a500025080c40d40015019042143ca081815082c150801c007090700104003240e030783d2501c8035860915440b002c03a0355078201c908031145424840028018022042c456081040009942000c1d850700801072407030b03855a40003184c44032200e03849007002d4451401110001010080c000b00020306c240220214204241c40310100358031100011294407001c031488540141080100c101e44101c1000030b400c21002d198203410791390a1402d51248020000000004200e050b144184250000d0404480440d0000305001810341c0e41d00c0c4480341842e0710310502a01082c0c0c00300c2c0391290010080c0040700d0151143c0010071141200f001010340d03004458100f1548580c01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 819797922 1250 819796672 819796697
    0x31c15030809030307082d21070c0501090c03020103050609040b15150c070f080304030c0e0a0914061f08060f04060615020a210f052805090909030a 65
    0x7004080704000079007542e10f844941d490350780042e403094088441e15881109120b40ba14152041421864990010389140084001c0809114110049070031410324001c000315900500808405807400d5120700240302e8824a81400e0350600c1040c48113a0104e0b041c04005401464184e900ca4401d03035101040440549991542c1022680d4800c80b5940001c140500c0f08102d021500280140900c402d004140090400302d0240c1014503503842000281d0051200340001181d181d041021744100d21000021640c40040b1100a0700701804068048803006d080d4500510700400c1b8240700781802401c1c240e043d10403000781c041c645030741d10a50460790030003000325222000f000021340c2c01901130700d808181c2c01e894205260714038003908460000743c1d00c1030180310100030b880b030f04289041d00d07503140101f6901c8200c0006008411805502c000308000003500344a050040c51007800725101c0c0c42d4824110011405015002c0d0b070150103d40e20600c0c06000094400c05d0001c02c45030003401c660b0f140181e4012 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 819799172 1250 819797922 819797933
    0x50a09090804030b0a090507090b030a060504051002130602010b03070f120f1e14030307080613140c0d0f050c09010e12010509161202150307170108031c1503 69
    0x11040c040700c0c203200800000010842400445001d00c40d40f51000913461800d1a00e6032070b02c0d000b540421240b6050a0800d12a03540c08070b1540d100582103000480d00d545c45140007800c04102201840c0301c1b40c404642a441d8a40d0015000103489445d0001c000c00c41040c03003099961417844c40380c1c820314103541d201401910000c24811103454030402940d120b1304607a5682d03861001451111103400c00400a08009009891601e400343d45505005140f07103007000e65004020140060006029504580b004802d1000503842220303488540c1d00814a42d0500f0b140d0703260641e201c82140300d40c0300e00b880d1041811541c00d2003682e00542c3d20f4601240382400b01001520b510210450050780300303082c40c01078210f804080c000d05110b814a90050700400800740c000e07001402c4d880e00040382c5088071014010050700d54a003a200900c140e66495601c0b0b03900c0202c202d030200b11307034160b02890402c0b0360700010300604000090400c500e007480c06010f0140c80399001c1c030211351003690a40135a00425808001099 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 819800422 1250 819799172 819799181
    0x4021509010e15090301060e0105032e091b320105040e090604020a15020d05130909030e03012702060a030207080f1c1418071511060108010204050a09 66
    0x2441810304012401442c4001000c400750007000e0110500c0000b0860201c1c17500380301e0071001c0e01124034004850750400000c030340c1d030b070b281c80803240410541e020280d00014405240c00c65503a0f81c072031090080404516100f420b60810307003591209001d55030004108410150750144050102088800d600c49410400f88a01002031137010b040c400208004641d004d4400740061054402000420303060509105001c245034080d80f0544078500b03040c0c0040120340c2d000c24900300024640c070309146c42d0100e045581d41103038a143c0c0b00d0fa0109140c88180382c100754110444486408049000b00700860740304050300b0407a00c0040b08902101e481030060001890520f001e0208901145001800c0c042039998000066201180124400001141320409100004441c05504241d01000e01c924111201d98030400480030380b0451000e10091203c49600d034081101034020a100c42d4103e8075540d8a00016148800d0100d06c2c0301903004150012a01c403105000302d07022124080c110b83c1d40e061401581c0700040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 819801672 1250 819800422 819800437
    0xa12150b06090112240f210201140a050d2309030c190804030b0c04031101180303030504021807030c02071a09120709060f06110d090506090d060c03051e040215 70
    0x90024000014030460300c64521001d040410f4801ea0f12501f0400224071004a0600c0e28013560030144a000050360f00040701c4a6019412000c107880769401e80041da4030b8003079070304440740301031400002d00035102c941e003c581e694401048000019455810002d91244203030030002c0390645c000d0000100c407000c100c1c400c1111030b014610550925072203949290001e80190381b04008a9004902403080c015050b07480e40790444242808040b0021107414482113901a10018040c980e4500015056413500482500c01c14800d0001013624501894003034020620344401c1d10040c800c48001064050022501c65100342108038007504000c2514200f1258003d00403030000c46020b40e40c1c00144070116070103100c02800c10b50406007485410488001c0040300070f030402c501164807200b0071040050300300f1049026a241920007070b5440101a01003010b46070a090010086441e00c00d1503d01168540e00103809120048415002c2d5101d249031a90356031010340e0003950055100c09141020700740d5030010100c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 819802922 1250 819801672 819801701
    0x312092003030c01050106020106170601030317041406270303060a05042c0c010f1b1209032004050912090103020307032403061803020c09060a12150b06090112 70
    0x622250b10643c50079144280d00010150303450300014450341004045000c0c40e003a4184c0101980c1d8510f460041200c4400320100d002001c8510118092100f0328100e80d40c44c807162800c40b0766608095001000350800ca04103050703820080620701c08207041c0841181e001d840300030108800a03007442c00704002003940c50301c140f06948001c4403145855000507120300d002c02802c0090400c030201c2000150951104425034400c00500008036440c141400a60807522504101051422a080c4a0550b0040b1a68101900000b240d2103003841c10030000c10061000201614240b200fa260845010703641e081081036042c00c0d10040c800d82c070040d4840c2d800f079a400990307450041800d0300d400103030040c2c0c0c5014404e0040902c1c0c01c40300a1048c002c442c01142071684e00081240708214182d04c000f500d48022111181c441c0340240d020840e503544609aa070003a05c0b0f20124036410f9001031508590318543d00301c3e80c01050b82003000d06506c605d0b02d072066440c0075006840d400b4580d1b1000036850002d00e8020b07401d411 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 819804172 1250 819802922 819802927
    0x10e100f1811190e0301060801140a0f0c09140418030c030201470910081002071518060e101104060f0f02030d140103031209200303 58
    0x10500168410300c0010440d0a44507058040d034010250151041d03a82400705500040200c0040000f1520b421a040106403400e01300e18201000080d0252800d580f0240d1190708020b50f060400080ca49820300902110780c080100d02c1080710076906a070781c1154902c000c144e402a08115298040c0140015000b00600001d44036181c502d906504010300b00f0142d0001d59a00001420941c0911074801c00c0e92011101606489904041e040b80c41c4007180c180800d580000c06064521594890400d0b2503040285203044614041440c91008a0ba46c4200703131461050000c0c940981041d8821600c0070382e0002400404200c0140014001d40018414925524540003014001c20210b01c500d04509001201a21b194090b141840050355204c60800d12032000401042158681122561101143c1d5003018401c0001600083e400d500070707000c13121a15400c155003521038035a54a00c00d41a02d1003a241c409c3c405107400c015000321030364041c3c002c144403200c5403100c003400d003554540211144000c08592 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 819805422 1250 819804172 819804179
    0x2070b0304060e10020d0b0d021f050c060711070b041404021c09060605240d091a04030f120b01090512031c051501020f0a0b13050a0c060207050102010b010206010e10 73
    0x2881e01004002c0c00d809130382c1c080b17060324171203040b4021448003050841d0040c03041200c40d0001010300c2482001100119220301e4035054450181d0160303000503e90a05551041c60103e0340030b400d003820007442200310f000b00500130a69903035000035541603418a0528921174100801400000d5104840380b140d6480d06407405041c9070101d010b00b141d418480c00b008200107280c042400a43d88c03009079055001514078020400c1640180140e0f03400001d13104000c00c00101c0c3d803d00100b60802428203115186450040009140d08200324010400c9503690f40a15140348250000c00c0381c89061074540040c04042c000c02040c680742201002002e40441030b6450020011100c044030601b0311007442e0a10b8482d020000924501d0004040701c040a002034003c1d0194171074099101d4800e244000c1c24074400101069000c1c07059034a00c0407030b0313501c081120401c40703180c280036542c010030b88a8100144503076600400c0552040c041c1c400c8140d41070300101444d074207042c82600502c4004200308581e13a66100c000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 819806672 1250 819805422 819805451
    0x4030e13021914040b03040602070f080d020c1603080901080a1b020109110a0e040f03030b10030e0c0a0807180b06040609181506051e0d1e0c02070b030406 68
    0xc01c0107100707030445503a030000b03000382c06005840203e15140e06a00c080c13004003e0300c3c4c0508122a48907521660041e51051310349400c2d07444a1100c071307015000b2040410703120039100881d8000c01d8010386c1401203036510044001100704100e446c0c04010b122540504c01c107240c1d5409108440d0300a42c1c200e001055061000d8400d03c214140d500e01580145e4444100e5000d0000343c0e07803416550001504c01c11051424030080d50011100600300604035070003008964140f521030b6120417402540185800010a200c00e4001c0c081c0c4601200007511307006514200911386807400e40102110144070160038218034103648103c54904140c8204a640d40302c1c0300c1ca840c03564800005102030408ca45414000e00c3c100b00051807201e0181c01040500e5151002c500081c43c4150505011117001d840d080d60b0300e82c0385444c14104840402c850420885012403c004264065003100308014030814001440c41c3c1010010020349443c8220840541c01c040b0090000c42c02c09001958030a004e044045112903007290a03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 819807922 1250 819806672 819806677
    0x50415030621150b0906060d1401060503090d0e03060c092710060c0309151206090516261b030a0c0f03020703020c01180806011202030d02070e04030e1302 68
    0x31030581112508100c1c2001881c2000680200f0844000c03c02c900502012445201c009081030744651000b2400a2803100c15030420402d44d00034000710040d9503910301000c0e003030b500181c82a4149026106884020f6445180e1484410078010014007841d01da84070034542c254001d07540c1d1a080341d81141c1d240202d0001c2c0d40c44115003151864104600c0c82c0a90f1a14039445180c1c111a00300801003080c82e010a40c8080f0501c2500c0d030307610301941010815a07094070f01c00c244a030400001e6003421400a91010f140d84103c4c4500c441d408400c2c64050086411242d40b400202d030342510700703e29602c10640901984800c1d0707100840e41008820111071201c0203032986c1088600030006030301d45890400003a4045054821400642405c0d828242540d40203912211042081810042041c500c41001c05c2108000c1c3c00810f039220548041c1e5845400e818000b22541800740e000381301e844c1041780301503c002540d030100e840d103036299455030b2240c1c0d500701c800182d000411984034002150f90800030049100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 819809172 1250 819807922 819807959
    0x40c09180206030f160f02030d05250e040b22050c0c0313060306050612041401060b0c01050f010605030f010b0a2d0206090610121704180b0609010504150306 69
    0x485117107045001c14462080b00103a000070454524021000709400200b61544a11011404a1035a980c03084007440554512903505c410182d540240c82c000360002501121142c0a50342030080c901e508050040c14420f030410382d40c02c05680c1030f664181c2c003507e6100303035080085122618604512044802d103103401c6051094236012125804000301900361050302c00070001a22180c2c00d00c064984a03030140b50000f80083c0c1340244502a40340245001e40c02100034003030318481036031907118460b1403600034203003181c0d0380c104490b901c4004540580a081030324450001c1800c1c01406030b00706181300c8000d410040392501801490341440390b40d000701041c1e80d4001100403074003040344c030140f00b00240340c0705010b002d541c9075410250912201402c500900402d03201c001c0b61880404010342713882a072100000c0101100700201081c0400c1c0308000c4029607606510400041c05108040d90400110703208100001d0f020400400003000021540803860a07008518103000401660780c0848550f070f40744215 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 819810422 1250 819809172 819809191
    0x614010e01091406100e04090203030310031407150c080403150c0206070c0804050f13021b06070311070314070605010602010c020d02160e0c0408190c050108040c0918020603 76
    0xc0180403002803032281d031007110005022640b03a818180f021170000c0480814080820a88030b80c115801d899542080a0701603001d030803a5500d01e080f8103000300c03800d802e000442d481c62040d40385034a000b5000644005880c050a80002000403406050340c0c40030114401701d41c000e60501c00000401d14201c2d114015030000c0001184034801070301d00a0030940001e02c4142401036101c840400300c7c110307605030380a848080c1d800607c01c05103a00040c401d4441d2402000d1690f000064042d403854644041d0003501d0b9508080b80d08a072542d1905500b0758244048024000c503082c4001300100c0c1c8501070342003600f04000e2b411850040381d51240015241309801010150b9110080c038941c3d075504010401c0c140e2141d01c090203042d6036120240180138418410003000d205c0260109441c0e518403400c4500a0a410f801c8580c0c0004d0b04030001039207509524162580804d400000549500a90389240b00c0c5900000d0141d0030b509058001c1d0091400503142e1054045950604006885020085000d1071011 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 819811672 1250 819810422 819810449
    0x7050717070c0504060909030c06020a031e090c0501170c0306120f0c0f062115060a0305090616021e0f010c02010209040b060901020a11043b01020c19061401 69
    0x11003030000352401780e800032000c580303441d005001180c0d10081700c509c003940c003180150341c2c0c01c488001200034001078400c0036100c2c08801c0c5040c000e02d02541c8011a024450038401c0d5010f0799910056855a2610981008030f2002000146824404c0700c0116030040c2d0060201104410b9a034000f8500350400704d0103503c0c0d6001101791180c40c40e10010544955804035066890301260740210110f50b000e1958003603c0030815800715210803604018401d405030302a086588400c0d0000000f00504000d85904689002e4003012600049490f0510441c4a5442c2c000b007111124049071200d00064040040d1180c2c000c8192119002d007083c040c10050440c00d50000d629420341e0410441100c0c19106401d125031801c0280803510b0740c02060303880302107400c000380c802811114004140a04040c28405117254100c40000c020141842c0ca003010b001c02d0705e0040ca918002c5400312038201e2140e40c2c1d101070076911002c0024803400810b0004044644503803000b02d0401c0d00044102201d4400381c00011034004903 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 819812922 1250 819811672 819811679
    0xf1b150e06061c081c0203160e0f1e0f0a06050909060a05090c0f0f030408031e310c08071a04030314090f09040b0901180b07050717070c 60
    0x4010341ea070030000032074006100030070004084607200c5810000034440309010404030413400c1000510300070040188015583c0c2e190450342d40000e04400080180070480d1040011003a0074880f1080040910143c0800c002c4c0076400c000d2000212000e40295109050080c3e003096521002a80e01c0180030946846440b00c1e4003408205410030007c00b2603014406040b800c0120350f960002458000340d0720002260b03103010844e510036062041c039400d1004000000140800c0110300c0005600c0b803c8c00040c00300c3d00c20005444031554640955618010485001d1411811181c1910390349114603151601d031750280c42c2d544c606058100661210485400c0b59008001a2400f0790024000701e034078011682c5881d0540d5006014426014031090700c41c0710106140e03205032a2041f28026551009140c0c1a40745083d00c0c0c102c0754003d007204c1105581d420410b0106058032618454442564096984c02d0695240081152103810201d0156440e001e0058905000d00c280c50040103128000c04218218506 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 819814172 1250 819812922 819812951
    0x30f0303070e030a080f0309030706060f090b06070f030e12060f0f010f030c060e0105040b030a051b070c030219030b0c19080f15030309030706050c100c0f1b15 70
    0xa0b8804502e000390803450f80040040da401003140c01544440321401e0722901c83c14155440c60081c0e40300141003e01d070810101e901c0802c071b407203401110400c050900080c002001032102502030ba00d002050303c18075031801000207000d1044041a90380c0607240d040e40c842e1300703c0b109181c0318040d1a0f51070641c02c20303002e02c56512048a012405001c034000701100c100c0c50341c0d032500f00c400110701c00c400810902078520310b2107030b1168084400030f000d8103c2080d02c9040c01ca2603a0024141551141101d00c26031041e9200598840c042c0c44507150041c008060051440c2c0900403117010307801002540301200701002c800076444250690042d0b940c1880c0644640423045100010080c44000310b00307105100040041880ca10f049066008d1240302900b440b0300440e0740401d24600411190f00d6050240c90b03030104000350b1040240150b580c1c2c000407a2034403290120740f50b0454101c05c841c1d000181c6102d070103018481c003c490034031540d10550b41019002c00e584d2144d0721040301c13a24549207130b20f1315215600305000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 819815422 1250 819814172 819814187
    0x12120c032a02041b0207121a090d0e100f050f070b040807050f0a0b041506180b040b090403022802030307210905060a11010b03030708070c06032d0b030f030307 70
    0xd0b030400120f40c10a800c0c010b07503241807c0c440d00c11441e4404800c032080180080b01d10564806600c540c410072309221070400d8907050702d5003096000070500014024a0319000c072020103503550300c2d100c0c00380000f1003030000c40d103035445026804c0d90a01c0801c10600042da03c0d10303d45200303500803002951100041c1c90514200740d00146600307001da101146202c0031849180e03107a0b030001e070700101c4c01c0314012800401601401c0030780e010405004271084400015542a0407091803543c00300c60030021482d41c5005c000305101e082e2800340042e4000c40d5040401017034820b2585a0703c03030181c00c411520942c0c0e400a4070b95400940200e661003200c0a40c0301400008100e40c020120360781c24852003082c00e09002c2407050207030a22940800039544506034020700d0a43c00002000790203402d4a641d5026030405011651107000100c0782030036592000685140f180c030400003903000003a00202c0d05a0043c052162061506081d640c8031592011801e556030740421078810000a550040e540300c0c5003c5c1780103441130 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 819816672 1250 819815422 819815441
    0xf0b0405030d030b18040201020f0703061b11070b0a0512040804090f0e0a0818030f030406021e06010510170f011a1e07170d0501080712120c032a0204 66
    0x142c1002100070300c41c0c0d04d174040001414418140b10540b0340d1381d400100d04c4d05d000c2c143c000b0564041c5400210600c541c50300303c1c0d00c004a01c40041c51b0101c14028080703640c1180600c040250b508004414449909403400414160b00185011810aa9802c500c001c035080150390458111000050410914200c0c0c001e000c1c17509500da20420030388822030030319600d914200500034007a40d00000c811008106502d2185519074014040b6025070035100d40003a540d600a0040d00d015204000340b20f031001d0403103030341205c90302c0c0744801038001c6920f820244a80403a00e400c10005000341241e15a0024501e0b5038018840c1c42541c5601c001c95261007800604414410f41c0e40403503200c00c0020501c07011818840b0640603661046507603440c3d44a080c030202d01c040022165804103800a44042040001d8110b030381628003100540e070000341e60303076440d00042c546440c1c010103143c2c84821071a21340d03002c0d08000c04924001d05205010100c40d404001c0880d0082540403a0903403054102c200f541498803070380c0540d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 819817922 1250 819816672 819816677
    0x610060c0503070213180506090c04020901020715140a0e150c0a030e0312040803120112020f040c0905130c0306080606090627070806030c0a0b0a03150f0b0405030d 72
    0x25802a0707100d05031203116280000e0700450940030041c60302c054170713030225840205210000741a10b0080c81c00b19100d40090721950a6880f4900346101249014421108000416001001d08502c0d0006c21001c200141d6204da05100940301603550300600b550040c40058106c1d030300d46102c44d031200c04001040c4565008440003920500240d129100d0000354000e806400d03085c072004242500380001d01d8000d00c0380703403210030040204000070080d0000003e03016011004d510344c3c5903031703032150071100c440743c07054002139840203a45500641c603042c29841085a5411840e001d00420340301d40201d2000100c0c81981078405a6400300d09190701d40c1407281001a1031350300e000d001c9905040000800c0542c0141110b8803800c804904483d019144d8218002c580c0f03100c510255852401020140410004071000381c02806885070008543c503040d400482030f1030514419034140050756208800405030040d140d0b900c3c0c40c524002003850121180301c1c0c4000d00384620142d68890401061500b08496541000107 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 819819172 1250 819817922 819817937
    0x14010831020102210313110a03050109030815060301030206031302090403090501183b07090f051012020a0c0807080d0c051318230a061a07140c0a08061006 68
    0x224980c0c04e10441e80c0002c01c1030020410b005950428002048141021641c0011094000010410103402001d00c6e1400303034441e80e44580c0c03980310000c01031003003074560b0364050800c10040c001840e01720051900040c10019030b1074100c41c0342e07000c00c0b0260b40640c3d0540202d81c0b0020104907540c1d01c02000011511221100403415242c0240480010406a02040300f41544452490ba9841c1c10380c010749640d41d40040741c0d174641402c1c000039122000c10700451055036214040459076041c403415801210081e41da900c41041814a03000f0029000f58003401c04214408403002c0c0818000c501800b51140909100e9035a000c02501440884400c0425082808820310800035800c0d41c00020800711205040782010f50513480b0b018100903c0300211000c6a0406034000f807124040c060100c030b01c94254000104800703500d5503da111112803801007080c001070204504000034001a004999402c03500c1c0840300b010303600d070000803504009a042340d003145d03200c44204031002d140c141c40c070002030049041c0000b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 819820422 1250 819819172 819819223
    0x70f060b04110423040219030606020d0e010215150307060201230c1b160909050c0303090d08070c05040207141204030c0b031302041a040f0614010831020102 69
    0x1d24010380410134141c00b85070b0040313040745c2d26960112011030901031030f030b030042d0b40c8000e50140040407075005190061250b03900340160386000301c42c00600d1041c16001491800800c030010310055000a00c84001550320f01d084c0c1041e034408000b01e00140c456600081001031078040490207103590182410191030840041c400100c0110080b14003a101c1409400c3c0c50203c54003005280c215842c1080e2101c44600c5030004404a041c0e11003810244030f0070555600742610130400d03549010311031940364019019000341b0002920f4500a003410303440b4154482049540c3c40002d41281c200c02c40c15135140ba2000301016801d10b003844809004801c9001081c01e06003140c40d003480100389030003041c090b1032002011410619425003002d940740d40c001c00038003a1024000c240074842d401c00b44e8442c012418181c0c03141e000000d078000e59003590403d01030700180d2201c04004603800103024240852800054092480c880c01d20188014400319954101c015690144002494900845901115141c031401c419 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 819821672 1250 819820422 819820439
    0x50907050a050636100806011d010e0901090603050d021506090a091202031c021c0c0c080c0109021503060a090c02250e100b04120602070f060b041104 66
    0x12800d070340059450588803003c031880c1180e43c10190440c0208007018440c1381c22a81042c8440c0e60b0559410303a00b03102861139034081560662819200e45000c55040d42d9208064003282100c00b968070014500781804100706000b180070000c0030780022901c00c0d1214006d00a001e82009030300d82088551005040e0404e40140300303d100840a00810b02c00c1c00351201050140c02d00d03401c0062103a03000003001080c4000c010380699a0b600000d881d001c1c800318039440d9010403805100b91070132230780d5140a08408000c01c0c0100001000c09203110002c3c4414102c404021402c600e01411107802d51900010707800e000d50040021002d010012101080c108008000385919100e41540c1100d100c2e0101140d4000580c0040c0e0421400d010041c500d100500246029900404014021618541e101d400d00f030711112009072030702c50240940150b4120410081019104100e440b6030800c1c000c900050407c1141e68031b2614081d0798070410b9620f1130311282c881c403191400c0e21030078200c2000076030014900391500303010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 819822922 1250 819821672 819821689
    0x8012a0e01030906090501020a0c05010507030603050a0b07110d02070504180206070204050a1107061410030803040b090724020706110c0f040908040e040b060d170c100203070e0405090705 82
    0xe480c1055240c150035420815650018806194000c0080d9111507488034003e10401c2065029550341d0300340300200f4500f070b000e0700c100002e880e0448040e0800340c4058503030a2141402604007030802442050020b40050248559030500e0400e5002e0b10280740b80001700070070f03030704842d585000748003c510002c0300582d9000e003190515035058602241c1c03940c50826010043c1003200102810030300015080003086401d90008031501c41e040d458007403a849d903800b0b00c500800c0c1c03400b000340713650020004035010451880c05150300910030400c81d00225129030010b0500c0c11040c00c5843e0a9041060340d5080c3d03501400b8510250909140a010308064100340d00e80d02c07039002140c079000d40070503440710241c2c1d103981d008180d055030464a0603941d1580c031000703105404811107050300d10b401058003140252070100e0480003001e170441785c11203015501108140d41d5601c20300048445105146450021890500140d8411582500c40348000b52541089c0402c1d507070020201e042e942c200500c00e018a6075821312 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 819824172 1250 819822922 819822947
    0x170c040e010639050f01020301030f140f0724020105091209060f070b06120f07060e030f060408031b21040c08010603080a0f0f08010e0606120108012a 66
    0x10820700d0400707000840d0750801003a4100c0400c1440e030355011801511030f410650b4020b0310580c01c0320f62081111401c1c40c04c1340800e0000801d009484016040441c40000400303290303007a080c00751818080c07000c1c1d84034034252a95220b105014411519805a055440342d4007101c290203000900c01d900c1d08a20340c90b1120003e200117012500041400da0107512800241c414514405192594450b00382c00d12221981080365040d119000d201a41e11000c500407990074404003030f42c00100486c0342407800640e40032032589031181c3c00d1310610b00b81001e01d01d410800b89000d24051007410b0360b41d04040001480c03e20045c0d4400803410002c2000f001c00503420b07030043c0300d101403102080403207443d10b180280e18490103a000307050540c01c1201c0481401040c0004200442994841400c0411540e0068031485c55113078080d00403030007130350042140c0500303204030719030103440204110304d09614030002d6044100d00b03801c4a000e6070b42d0343c2c003421441c00c81700b080560305000703101100210381901c41000703020258084 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 819825422 1250 819824172 819824177
    0x50f0402150c0604060f182d060c030516050c0a060c030e1203070207121e063b1f0207080d0207060f060b0a0c0615090c170c040e0106 59
    0x7078031403034019101c40d0b500d540142ca07028105802c10b04c024144803c04e40b000b191034041043c40d80100c10940d880a5a0b01210303c01501c402d94005208503000503081a030360a04c1c2c45141c00004810384243c0c0c0703881a00d520002601d08003240c521116850b60689103041c42010801982c0e0010006540740c1110f61084010901c27000f079120440c007824039030f00c41880c0e074418006516400c1c000e80c0040d45c8111070560840718541d0782e40c04003402c80b4401600180c681e0000300404065004407a56000f1000e00440340070981440c501e0510368808900c28848071140940d0501840000f89070703c40011808102008060107094400280c041c5071004042115259000440d40c0410205002f030b20300c00840702e281107445850b00c0c204400600424249010030a1610313074080b490a40f440150303024a542582d908210000725501c090017052100041a401d0722103200c000b52200b001d015005040d20281d95800549408c0b404456484401904440361000144014417070301c00242b59041c110350703551 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 819826672 1250 819825422 819825439
    0x41d09011103010b1e19083102012303011721090103051335030a060e1006020606011202070b0c1b1c0e060f0a0c060c03050f0402 57
    0x800a8010048040340703403100c90000c0000a1050311040192980c1d00e1491614000560b1200c1c00034014401d003222540041c0d20000074054982c400c5100c60350144103030710030008424058110450540c0c1c4603646040b0044404508000c40d40e0203030344502000d00844803403100803812190b0400a0005010340d982c150b00034000b2004010003009020f21011440c110004013146444900000d64884408a0301190400012940c40c401c0c80c44400c940c0c58105100c0803600715546039240040f690519a04130006050b1170400c074402280380110301680e411400062000c0c94601ea2110248001308405100100603100300100e603004200c45501080910342608201303010801e140003801448400307407060301e400c010400d04818103c014107408803400e5a040a03054980003481d55000420a5030004109072581e1061140c080c2000700c1800d00000c00302420a00c0c1010720401982080fa98134000070348040460003400600d03c0b400c8592400c0e46424000707807504030b40700c5101b02d00280009000d41c614 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 819827922 1250 819826672 819826681
    0x60607021f02030301092a0e010302070212060901060b0c1c05070b04051e03040b2710020105102408100f0308040f06110a03030905162603041d 63
    0x410000d40c0708203064010220210700180030095a0340c10900071110318134540074448039452120741c8850300c64025819035400b80c0202072422202e040440302ca183c14550280f00000c0140ea90406c01d082004401c0010622460401c2c030443c00c0d00c4480e030240c030584004108440c07c1c0f2401181007e45100306091421001c602c984003221548510107000e48504810300502c000c110380400c2e4904100303400e400c0c444410314900c100300e80b00d216900c9040351b1107034200a0704000d280f40d081c4281e4510034100c0700e54800b00300b401c0858500c02e0100048801030750b5034400c100041009141031005021400c05091000701c3da400c0001d103205000880d141404100000a08040029010030000d4082c4000c00d10a6581d80d00c0c00c0c0b03241ea00a4020192960210040454160300c21000004104003600080482c4034070303501c0940062104160550f01c0303004108102c81012541310603003000741a1207800c0b940602c500b62a40c024000d00c0182a4481d800802003000140340c90b54200903100340c00880507482e48c55 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 819829172 1250 819827922 819827929
    0x305031e040306020706090c091116050a06020a02061b0702010c02010e130c02101802091308130b030105040c03050906180a0609110915010807081e01080d090b03060906060702 77
    0x5154001050f03d03000146060402110b6040840308502c10b5580d004200e0310b556814040c3d9017007a54020340d0050034440401018070442d082403000340a002a20010125920340700d00343d9200c1a02900582d10000c180081d20b4000a2004a048101d200080c00c0091701da0000341000241c81010341042507001c0300f10b1140c0d071006c060750310869000800f041001c110700c5010303440d08015400400340c1c40c9030800417480d00c1d40340c1c5601c2c00215401095000c4a9132026100610300000000c180d03102d95080c00b4803241000e240201c1800b03441030080880d10780d850b041c200001c0d114001007101c101410503003413040884c00000c90b00e4000301a400d05458842884e80390300c1c900034944001810030350405505174240700100d000c00125160544030384460b503031020b0700b003451070004e40790a50000d80f8101c0001c8809210b03c449a0f005060011400407100300c8902c15100e03d0700c2070f0815003c5800800401411036003103c0e07001e00405d0980011400e43ca008400100348a1000700340c1e074010306001562400f1540c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 819830422 1250 819829172 819829177
    0xc03030305091f1a2e02030f0313023d0c080d05040b16091e12050c030d0207051311040b1b1204050d230a0b0906010f0305031e 56
    0xf00050b04807049040d6410322440039024240010041881c0a00c1c40d003182d040601020b804441003003034950781c01902c030810700703420818145d002c4110f00040c40405580d00030300c0d0055005103548845150504d0a500411040008001409000c4160740300c1e14280220902954113081001960782c0301d0b0060302040c1540c440d1550f01c0001c00384c07907000400742404801e0340c0c4994062800782041f10b10340c0c0c2d140103c01d03228207007404000c0c01240c1011000c00055181c00028161035040320b4a0805c0c543e9540040c801080c00403504032200e8104107a409407900f8108414200440e5920007000f4591a10002c03c0c0c5600c41000d0540589849150420b01c401c494002c0b6030050030003a012590320680e0f00d854035170302d4000115001c1d0384e009540d00c2c1400c030714210007914281c0c2c1c801421030f15500b0f03c1c0d9460035016030850300c0c140780400194015401c027a106001884000c0e010309095501c5281400311981842c00581046a100364003400600105500009540750002c06546035106600c10748400350060 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 819831672 1250 819830422 819830443
    0x6010c020604350a0506131505090109030e0103060609050111210c1011040e10080d0e09010f0f17011404060b01020613111c0807080301060f05070c0303030509 70
    0x1251031444951020001d00b0801c20b04521061002000c3d07000c910b02540c6420126101078400e52040020541186105001655580c800c012050000f0102d00b0440150741045481103401c0e55104105014907402129100115409103401c0120f01c0c14410050b04410441c01440c1c100008084011258442001210215012407100d0201c9002941745c944455114101c2e44040b8003807514507942845190262803001940c4405080c2424141100002e680c01c3c001d0050300e1181c3c8004001685c5101440380c00401c5580d43e907407900c4d0803080d509124822a0681c0310814400728807000b0405028034426110070b0341c50000042e400720784d035150107601402058001544501c011030601c81041041d501041c0010400e800307441d401e80d14140c1441c81c00220b1031010384080340e46080612075241070020010040d40c01c2c018924412507035181c3c440143c0100004903001280000144411a0044003261212403030307203442454406507990324200c484107071000a007410389440100d0501e0308144000d01c02c3c0e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 819832922 1250 819831672 819831689
    0x30e0d0e30011b020d0f050d05040302030d111e03040c09110c0106060203030109140609040809010201060b070b1005060c0a060b150a180807050321220306050c07030806010c020604 79
    0x80c483c104412840c81180302008001500c0740140691400d402a4608501807600707480f85801c10f0f1a001c0810702070a00200203c1c1107001c20400006188100d2080f03548581c5003003821a1116039070f190f400341c14003074200c0800e10207106000308400a904da950702400c0d94080321011076691101054054103000307000000790203500b454000700d1125400400756048a0301d0707040074020203100c18800c1400c03074400d940c0b25030004110340010f00460a0a002400e42501c1840002260391780d810001d111a0072109048131151a0003091040700c100e081da030800502822143c0d603291080c96441c041c0e0f15074048100402c00d0380c466848424555030001d912040741030354226540d865410351401410054004842201c940030b070b420102d455400090b4450665002500a144140c2d000100a2247c10351041114640f5010003403258000400c0071003000b800ea2107244007262500b0b5160210a840d4010b106c420840c405004001c0400ea000051075042142030906102c203044074008a001d030303c5560030600b00e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 819834172 1250 819832922 819832931
    0x7110306010e04050c04180f081908010305251403101404060f0614130b1c0506060108040804090203181c02010b03071217070210030e0d0e3001 63
    0x301000b210407040d226034842d0742502e0300c00110804110455441e4500d0b41045550b800380d1034000b1320640d060b03070809405a01e202d804d1a9245000102c503d4143c140100000e1441004200308101000154807081005017044516810030b070707001d412104103208011280000d08400340750750700c0500007134100400c400310600c400400302e284450301c01c000f9202140d5032071030000700c81c09a000c6481148155041429441c2900f072043c001c1140701888039403c0aa03007942c6a005071881e41d5260000f14601c03880c3d103a402c0b070101c0300b801c2403414020000c1c003460520038048208000144c01ca011a400d6801c2442c006171a078550075086a5049010f80032101a0f10076003440141c543d803001e00380825403440da40240000385510047c140c440701c0a20850204900c01110680021010b147d900c21000b91038091504002d030640004809920030750207100440d5680b03c030a41418001d0281c00030440c0c0905240c000322151602080e11894610340c1d1001135102c141e41403c030341d15212416030f003a00280000b442b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 819835422 1250 819834172 819834179
    0x80d02040b0304110411030a091b08061602010b06040302101806081f0302100e0d15020d05090105090a02120a0c0f09050106140d330602010509030c120711030601 71
    0x101c00e40c2c000d80d0103a500030842a69116a45440c2c010541c0c50300948600a081d070310780c00c098401070512241c08603030345150644d158440d002250900c01c02030081d94002c20540c10b140c4100c0c51641c0e03841e0340850440e4108840489280c903a40c0845040382da040c0c03041d0440740d410700e1080703460303407078014880c442c050141800090441c5c1c40a00c450051800c040d44055010003a89401a0a42280f000030b42082085043c242c07000e004400e21016a48064032801c800e00156442da406c1000f10f4010b0010b0940c04a04980c5140c902c3c4101c0b503108141c80001c0140342401d0001503a2250b42d154001e01c00c6205203903400d642c280900104012541c0b00890351001920380100003071546d483d00907114010310703200000070010312800107044d00d01101012140740c5000d0007400300203020404011107030019034036507101011005644101050b007002100c1041b0030f040070402400d54001030040c02c000e60007440702c03620344e00380400c12222498500c4105170703550895140c0081c4c9004524103c3c0c1e8580202070000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 819836672 1250 819835422 819835439
    0x1e09021603020d050405010e0906060415030e070f05011710120305070204140f04060c020304180c02060c0c0d120b060a050304030e0103091121010608071e0e0f04080d0204 75
    0x21040e003071007034003510705000900308100d405000c0c1e0302c55540060202102c0300c25a081814030182c102c075020702403520703203a12000c1484488101402e085d001035540e10f0428190081841611f0140c4010342c00540180c1c03030400024035504c0b0240c441c184041044001c502403115141084008240624014040c54624100a800e0360814a030990013076090050108118043c401c0c60b61068680107110001e50b2903613180c0b44010076240d03a007034055100c20080440c0e40e45404581460350100148045107203001b0281c02414900701a1140e22005402d000d80c040d08500420103510310707921440c201c0008184090b00310040d0540c00c610b00c0c0c000344001a120302140d0321100441c0f156000b91907001d2905031004c011400c84210790b41c09040315541e030011001c1c91034100110074900118004184074030b890350780e800d400c64015600221170740e4402030040000140c00c070821000e03000740000c9040c8540c0303825112003441400902c10100e40e240c560000d030400c43c0c03007029945a40e040c0c4000b1522151295401e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 819837922 1250 819836672 819836707
    0x210020f060109020c0703142a03010b03010e0c0123071406180c0111012d1404020f190b0409050117010c09060305061206091c11071e0902 61
    0xd40103401144004a010f00340b0f4021070302c03130354150001003040313920707540301c2800b40c4004c445154040d00810101c4480e500c0c0702c10808003031210041b201c5441070125070070907013141c000034012170281c4d04000c0c000141400c080303440c0c00344c510b00303007011042015400d0310132102012000c1182d016283c00b1540b002071011103080250340000000c125003035522255484087d14060300080d8130144e10511140001b540305001000303060013407600114652030003c0380d000205e418841c118a403081641c422000304c600720f0085031200c41c0e0000c0d0215660500390082004c654482c010310f8000c120407214504a0070360038014800400c1040c01c955141c1e5201d4240c0350107800300303104244130101d8a214140d04030780b042c861102e140c07440d03840d4114002e24240d01503025203c0145100c1c0d120040c021071541c27202c1e00748003140c0b0660000001c0c2c940c03401308004100100250084043c2040300d126441c0380102070020b029010341d03201680c1009840041c4024052120407600403445103400400c245c0044103c0d04c45 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 819839172 1250 819837922 819837943
    0xf0e0604150c08041e210c020108060a050f0f0d0f050703061a06030403030b120706020a1b08030403060522060b0306061207060c11040509031228050a0603021002 71
    0x81c140015165048210340e03410068402400f001811040c040b01e444081c3ca01c0e04001d44500c1d0240c0d03030f0013811044183d00305048600000800c40d071900c1d0200319a40501001c3d0b102d00c044030b141d1011800c1c1808180000c0c0000391260069001d002c0f0602160744880c203500e201d65020301031040c0644245001612003101e44401c5810500b482010f00308c086004030711001d14000940f025066986036201200602401409035400c5126040c1414102d4410301055001c0e02d80f60300109101691440c145081640807440e00c80300c010142c1050002800200031a0112500b041d004644e627221b021025000b0700713040e40e0041c0081c26410300d000030041d46030840c0b64440b0080702511155960401400460380401014501c030380c02c44841070007514002e0811005513030165004c0040183c6040220742140d000303440b003650301d40c001b140f0303154542540340c48190700000078160500c1003c190000c001422502240c4940b80d1920340c5d0001d50703c44490350081008640060030b04444020000021313460b03070003115 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 819840422 1250 819839172 819839213
    0x60507052a0f2a0108040b06010e1801090204030b1803040b2b0e1507022d0d020304050312090a0302010507021311030702120c0703111504080d030e1f0f0e0604 70
    0xb480300084d030050406611903a0070082011a5503198401101d4114159007aa94862042c10400c20490000c68500d8040c00714401d005035201c0c1142490f02100704001c1020040000c600c60099180001100340e500300c408500d41d441d00e070901242c2030b9050300c004121a101c50002c000c0082d0b0080b14580040501400803401e4071220051034002c1c0d00003400c100e402001603400740c4112209420a0500c490045d0145d00c3c3d41c0c1c046501148a150614486400c2000140e001040c244441c0c54207000051070201c09a102c81d2401b824580418014041440041d040c08004501c0c0c0065488a0704030800e502c2d0041c02c1000201011449401250000e443c00b800510401d40d680520240c618200c5039034038a102e0007883c0561842e40c45c01c1c0d180da20160126004102c200b204440c09a10324050400703051400040c04500c0c40d0082d0080441c1d0301d4115401485d407200b01d20034074110b0100c945003450000d220005c2809403c140741c4c4000b4250801010300c1d02d12501c410002404154910000c000c0301d000e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 819841672 1250 819840422 819840493
    0xd0e0703110306100e060d02061207140c12090a030819020d0e0a0308030703140112051516030902010e1008010302040b0a030b0f090a0f0807060507052a0f 68
    0x3907092503600c1404569502d0614110081482411313030040e04c0540c05400201069088a416030224601d508215800b0200e0000a818000d040e03402603501b080300744400e4403260601e0f0042c3e1961341d0310614008800c80101300002e0b04456900c1d2958504051504150200c2e5103010103c00c81d0120462020800018041d659074202e0740c3d0b114a50270350320321500804404405d820745c8c4600350075500242402d0103141d5943c0000c0101c7c2102c1b000c6078000d10400303a1204e8002e58904004d41007a02008001101c3c0c407141040004401020344030104c2d8140394035001a0a15483c4010b813002d1070791f8403009a0048003541e00c01c5046510a00e030a040c1e0b4402c1d1000c1c00651694010300c80c18800c04d000051850f5092000550104c030059141948213001604542034202142c0304c6134400310305181c041c1c2d2030b207400040d14824031450780141c0d500002c19181032450080400e41c0100c107000d60f800000907003021709400d4901d2820403c10206034050410a44207121031072058074888040f11302040c001c02012 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 819842922 1250 819841672 819841703
    0x80906090102090a0e06060d050412030b0d020a150c020405092118090408280e0910060f140d0203070906030b01121107061109040608070b04060804080d0e0703 70
    0x107000369a540c41002d080004c2003800c156800c3ca201100820851f04030300d080c040040408800d000d40750156004040741058070030000d400034180c401038082d0600941c40da190080060f01c0c0c0c0721a01e000c8400700c843c4440201c407080c0342144c14062041d0b010b076102c3c4c240028011100d1000c2100c0070891503805001c541110219962400c0d402944004404501c8108a004240c00c082d038003d5072091060040ca0700c0c2c500d0b0b00c003040d035014004104649100d00583c454101c002c1d040302c0034120600301212584014540f02d84c01c20f0001202d802850300b080010707409848410b014085480e02d04840300000c98a8200c2400280d0082d0070407243c0c3d0303000840c442e000080c194064842d030803814070706030740310140b150428002c0d6014003030508032070380d42420811161021540b54841e0000c004201070f04543d82c0d80004042005440c03458004403080e40090400b007004001c0101240c044494134189004103660342d042818040c050703912900c4140d42840100b05200c1ca0102d11042540d100c1c80000108984 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 819844172 1250 819842922 819842941
    0x20301090b091e0a2a03080301030204140f04080c0c130b01020606153702160812032202030f0718020a02030d0b27090106080105060619180303080906 66
    0x1030110030f010b00354100264050100d90040302040401030318442440d01328000c82d048069001159006817120342c4080010710851505005071002c003202120341072441d0400802e0170700c009401420050080708000b0b0301d1103140c0c60900401da0345040c01008481200b8a440c0a18060589a011603005009901c0001c1c0989014000d1111064880001c1400d00d19000c1007441d00c03007414040c2541ca1174110340b810031001d8481d100040c01404541c054116080c810561225801c035941085d03c454021100b41d100411840042e60382c01810020801c0c6c1d003034029400c01c1154680100040e4160142c05090540c0140001d43c0d03000b11142e00000e51030324007202004000301d0140820082c010f0308204400b00d141c2c0d8079900846c0803001d0040915000d041328a4000e2403a001030501400c40c0c0c00e650b07081103c6d20300e00303128200040050b00024801e9140180000f501031291011090f81000c0200190700900d2080741141116105440c02c101596124100030303004500c1140c002c00349216840020b00d0186 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 819845422 1250 819844172 819844213
    0x723100c051b0d02060304050f0706090501170c0403050703141513330606021605010e090a0204090207030c0b160e100e0d080a120c2a020301090b09 65
    0x20382120180100c80b01c100d4001c01941035810090b07070b0090030440d24a000d1380e034640065016a228000605010901c0b8400c6c6080c03a103d0b6000c2c01c00d0040301c460400c450713600001e205400d5450001041c0f040c0d030750601005454000c2e40c0001d04280320b00e50f00071040020210040c0c14054030303030048840702803990b0001800302104959010440b0600d40c69400082c40b018200300c01c45900d405414030f2484070078030760040100d00c845281400c5855050030444e441e018807044020486c0c00c4903840700c680c10400003a015841e00030006d8090b20172000000d0464040b0f5040c0c034040c0031111415544c4051034200101560b003a40c0044d00d21204040c042140d030030341c00b005000c4801441c0c541c00f60404510007004005000c5000711418010200b050907580d903141400014000d1042581a403203841d002c030b0007403045440f12825402c071031034590280700d0315402001c14103041c400c40100b5041c00c1d640201401d008403030294025055070a05d08000c01700034a0420051051154404481c45031107003271491503181 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 819846672 1250 819845422 819845447
    0x4021e0a1701030507060c3e030f030306090c041d07140315060f09031c031508060402040b060904050f16050a081911040b0d05130221072310 62
    0x1540403c1c030410495000720071f0402c58070b00511010703038102c001c03264442c824148400030102565807403080c1e039518903a000f4500356407281607005103900c00c0c003800340650340d100140c14070740703d29007007000070355002651000c540103801c40782c85072a41055a00507a80c1e42c81002e5031a00302064070680b1004107080b000d410380744210020f2100582c020300b00b0061002c2035111b502821402141003002c0d4466880401000d20b0b1030003103201018840300c0b4407400a084521010710300d419000712030010807081000143c05034000d5011200040c4e028440c0e40011910b12407c1d100680023414402000410a03072400000d1180f103603032040c64500e91020310100c455114200b10b400214440c10041505e0380d01070202c101e042c4030400300003e0340300003510030410241c10941c0706901740ca00009084800b0203090048980001c0f403000b00021215113030b400102a0346614950880b00440c41d004602c03038040410a5000810f02480d5005500d8020615681c4580442120600448042e406085401d00c80c0d0780983d003a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 819847922 1250 819846672 819846683
    0xa211407020f040b1c0305030109050601022b12050a0906150b04030611070c180c170105040e0709110a080603161206020903010f090b07090501021b04021e0a170103 72
    0x522412404220082c110050105d41018030700109404440301ca41641c05050300a4546503282c2d07142904081c02da403001009541150491210032a02c8408041039003042040d0714180c40b1403070601d00342217a25021349080d003514113090a061122a21041d8001c01006008e06010700682c000300038081500300707440c130456050a03010401040491056403010300c076946005401451b00c88c0c261a100a03402c0b658000008094046903030030b40607d050710842e000340c03d42d4101030001200c204010f04440c2414400c0ca40219210a04451071180502000c00a4009200d0411202e47c10071151002d0350499411100405c2c000c42c0070a00d40e29001918240540101c0c003100300050505141e03e0b1180741081040b980c058091100c11003030740e001c3c081c60545007060103000400c0090340c03c206100040207442e9030140251000e007401399981c0880c2d070110540700c602444032191090b070b010070003c4c4200f43c02c58006011541040d03170900d10a4005125420403030741c2e0082000200116881024000e220081a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 819849172 1250 819847922 819847939
    0x619060c06020d0c08190506130506040b031b04110405030304062a0b060a060f080402060a090f0b0a0e010216050405041104140108011d0604060902030a21140702 71
    0x400e00c540914a005441501c026051012184145040da002500e00e1008948084200110002241034030101d07001201814080740c202200030902c00e0740414000b640b0300f07480703400003002c0f41c8860300310900610001d000c8800340b05201001007400800500b0b864411b5003001c10f0755514194030802d03503065a10080182d0700d0300b0300c1c3c1034041d1000f403012461009402c1c00309841403442440e000d0a00c60082c000c510070362041c54210100201001190000c8043c031100084000c00350750b1188941d68410741c156030705690b807449043d01b0740b1070340990b80c410340040e11600008100c40380058041c04c01184942c84014840504d0001680c5810030700000d01d03100d007601c000c10800d034034183e04080d80041c002c95480410603580c10214082d100f1200b0040841d034868001000012000d108103c1050341a245a94400c2800002c181d10344034090000341c00c81d0f844061100556806000c1c2100941d400340f0104c1c114988000c245002000031b1605901090405840000419000c4102c880041d801007902c034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 819850422 1250 819849172 819849179
    0x1c0b0a092109053f0f100501091d0c0d14070b0706050604050403080f04110618030c010807230c010c0903050d09051f090305160306050a1416050d0204060801030b0619 73
    0x2e21031070003070f8901c000620404440c4240c164082c03000806c00880440c010400358103000300102600c6201c0d41c1c03403a1003c048034030a0764244c800700c5c080c0f5050508407004040e503d00c03410002c041010100c944041c901031018002007007042c810052800f544182814496680c03030004110890f8400c03640680464140300000303031120318407038929602a1142107000310080003031001c02d4540d004900c000d110241d000c5031040207450100000c211510f030920b0b12060a280c0080c0042101450040f001020440a0070710601205510155541040041300801079042800e40052000c403c0c5d02c030075581c0d4015580c2a5400500c102141416214060003040341ca4050748510314010301500303081010481980300100c0068014088000061000300e0ac0c00b9030541103081c00421a1409081805154a0913003039071032400d200c905030350303002c0601401403045142da154141d0f00c91040c40030b1010424800500891040d03000042e0074141c0340683c25803466665024113001541281d00c44560b0303001000300041 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 819851672 1250 819850422 819850519
    0x1103071106160507030f02030f06010b0a0f0507020414180106030b0f040f0b040b070e0402070f1410050408033102150c010213051c0b0a09210905 64
    0x9202d40400c8502d0304032002c200352105400c000003500100c8a56444120b204198039041009644130144400034001d154503201c40b0010a1003040024814841ca03807603070354650b0380100b040c1c480c81500075205210590240d80d8841c25141c04850a6800900404d94095280780510400007500e6101c078412421380c9607401468030720080140202e6442c4808030700b00300002c040d485001c0c080c51240381c003040c03241041e51010700700c200c80700300740c901451041c0144004292007251071610187c009410301d810300c40151005040ca028841224589410309040c0000c12400c00001c40c8242010300000c41c99801c0340c8080d00142c00790464402c034000e00001901c0141c9000500c20702100a4000c1007071070460703106030300e0342179801860300aa03451141c4502080181016203c01c100d8043c0503881d04440b11040d9551250340801800c024401a51401d00b001000400300740c1c1400308128104080710130ba02260004d01a80300c500580f809078110b140d101c15401c10301401400000351800400c0b84a00302000e21 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 819852922 1250 819851672 819851677
    0xa1d070c0f1a0a050106030903080f0901110307050a030f0515040e0c031204050f1f03020d09150504060b01081b162306010f0605040611010e0303010909031103071106 73
    0x6071801c8401c249020006428041540aa4210384004054919041d4a110102c4805030310410505007484c0601000030762003400c840d03002541018010b00d81c2ca035001d01c280144854210750482034000018020030703c0e000005048801d250750350a00c004004d481c1060242c0340190380e19482c000c0c1d07421401d00c0c24034107a007044007660340741400c46000f409402e00103403508120918800c02c0f00350018040c407041c10100c659124030702003920300c3c460386c1500f103224842513204003200c14205540494800903a007103507004400000e07082005c010f0103801c000c80403001840d0a035400c841751440e00010090a5000707050003445001071049602c0320503843c1a1080055002191f05185900b6580040b40021a1440320189811800317000da0301c08a403070800c0d5071a01206800268841813000e204000030f6070320400716410f4a01a2030110311880b044102180901500003515030117020120020031041595848103809501950765080b0620619911540381d11940b0700107010502884024030050070314000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 819854172 1250 819852922 819852947
    0x40f0b120703060510050d15270905030f0313080403120315060219170403110a2336150613052202072001050c0a0212010f020409050103020a1d07 64
    0x5000c61450300c00c8030030b01c60103001038000c0f03002e030703d911200310680200000049c0032640e0102030402032071200391281a0740f4090000c1a81701e002c400400200414031072450041800e900800d0b0a445a499190028041704010112400a0700d8400c1030030641d44901011412078034903802503d0a000c461451800b510541d82c0c0544400c480c1c8031104d41903d100d18001d100039070050403c004031000c2c071400c00241d00c1181d4017055533903555203080070611303089462134082550101c403007080740150381c08140400114801840100781c100c21070b80100842c4a01e5640c07041600f44c0f4010010390b290310030800c02d40104244100d1035070180c8014070032030800301d0700b407640c00207810600030020b00b0542d8a02d0aa0b4000d04c003c40b0201d103161080b1a2a1020080d9080703000b80900700307a8245900541e0761580e5052100001e445860081221200b2200a50040020084190045d0350720f9031950100009000d00b0b200483c041e64200d60009241100d01680c0d01e40c51200005418140d1104082120fa8102110 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 819855422 1250 819854172 819854197
    0x91305070909020f1b030403030e0a3203010c0305071107030b040605060f1306060909110a030b061902010e0c0a0b041a130e04031d0d0206030a02040f0b12070306051005 74
    0x108030031036020780f0174a4103240d0561400070355540e4103600d00246400c00144e44d0b1070190080000900240c02c80c0040c500300d07046040c007081201c841181c0d810182d04140c01580350194a89240392070400e80c144c1005100340640d0312821101010369650744d689104a04c8090300740d0441c0d17000304001844c543c00c0705400500050405251625200000d00307200c0c080c6078076451f4503a907041d08002141c1c00c60903000c0140b81880080142d0003800302c1c10b008a10401d036041c0200742d07941007503208558070002958a008044014030310a14200800a8001c00e0350303000344a850b100340c103c0c60302c40345041c8000708103403020090000d050915102e500300302c2d41d04075071034242507030700c24800d01c902d200d14280803a00400c204464111141850b0034003620603000ca4409821074008046c41d1030b207944817801802c7d540c03076043d02d480e03a5a0744c8a0454400902441c0c010f6403842060002c001200b5114102401c0c0c000d51541c00c0c6690358030394034000e60484041b80305454203c01c500201d10451801a0041d000044120 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 819856672 1250 819855422 819855427
    0x6030a0209100b0f13080d200726060f040f0b04140a1a060406080316020105190c0512121605130611011d06010504052802091305070909020f 62
    0xf01800b203150380000701990501500402c1c100107100300c0a030600024120100903010300c0c1d441450062402e008a840100300e004d403d0401221220b0811400c00103095110307000d08100f5400220200c03c1038400300001c017a00c5801c2c041260b8046c01000705000350391200304d0340400d4035035603140c040d03480000300b040d1071841e800c1748607190110051000c10709040c82418405446914102000c6514001500c7c55010b0391402000303201d00b43c07001080300c00d4402181100d000c0c0c10400c2c40121340c10310500301c030000d116200707800512032941c000c0c0700100010306c60401e072141000340b41d980d000c00c0c2c065441c45110300d408407004641c0104030001c0c240d0a00c1d12038030700b80380390116801b00c085011202e0791100c40040c0e020020315651080070320880b03004da0048800501503140d5125880c1d96104c043c040c44e44160340d00c5022030841c86e640c00190b181400c404801452040c40c04c40407000a40005c1e4015001c0c129010880c1c01d049264890148101216100c402059040600c0d4070000d4100d03890551103410304 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 819857922 1250 819856672 819856679
    0x605300a06020706141609170115030614130f08030a1d0c12072d0e0c07110906090f040303020903070e0a0c03023a0c05130e06030a020910 61
    0x7640020844a402100c0c003092051184c61075200c0650020100d12654500286500da25540a14944102d0340c0c503024001c140040c08494030700511400c1c118800d4512151400030421116800c1160341d45410810805aa925004900c0030304207004c00081002e4640d491800c00205080c0c050b54100200c914001055003102d6039880400c05860f042c41d51551102061811500d800021200d000b2104070261240740e280c000307101c420031954000c8000d824400111a2465114803030850010072000014100074104049080341c2588084c5003a1800c28002503036005505001002a00841002d45043e100b0341d5011428408050050003c80c101502009030382120f5504005240150203000e40800755410b00340340307220464040c11110020300d4010320901c0591031801100c100640310b0303030048122414013100c04d00c40c01040d04180840041c80d000d600009158801c029148401480c0d0050b56842e84504000c0c402070300c2221441ea05521105030311006041111585030444c0c407130201c41c0d03403040c2c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 819859172 1250 819857922 819857933
    0xe03190215010915060e0a03060509030903240105010509130b0d050f0c031005010f0e040516090209040e0a110d050312071e080411150d060b090102010605300a 70
    0x1e921000c2450b89a81c0071125a01c144c607122401000b41d07040100c0070b60610b001144100c4a240300c00b8165943e14000904986400d001302e605d00360300201500c524100002c84901c01c2100c00e43c9061448040300008181540a0004c40fa031840000b042000c0d03070003c043e000c40140c8040159241c00c241111043c20004d54100101c01c6c003c041e04000d0170f030a909031402c1c14580341d000400e03009041c3c204001080800c0143e080f00301581c0120351003810694941c01c1503881c08050f005c0c2e40c54407446c80d034400a4400115030150001c010120740c1440b20806442030196154003101c0c2c0600281c2909500000a14003134a282d80400c2c814800c0d242170081c15440380c09044030031541c42c2d01050003c0e1009944c50085041d80700400d0450034159280d042075240d00c00c42814040e1014007a640742400f03d0603a40144080d2100044040c505010954584d181d0a1030340d0011340b2041d0140d82442e10100309841d005103140b1030741590410100c1d004072034647d811104010349140700c0f4640034001c0504003098 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 819860422 1250 819859172 819859213
    0x1522020d0507060201270f0512031e1e01170c0910090506090106050405100e031c030f0209061e0c0a03030212010f1d0a1508010501090c02010e031902 66
    0x41c09000900307801450080e0190a5a207004c41021407851007007800c069a0f442d034011220b289030000f03d0285000391320f2030807901d00556803032888020007010042010396882d403034092108468402d41d1901507140d100314008429038601040448000c01001404002940c18640080312812003c54650760f400d10003141c03d4410a0ba002118800d41100074407a82d911801229088882a07480d8075040d890080028042d00503409003a116400c60b03a60300110318401c0700302140c0c00c40024291580514207801200c050403c80e098074012a041008010204103244291490301c5006442e007450020070940050000220300700c01071402c07030207104151b1040010042640b00074441d032401a0340b665218060203006005070320040d06503060820a0100c1011001182001c0d102540c0d00c4075135803140344414014080001250211310501c2c003000510590540065040342c4251078100401649030204038280c8109883d146025442003041d483c10032072202249110303100c240706807840050390810044410 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 819861672 1250 819860422 819860449
    0x60412030503060418031202090a0b12060909061e0408040b0c0f160b0f16021f11010506030307020613091b260c0d0609020c030301030302070602152202 67
    0x2501c0801000880d04040c49489000e1a0682d00e600034805982d4004044190003801c940740710340c0115194000d616881034050150800f09503d80c1c568011030128400b0303102c225902c038840d41d01000400d4a0560100d05e1034050544226150032101d22480110110030002d4001c80d0b001004000c009252121078014240040c010005043c01c0c0508128191600e100b2b42c86d09154101c41c040100000c2503224211742940303818103000c80d2135a040c24120b00b2800c200c260041c1d08685000c60701100e0110854640c04444650b48a03481b2540403041d959003214412188250903500c1008600c02518080025250111400e02c1c801100d523141c04903034041d030b80320880c1a294540c0542400c10a660400c003180486041c43c6410010b00c00301c112100d010520103041805800c0000908158418454101c00090030210009558070b00d2250074240d901d5000b448198018094500e001c260340b403022500e00c82d042d080650004c52500c8210000b6058442c030900700ba8031f034424402003001a00e4000721030400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 819862922 1250 819861672 819861677
    0x30405070303080a020307092715061403092d070b04090c05122406160204150b07151b0305041b120602090d021201060305010f2906041203 61
    0x351840c1d4a00541800c4010307100e00b80c005e0040c02042503055000c602d0b1012210451851b04101600105131149070110384d1105090a051041c035045c0c09140b51600d404460b000c0e039443c20705002903d40740d841e074001a034a220b4140c1103005040901441c01814402030b000700c1c00e424480d0503207020140d1502043d41c1c850071548101260400c5a40050b1003400c00007107140c100310746002c9090103c01d04021001b01000d55141d00c4080600d0010110b210030103c50314090406035a840701041d401a0085031034804030700c00c034102194490310b0000d42e10744104480d4030943d01e606080f9a50741d0465010341c1032420011803030f61216080865000a4100103060740749840004030ba0a1500703200308110407000e00c07101c000c0c2d9204401c11400340003102803918a070300204016110403080c0c0000300401c06900000c1d521814000c1580c04d000f806520000c111b0340f00e44001c00084500701a81d600742c0e510081c42c07a00700200c00000c400315503003a00e4000d01e2204002e050f98a0541c640c41c3c0e41e1507041101009900 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 819864172 1250 819862922 819862933
    0x2040509180c0103090308070c150c0203040f080307030c061a040f050403030c080613020711090115020d2a0f05011a0a05150f0a2d0f0806060d0902030c0303030405 72
    0x540304000e00c5841030b400800e10382448100c005890213442010081d042c2410000f00c4080003040c00081500d4040ba03903404641840181c1c17032160025640c0c1c01900540c1481c681701840043c10580000890301c040b80c0c1511400030200040c0c076208028051456150340c1103240d45070aa80079507852180f0707072280c1c048030400188c07401c150034021304840c3e2a1414906011000301071100e80d60720040016481da42141002d42c1d145050b2804d903029002e00101c4a0b00000c03000b0022452840b07007040450094100c0d42200c1c00d210f003041c0101e6210300040070031805042003c2d10445100758403031020400750b000300c1309171090300c4040c0c1d0b65608440c00a5134800c0c4003002d10610303076100d10302580694010281224007030b1400311a154600e0b868400c1c80d201c0d1070b81d4000020146819070059540c89405140c000881520135a01403404591410035090780002441288504420034020940d890141c0340c0a404036040c0b01c1720380c541100903c40a5404c2e81d041c0701d8888180c502c0d03903003000190f21591141c0302400d03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 819865422 1250 819864172 819864211
    0x91e0213240e012426011706090718061203050304051606081506070b040818010908060703090c2d05091b030c0d020c07050117090604020f12010e0c01020c060a020a080702010302040509 81
    0x2031001e96490614001f681140c018040380c00e00c00902e0809642c0c50b00301003610000c068607108010001684101911031201400c0828190400045d621481c02001512142c81040c0c402e1006820503000b000302050404000c83c10140707110364403034101240942031358078000080c0c6070500c24000407034045a040b0000542050700c4400240003400c50042820040042814210082d4079420001c1040302015903038010201401803058194000f4543c0888140420400d110f0000c020003860140090091007428001502d05080340f9041c8100d10311102d098840c1064030225032281d00241c042c6014038001d0010002c0518640300030402109040d00a24040e403416001501c0b02d0145180310241007440380c1000f50b000004224070f80c4c003e60440d130700c6002c08109800950703136000c2903482e000e0035032902d1501c0c03048032400180d00380c0c525002d800b12000c00001408011042c032601d500c0c84016001090320000140e00d00c400b800c81d03107105040142c1000c4d143d4020070b41c0030070212144010394a5120b910b0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 819866672 1250 819865422 819865439
    0x61b09050604050603130611031303260f07030b100513080102091809010f0507050909161d0609040903170604091e0213240e01242601 59
    0x80030150307882402c1c5494500002c046001c0248116044d80740408040100302c1c4035848040382d0040c3ca80005c0d1a4180303a041c13100c5150505100b00c0c0070811500400094001d481c1185c60100c15641103401c256680000311040d025000d0110014103468140d4004581c1c0c07180704c0c00c044008a90360380c80d1900c809040d0402100d10503801b403207050b40b040008040680f00e900440481c1d01580790304c2186911200d44690052210030b1000032014940018020030325448001000c94840c101d48c007180940b1000c2900c0d100c0e00300c0d010b404010a4203e000ca8060922b0740c00e44000c180001048a400e0403070900c04101902c00004045000640380340500f450101c0c003480c01900701405441c1000b6440e007a9640b1309180f01d42d194113149801040c45400110b50300c0c04246d0a0048407a0010321003a45015140801400792001000b100e08050201180c0c0701e80040b4842e0484800800300c1c1c43e4503086000000710013408217802001c214448040038011040140c0c0c0c0514564210340c40b400d507600d0308802 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 819867922 1250 819866672 819866687
    0xf210f06061e0b03060102060412051611130b030c0d1b080a03021b060a0302070f020a0b180d050304060c0c03051f0e010b0a050405100e0405071706161b061b 69
    0x100040940134070500901e644e000a64560159214071620103070405048165110b0050003626140464503290800810460060f400240141540e51040100a0640c05801d4514401105030503034400c4006040b01d02d031041c54075203c0c500802e02c00b21460500c030b9000c0300031405a005910954000c3c1005010168108511420721510054a0154650220010384103128058041d42050b03000b085200074403820418a07400a130780240301c0c07000035641d10404451904002c2c00070b9500c5d280062070030064281200c42c00161640301000d10710f443e0030180c040e504020361105c2900c00e0b142841e004000918108551400b009080304280200c1c401a04000c09a44441250100e60790501445079025240e00c203070300d400da0b00101c0f40071409a5410310b031096049482c2e401071040101c804103200c180000401d5101c1500c0c088071803105507011540303e140d920442074540c49020310080c11030000d8548620303003141d00b480804030404d005031340c2500c0f040151000361056010010041d2800541c00350400321 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 819869172 1250 819867922 819867929
    0x1050403110f0d14040806040c0503010e03040b040e2215060b04080604030e0111120403020a0e040206041a0702100201050610031b08060f0a0e100f210f06061e 70
    0xb84140c0c42200380b860b40764400740300000103100d01c001c4140000320651042e1005000c4020031100e107460700b130502c2d6a81019511529009520706031160850b804044111400d807280d40e0381651415291980b80618400300a1101c0c0e40142d207060040815480301004c0c1c030905008801d202082488110514211030060b44040c0a0607410002040b10b03100108002e80c0c8203805040030810015a1401600c01e801c0d0410b2141c00c0e4041d2084464019000201030001d80340265440d001494840c5000a40102c040d00e000e0b43c0400240010042141f40001581e040c0a00b8a030040c10074050340d010446038000003030010090307511a01046024240f90b6541100420390745024003a03036212040e11170f20f134203131001c4100400900030b0000b21140c4613202c5008036100c003e001c9080d40d07a41d51180900f0005c00703698000e00c01440a500041058101c10004180c074840030701e000e1041d248100c0c00c105040e100e10120340990b00800300c9000300300c1d50302c58500105004d4401c888524040003d0800708800740c1c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 819870422 1250 819869172 819869207
    0x703091509030b18010b060c1b0405090304170c21010b011715030304030803070e100329180c0903150405070608180102040f0315230a0e03040801050403 67
    0x600400c00300700c203c5400750700041c0c12404015495014103030a030142014240b103c0c0c10600000780042c0b4100002162101c0001100c15030340310760103241c1044140c3d002520408050360060206100505600c2407240c5115018012144845242d00104602c845012313406480384c9600e10b81003200078028042c5141f102c1c424030303020054001c240c44038404040301078429a120101e504075130740075803401c0040307034082c503005003d8980300d2506110040802c0a811a81c07801110305010035180d5501030b0044450305507100e004540c440600004440ca4007602d02152940442914190841c0d14050040140070704100c900c01a42d40d140c0c1000d151822410303440415282041408020201e60040389180a82d00c191500c0c0f45030340c462800341000f0700c500c100c541d18254400180054078a690800d5030741241e200340d1428180c510f81d02410412205a403c0c3d00c0d1011034074100c100042402403040c1903100d02c0756500000c04046901c2d90914640081e08640850380d502c00a00081c580c00c4005030000e900e010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 819871672 1250 819870422 819870437
    0xa1416062d080411011b051e0f0307060c030b060d05070f090e0c03040503210609060405070f0818010906020405130501150315030b0702031201080d050403030e0f030307030915 77
    0x81005201441c003d002500001080e9250412a0710a60a590300d402a040d5108009803950030100d44814a04414014041c1c804040e00c6900002040504c410810000031303600342502a03c0c2d01019042d804810030815a80303102d508400e6a0320070103490400707441e41c000202850500d03005801a00c82d49528070900032201020045900201406588220050262500e9446914201e13285002e49140000101c40f05501000c1d29011210058030070f900c11140a401905c0351818001200e86c1614440700052a9141c031b10303101d0b8021201580c000c00e460354035408848d14003407480e0840d813a006049903800d40001d01000185421081c045551681c06030410155250540100d11100202584400e054881074135014070401c07407610744021134014904c00361a1612020080d142e901075251b80d98201d02d014004516894002910b01500106403a1189040d04585054403001e8040365100c2d031101340e0580030341168905001920f403070341c4603444250003e820184501c803081c48190b00901000140b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 819872922 1250 819871672 819871757
    0xc02100c150615112d07050603040804091e05010b0a03150b0702090411040903200a030206010618031e050f01140c030603100c121503050a141606 64
    0x307942c603d64200031605180c4005081011402c2c00c3c00e801403484108074240307032030b0142241c0b19a20006045012281a145080c2e152003c00440e40810359020740740b020180001d00c00c0d000241c0c4002000c036040110041d82040c61144d00042d14004d801c110311001000c030f44240304075010700a0012011984004c104000d00344480c00040b40140c4502a1098610b00d006c10240005060601441c01020703100380300a9078142005042c128440e441000048d0011000c5441c000c801300314100788641c19806401c1030391030848100c0e40214554031602010a000070000300041041c3d0f07445e8500c0d02d10403a000180395960821a041166201d500c0100b81d04002051050305251813840d907002c2180c54105480341c0b1000b01203403600050351807001307401e41740518840016410500700207103aa4018814482c440100d44251100e032803501c001000c0398400c5003141c0014200714040c15103c181c80d4211060405543c2010034555200d5000b0004507114138004445407131a660000c030b20ba0308100701c001c0f41204 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 819874172 1250 819872922 819872939
    0xf0b0306010305033c09131a060309101b0f020d05220b120609090a02012a0b01060f120501120212120703110106060c120305070c02100c1506 62
    0x403680560445291003203545c65905040007050400001c9289100d50f0900e098030b1441c580d40000419882001031059405140c07441d4001c9805001100784103140ea03803000020b20209401c05408120b007401405410302611007240314030079208407034144508211080b41e40c060200704c2d0400750f11007190004140020b200d5045002c80b40040110640c2100310100c1e40c540d17085040c020340080b1400040090f50680e00c0780b43c20390040c00360408903006a40ca495403840540d95080f00e072002030100312481c01412048038401c4404207001c015060b500100c941c15a80d96911360750981001001c10010082c4002c140d0344030078031790309003c0c01240800141d41007990b0054104011040203114800e803480e4928184802e000b40300070350f07003901240c079203c403c05c4c40c5c040d001d441c0b4a030900c0125032803e50005007a911030081073310386507000003c0007013590641504601503d0024481001d0002c240801c40041e241c3d080500240c01075659100c0382183c40e4501344032006455070768100b0309814100180300452 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 819875422 1250 819874172 819874177
    0xf0c0a09060c0f02120c030708030c0d1d030703030c0308090c1c1401020406020109210504180605090421080103151a030a0501091a0c0910020f060a0f0b030601030503 73
    0x1091414107981d0b00d0039514294038048640c000c020b401840e6202038418034100000d812030b480004600740c890a41d118004155280076840100b62560300001c1c00344611b07800380d441e0103680b03400c0c40310103c028051000441e180c40307030592003100007810f8088004241940041c80a40004111028040a82e0544000b513284403c0c4010560090410720760101045031802090f444013000c2c000a640300c90756090064001c00d01d0138426280d450382e0003800348440300b003103080708030707050303550300c405003001d00740904200d451002a5000884c15a00c02021845644801c03845210f94455191031507000d2061800780408c0d48514a240c0900000c0c500510005400200c0e4016581d14103100040c00c0f000356074420040c80003850700076014007070108100d080c4541900035544050041c00540e0041d00c01c50f4109108040c21180d41e814185c0c1442036600c1c0d031900017a5000003105034030451b04034406460b5401d081010503100005100c2d0f442c0f0303850302c48180c107000301e50000c04120041c1c039080d13140d40c4a0a440e803 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 819876672 1250 819875422 819875429
    0x806010b090d11030f01090c05030c0a0e1305030c030418060909050c1c1704032306070e0d0213140c09010c06020904110403030c1a06030d080703020409090501050f0c0a09 75
    0xa40710030b0010f4510761001c21425100700b00c88002170042070103e0406080c3c0b040f0501482c0d000380034041c4690600c1c101742c1420030481d400c0c11074130103076941d801c0b42159202d804c0c92011600d0380000c00c4586215030b01000030300080c0003640d0080c01c0b00051544050101c9034a507014400c014207103c50350b0080741021131105000a800c1d91000b107030746601b96482c980d0b5810b01c88000c00c0c980c00504041d00c000a100040c10549100d90148501c0c0304c4051a500c0c0300381210109071711f965004100243c0c8103442400f071100300c400040d1084e4896042a40080c9070030380d542001c2900560fa078604c0c05007103000e910303100350011000c2c41a1b0746071102000c00207001c040400809007803540c00050704661900c43d43d000e80712907900e501c6d905031101c1d201d140c0106201100701003601c800380c0c0141700300160a10082064069a40100101011030000c64159200e1900429001c24075900740000a080522809003088080c8900b000245516007019524442070b030103441c0c0e8002e80c0302840030401143d006003440055 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 819877922 1250 819876672 819876683
    0x30203032209020427050123060f0f07021306080705060309030705060103050d03140c0a0804030e0a0f0f08030304020108010e091c08041101110d030f0e030c03040806010b090d 77
    0x1c0a140d081d841080c0706050748810980c9200140000f440a0b110300d206003d009410040182100d00804920075601d080c00f440c00c0d00000d0350540b410400c10741da200294400040c00d02c605011006c46c000440703400c9075000d1422858006180b00c1103107004141210a101550001c014282c03d1185a5a607000c0d070f4091140501c40c000045407400c4010000d494406912400f21000c0d90b843c2d14009131200100303185140030a0800c1021450001140c0c44e0a129135000301900d4140b14130000100d80d024030150007681449000d445181d203545030640c0700c2d4058441003090800b850f02d000384600e500030300d81c0d1100c2d1840d00103205120060fa4415100340c1100c00101941d070082e10358a80342c03810201c00751004503214061b400481030490b04081c030940720314000c02c003a10388400c1d5000151a1a9502c810303182c105e42040c4440710105010703038002e140103414030800059030315040d04030758915446a880e0344140e500100f0f04014801c8200032250140085050706800c149100012889051998034004c00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 819879172 1250 819877922 819877957
    0x90f160612110406050d141e010e040206030402060306010e0405040b100603110f13080d0c0c0b120a051810091106190c031416020108151c0f0b010f05010f030603020303 74
    0x1207199290304181102c8540110200e01230402d01c080740b240030a00a8480c008601d80c10001a01404544506100b250040c01007841c6980b56400c01c0316a600090005062001c0d01801c03034000d480394418035100c3d46c41030740481d102d424481e180000c07c5400781c0c23022040600707001121040c10300d5902664400800810182d4541002c4005141d07035464a80104400784208030740d2440860b0302c000024076890140007030110003034480040c41614883c1c0403070854150300000200e4a01980d43c1c0c0442e9100d002c1440180000400798141400e00f07140032a001c003499158080d5501340009502c40c00142d0001b120300910301900520384440040441c0f040c441805406809601854014080c038440d006255403041d03911041046402442c01550009900154400001895030004040c044804010084c07500c0d40d135440000380c450303502010321012159032080040c0c0b0000100c25001d9180600038031502d02d202903003050001013148082c010300808050902c00100096180401100d0000c0300c0300c4010305 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 819880422 1250 819879172 819879187
    0xc14030102190e010912030807110115120614062d0d03030e0f01200702060d09050a2105040918120e032112090f16061211040605 57
    0x240240109589090310b0122a1101c0396040e41c000e103880458034090300c80c40107040d110300103400e450b0f0007004001c0108107202c01040e01c99000384840b401015080b0000320384820201d813290805019030307101002c80d86090207528104089806020401616410141480c1c41c0680000700041000d50b0808a6005d084041e424850720000780720307508400190001660000ca071a0041c0180580b40c0032010600070f0540b80020010180a0038885690314204140403410380b41c50702800703600041081742d0110040000c44509030f800d00480a8950150010344026520380c10042c45d103408070303200e503002198111903035944590060300340d43c20f41d45040b030000f80a000010442080c0039021801070402d1072459032504c05150300c4200d1a0641200b075056404403008141503102e00c1454000c44600340300e041c08404400c030440d81c696039000b00b101003110354000c81e500c0c0780c0d42864103d01d82250101054241030003042d0b00060a04816440e03281e040140000d80d02019801c0e000d203001c1c0d90f0402c0400100b00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 819881672 1250 819880422 819880429
    0x31e19080a0609060f0509071e030c050d050a061505030c18010219060501150c020f0d0807080f18010e0d030e0f120708010b0d32010c2007030c14 64
    0x68040c0078001c10a00d0b4071046409280c520503c00ca03442071f0b83c124002003a00c0e20408902e43c1c0d61b0321280d01c4807040c41d42c0710010740143c4088407201d41000341c244240c4603107207498080c0a02405600b680022210b00300082044024101c05144050120800030302401003210011501059054070960309005107600041741088054035036a10301c2480c1e041c80300140200c0c0d83c8001c1c100c40000c107040b09074034600d00c4252444035540d040694403521861541d89139041801c03a41e41e05078801c007181480c00e0350958458640707800c080c0d4000d030020350100b0711406520003541d09a0040d4402d091200c0050811000200c0c5e10700010b800034100200300002c0030854a469411000c11040103041107140c080d03454032242c2c0d8490130b200d442120f60800401180a0412038289140c943d000340f6000e5450a040307040410041c1c0f800c0712482000303009800d01540c498284601c5810f03c1c49540d40c10160340300041080d01407280c503088001c0c9600085001c1002840e1108403104540107802d100d00105003a1002 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 819882922 1250 819881672 819881681
    0xc080a03050406050d111b0d0e01020a140304050d060b03010f02031312030b060f0d1b02060103140a0f061506030b0609040b0607050105072714091512031e19080a 71
    0x152006c150b00424501c0c061003041c03461b000032124290469180e40780c1f9400480360459402462809a0000c10010003c41c0e80202c01002001c80b0b04102ca24095840f00400c020b80d9244000307131303501031b07071102070090f20720f001e0054100d01e0045420a40c114100964024444402900010b164000c44020a80d0250081d088690400c00050120703407150307005081011950b100f140410001490240c0102c034046098119030603c02444e4010715180c1e00f03560300c03641459140b0841c01550305c40c00709500c000800407418001c410340301f07110100303052202c04440301c0410900e40224040c1410841c40103c95210201a540107442c201c0c0c0220b00c081c144008180148558040607026500345010070481c5d50300551054250000c0042c50400b6100b0188030001b16040d60140c10280e41318100b0310798080ca00581d4464114603200c20440740714901d040001d028410034107425646410102c1d11607000000c0350313440030805a5003070b00ea40c58613084545010701c80c10f09000c1c03402031002c0000440c11980c8554013 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 819884172 1250 819882922 819882941
    0x310081e0d08190e1f0204030506010902030106051902070b0403030504170615100e040501031109090d05070f391703070f0f0b090336060c0102250c080a03050406050d 73
    0x2030780285c00c4d0107102d4503406548540030503569441010300008070b1030301c20720071241210083c0d40c13a281069812400c0d0080c00f00c003424002c0440c42810340c0801c5c000440300c02040114443e85500c1d07512441c00b10180d5044100003543e00303ca8200c4420822561151507147e110640d0840b6810006002528140c9046420300c1a90342c0043c60f0400100400482103000054507034112000c3d20f091b40d038484e0007503540002d98001800205d091040350001190b414203072003001c5c82240a604190805a2269400c010100c4201d0812906441d00b9020b00003080c04800900041746003d41000b08c820b1856680f40b155030b400802c0340100b6001c180510103000080e603501c0f03a106110360500d0410000840e541e4201080c00b0149900b820082010205030701c944400780906030340c6210200701c0d524100001d40c0c00c030080b11500c1e95000c2000e18802003901c0d600c2c40203c00f240062581303031545030822884d01c40070b81d002422103900c50009000466088002d031011195186040355448003101c01c3d110107044d51a1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 819885422 1250 819884172 819884203
    0x6010906180e042a060e0f150309010c0305010506070506010311031e0105090706050301081009050f0d080103121716020304030c0308090103050a200310081e0d08190e 73
    0x30140700800241c00195030b010341c12113400b074820111900040c0c0c1000e600c0d00c100e0300410380f141400c443c035050040d0aa540c88400508800010423120a40c001941c0b0807a40d001082e592051980486905442001d014003010380d0040d013489040d030b5409964400601019016500b40c80146045650070089080442e0380500c82c04401c4604124950181c05e0580b001d0041d4010100045482842a400d0760b0417034030302e00010400340c4402d0458900030910340400f0f03501c0b8042c0c04d00c4811700311001c00a920500480e9650140d4070b6241d8203000c075518542000302e81c03c00001500540038038144101d150740022041c10181080c000004080e4907504c100c0e8401000130650303101c0041404108000f600031114281c805010b1036480a0151007101c20744c41c62461022502c6040c0d40c0004e883d81d0255074001d60000428202d00e840c0c803c2c02d0f1400d603620951540c0c0440c0c3c848038044001040c025401c60801d80d00b40840c030b505100c611240204030006071406001e03034134059054080d03c02c00004002c0e071002c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 819886672 1250 819885422 819885449
    0x6070806030d050c01150b0409050106210b0102160b04060e040e0703020915030d030e21041214070e061002010506030d0c0303090b0c0a0315031a0c0c06010b210601090618 75
    0x1000201f40c55082441203100c2d040c544000050a1409515002040040c0750750044c0145206c500071801421800030700780c1144280025004901d0080d074200703001d0600303642d040e0349503403800700020601c0c200c3e0720941d40108e040424000413514001210410341e0707130488110f00030b555130502040d149020506c440d58135104504149450a401d130780220f170070050f2042a107d442e03801c83d0b402082198400f00011080000300001c001c81002c600444002a100321140130b0114202e440040c40c02c1c04981052140a5008041c011146803d14803100d4404041c0001e200034588440040e8070b40c49c0424070a0b0500030280c65201c10540f01e64003080042d903002c1c13144000b9080c0710700c46115642001c500c80c00801c1c81c0070b0b0320701407611a042219046951000f0380c2000f00f6403002281e4a0154003a1140c1c046940621140801c51420301c001c6002e080a07240ba192a044010304440c0c4460586002c442c107406840280582a6032101800c025113903a420104510f0404504bd8100403525900a01741130100 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 819887922 1250 819886672 819886679
    0xf021c0b0303161506120f031404090f0209030d0c0c03080f0c010906140106020304080709020d2304020415180507021006080c030f121803161706070806030d050c0115 73
    0x40c201307400c5100d00c0600104a582c3d11002e180c1d290f5001500003402d0780c40708081210000b44200c1c4040881540f05c484241002e90b203404030710540302d1242c003061156401040c1001141000c001c40c080240c21890401c18442140d107a440301c0070b64038080500101000107592050108180440e16035a441c3d800802c0050010b04040707004010441315a07411406180002840902c000107a40a40d128040a0140e091814a45100079840000c0218001d5201c0b00241880d40d05004040e52101003404a16440e203082d10402c400c8070b4985800059211404005018400502c840d0300301051050f800002c141d03e030b6000c160f240051513119410f42d181440000314001e900402c11500f40c84003542260208002d60a23034a44440d070b1883e0b0a01c80d00c82c107000c81403204400403240702e186a405006d85524080c4804000c0303c5111507001442991142c070381c1001c54500400406511280d145080790b0603082280c0000d0b16951241110820070502040c1a640340c0f1f82940700d5501c00340141104449144d9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 819889172 1250 819887922 819887933
    0x120108010c02070e15010809070b0a020d031b050706020702010e0301020d0204091802030a03051b03042309040305030a0902040605041b080709030b01090507050904050c0408010f021c0b030316 84
    0x8403040704005000e440f200183e40140300d900030340a40144098603090000130170044600398002842d022080c42102c000044040041005007a601d00303e9010b00b1015851100103416204194028410603880d20592a44150b00c41e00340e6107130320b03030143e00940d89501070b0004075240c480094816525510000e41410039030703115070043c02180c03d041002c2c0310900b00d02c120070042280200c40650140c0041b507548002a101c1c1c00180f0341501117820803400603580c1500f8601e10303080703030f082810303e08034034200c0020b005000388020310170070303c1201c41f8091407600365402002da01010b07000c0ca510303c3e260000c5104540e60358000074003800029104001621800105002c541c40e408078000c040740030000441d141c075124003800c00a80780c000030124402e03441c0c88001401894002c00c004100641070240e81c1207641c4600546025030480d07c642030300c543c10481414212400d803104001c00c2c610420034160084031107080b000000b940720000107000095100800d095104080300300260030081e6110034100070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 819890422 1250 819889172 819889181
    0x1b0d0c0e01090f0209030c01260f0103140109051203060a1d04141b010f03180b31021302040e0a0203012139030501140a0504022412010801 61
    0x7403550b02d0a02000c003003030081c0d0089101e550001c1da0140c02210f089040c0d940101851851104c1daa0f500d001b00c220040d030344294a0320156502808503071510300410034411000340d000744c03041019000b0080c0703640950b0388035660814030220321802e8001100299180da9030008403030007462070540c28005c1040729071606031840d00840701240d600c43c107500744200740040015403140f104040703500041d03070044903001940d41d020a0b0300c0905c100360329640f0901000100081005900d0301c00d9006201c00e0400190280e507070010f40008108103c0c00b0183d05014034403081d5581009501515580c8074030750700d0340c0c90201a108641084540b030403858188a020300550f40114121203c014074a200b801c202c002010304100c0ba180c015008a540312500b030f24071580458006908a174002555610352030030806100c9480d850751050b689655228984140c00b403c84003c9540706110b04001c116034a003950000b40302c2e4280c40b84104a43c4a1280b0201190310f101041342d4007a030100d281d51300d166035500c00305c0f4080c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 819891672 1250 819890422 819890429
    0x60412111212090c01020307060207020409080a081b16030c080409140103150207110f13060801092a0e181b030c040903050f0c07050d140f0304081b0d0c0e01 69
    0x25007058002003009102203000b544c0400305a01961400c0404d4403120069000500e050384c4c45542e0344040341c00100c003080245007440b46a264a1a03900d0106800c3c096102a100c1041c410742003001111480c0144044400d009035041c10100d12200060030001c2c85030286401200d89549062000e2455050410405048911400440300707440e0b90b49940e90f0582c001c00c0070003010280a620310440a11303200e042800080d07005460f0031004849510003c0070761f4a15440707410342c2d955420000c01403000000170303c170001d02c0d00d07910010054060444081c00070510710451228460607400300720704180d200242e404c2c030a0242d00f1608100300080b490440c044820028510a01c60a4410640f03414980a810340080c0c06403111401c0040041c0103000561000c0803420740340c020410049403aa5a24400e0030b10780d03028800364000819520f01043c5800500e09084a60360320611040021036800290341c0301c581c003095926001201218003007000280d403864010f0911440c1c803004103204141d002d00318105c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 819892922 1250 819891672 819891697
    0x60905070618050f040b0d110a0504090506070c0515090607081503120f09130f0525050d0b220506010f120b010e1e0906060c0604121112 60
    0x90369140161030103a48419101d030000c2c444403040000d441c011000540c00e0801034808a144c443c0301c80011640d540c550300031a004180c2c4242940e480c01c0034600707000640320a9900700026642030b00e51668818000b4a518200040101f2440411030b0900c00044104040b070405400c9013804505180c031100700b00c88a0000819840c0014003a10500181840a10014014208601000c2c0700c5d400680d002c00300c4240491020407000740300d41c4501080326942002d12500240e84c001050800c400e80d5805001e1419900d29041e024021601e103a080c207150700301030b05100e583c84410003401d601030440b0a40d103551154103502c0002881c015203409450404802e003080185503210401541d01d444600307501000581041c80000e405c1c0900d902842e02404141800c00c40100b40700001441c901882045601c00c22200112101508080c415641c114604640250400100402003543e4800041014004010600b0200765407400ba101e10461849000e055841c1c42c600303401d442015500c6601144603 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 819894172 1250 819892922 819892933
    0x20a0203191a04050304150518030c130504020a030c0e0601020d140915040902070507030b0919080a0e100201061406030907030b0c040503011506030c170105010c050c030a060905 78
    0xc600600d41c40012140d40d02c90315142059039806804100050010000c4032140f104203c04203110182c65400b00851841780d0741c942c0e54800050050f441c1a0407100c14902a5205480c00311456440407448082c3c030701010700005503955580002000303c442079101905210b01131030041a120700c481d9030700c0c1c8145001c0e02101d401e20070b5000c0468500d0281000c1c8500d00d00d0074814250035160804007000c0c802d180058440c03c05440c0c1c4048800c9a100840c100c03010740c0004410070400280b8041d2603841030b43c0b1000382495640000440510b08000d0034010100400003c0b5140c060b405150b240c20f440b800036080346510343c1c1290f0064001c20182c040c04a1880a034914194070b8940101124881c1d204080941103507491540c54046002000e02810140e00050002007240d071401d1207203480840301c400c00c841083c1d20300017010742190665280001040b524400f0b0280c000c20141107141141d10a180c01100580726007401030824505858050b403600514000809104080e0466543c4278020025101c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 819895422 1250 819894172 819894193
    0x3091212050f0906070518030106240509130903022a03010608061302010302090d170a080c13230904080403031704030e040b1507030819110405131803020a0203 70
    0x202c005080701d10042c20790203000022041407040006e010174401d0242d442035170320416000a401d491194025400c60220443c503240075000d5a142e22800e0202420180d20704030900f000b05021a0100c015803002d680ca50890008040c42082038240142400b52400001c0700380f48006610428152500340c860340c04c1070404200c002c00031400d20b0241c0c1030740c1011040140c241d4010b401a400009116500121480702000410348140d0950500b5156000c00c03666100d00074006408032002614460f4525000c1c000000b4483c00d01e013004090301c101004d00031a1400320344c041243d220340d80003500d420070425800d0004000c90800a003060703d1003a00e03072030400f8010900e080060002110081d00003103136109554801e084c20b03405460001c901406402407c190703422561529404602d08500250001082118140c1c403010825005024058240a100b641c10003941c05401207008881c0700e4401940f100d510380c0d18543c0803106c0300c1082494610b14109904000c0d403603640c101c2c810b9010303005041c10003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 819896672 1250 819895422 819895441
    0x131a090609120a050313054305030a06150b0d02040f0806041502070c0911030f0702070b070605060d170a0822030c0302010b3d17070309121205 63
    0xc4100352020b42c0d400d800d40d940c1b03488000d81038800c544203641c2402000750482242248a00740c0c80c5c0314a41a0218107044076002001d20190b4604100d060001540ca009000d9070380d002c1400d0446980040740454410b062203e20000c24806501261428030000780d08901c3e0001500944100c512100e07603040030b60b548031a019104e00c070841d00180242c1c00500e198841007416405851024007803c4085401903d07044900708a030801c207604031311814040200020550802d01c4254032200d18805030481910303201c00c50b000c41c000d590004203555103400015074a510b40c5182500b510b50800000c1003061016048111b45a003d02544000201d11400140c0e2080c0900003400e1110800d08000003080615141110384502c07100c02142103540b508860030305951801804005040d038000c5025146445000078a42d40341c1050304182e03101d1b42901d40021581d000504441c0e01c4800c1d044024080c0e80e000750031030047c40b40e800c0c01081c0e0f210f410440d0158030b5100d42418200461041d0802a03a228803412 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 819897922 1250 819896672 819896677
    0xa05010f050106200111040905150102010912050c0c1005041503061a0c03070b0f07031a030303040308060a03151a011b060c030e0604060203040218010e131a09060912 73
    0x1908080b6400450310380c0c110030305040e04c0e40710f07001000000948818001c0c101601d64002c1c1d014090103500c07082800030624001c24440e81a071824002004a4241e07551a868580c0d6080c803840309124001c9200060441d080c444152031120091070800110300011029015410900891b10008421a4034019140c00b910615003500d265001c00740300f80b010400301080030b42c0444c110300e8040c0002e0114100203018040c00500644440006460070303c2c1c00c04008003120182002c1d181c800440c210501210b40300441125000340d01494061a99901e24021400345d010540c0000d007520401e286c803004849007a442051950351142008005402860044500400c10040464500c00d000d0f80f00d400038100b544900030042580c24086251300c065484207040c010121400e5980540000030030085107840741d00307401943c02a00c415042541401c0300601521002041e40e40800c40940c81d500610404000450f1000011490302207145881050301e40c03510426241c8070340c0c0e0720900401e0022201001c05 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 819899172 1250 819897922 819897929
    0x1d07020712031b1a04030f081506030c030702070e1003261b0705060a1101050606030903030a0b040b0a03030e0a0e090c04020f1b1b24030703140106020a05010f0501 72
    0xf90491094003081d030003846061540b500b107607200d4004000c40f0b0384515690006100310700036103840c14a180e801c58083c00241d0b000784040c01602c01803d05010740d83e03488003500c1c2c00151351001b40d522070783c51b00340036454242c003178100c0d80b0340351403000401414884540e4981c0503031784210345000d230111303406940e190307221000758003008185001d10480d00a40c05044800e002039a40310119040760b60303990007090403940500d103c500014072041d494407501400b4012541c11040a4441d140381d403421030391085c0c90340000f82c0a00075094032000032b0182a80e43e500103411651005180c1c1959650300c1c42c0140401482075052406013400c0e040000b044802280c0862088001602a0a2440c1e007001041700030751050600003000c003c06e00003c412011283c5001d4840003003100100001e208a0034000c0391188028512445841510310908001490380d01014003451601400750f01d80d2180c3d24160f002c4c2c0900c0c0020b00340d0000010000464070390010b59801d005004100030031a5401400c88141628002d00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 819900422 1250 819899172 819899177
    0xa0b01180b010e041a06190305160c02010c0c03080f0a0206070804032304030b0403030b150f1603051e0d0c0305041218080312100e0f0a0b04061d0702071203 69
    0x60100031303060a8000f80c144a01c40014003104040e42d40c000f6000741c0001100c91131070180207880081154041c480c407500104096040108c1446000c0004e0403200c084c4402410070208503a10000c00181800c0000030b581e000b0713410b540303440601c055180150464801c0800510594000c904642c5c0503010f614000ca81507078401d002d09407482171403001c0240a43d0701c005000e00421000000c100300d440075500880c801c0c1d0f030100350b074800b003810004030f1a10002c4c1e4000281c000c01c5021048031342803044404002113403420031450302e40d5040554040c01040207103c400003e8824940035004000002c00c0200500c000070001d0402c00c14003142228401c5034010690304d0000303100400305000d201410100009600c10604094a80d01c2403030460b00a01e050f00569499002800380407040b035070020016003000107040c0a680b420f15040c5454079000760024440c5651a218a5801d484942014020b003500410350718940103070031003180c081c0f41c08483e0f002c0140140b81380480d81107110500d0701741007034069 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 819901672 1250 819900422 819900437
    0x20d0e011b120203070b270303101e0305010207030801031e0803130f0c0609081e0d030905030906070c0f0816030308060307030b0c0703091a0d020c010e0a0b01180b01 73
    0x6070b0b03466020850100305442980300502220000071219071155200350469518502c0520f08142c0d00d00e880704a04014404580040c400c02840b008032250480c100d031001c2a86d00da406180300002c007159007880d00007405a5000180c0781040c5900460300c05d040340e1040845015100119249a5406d031420034000d080750b5040010450700c424246080b03412500a02103403241d2101d0765a1000010803d0307010740702240c07420301c00700001c03103050000d6607055803100304003200640202c16564483c1c00c169003030400d00d41d4910080060040c2001070750324040015043c04c1e07450940b4242070160204902c13504025110400000c41c1454011484c40c00a0700c1100094525506651781517800d10801071131305406205c0d404c00000800c441807600ea00801451540396540c40003030400a01c0312a254102800d03420780c00103968444256102202d06980d08142c00580b54043c1000181c09400108042107491140200c01c0c400e2007080c28041e41242c103002d2220260031030707440303003030003a9103804164034040390f01d1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 819902922 1250 819901672 819901727
    0xa1101180302010c1a090604030f020307080702040e0c190503010501081c0c0813030c1409071b0303090503120712140c0711031e0f01050910021c020406020d0e01 71
    0x1a0740044c001c0d41c07280c0c1400c0403030f0840f218288880f05088643e02407561040003480140342c0c00c2030405034403045610107503243c02c03155111036565200300c1c00006e0045a0b500e0444c0710400b024091036558880090161700b2000721100d044100390018000d480c802e5180600020740d50b14006264042c042a0720718a515003800c0000540b21020ac404081d9071002d0304000c0341c0145000f60300f00402540c841d4165494140c00c140b20314820303054070070b140b40c000c905d00418010b03030a4125030b0788025805454103110f0140000d1078110050160310400805500c030110b65031043d5110350000d107210b00900d07030f0340080d5003038006181d1003a18070f05603030b00d160454564046070001d440b50f4001e01c4083d0041501d480da2030403006c0800d02d00a2039800c44161140d805082c0e040310311043c803098120907140b90081c03100b07040031801280c0318404a00b21100c581d500103190394074a42101c4e2100c14514840c04215202d5a0b5084061f485880807140100080c0c1203000c100e0580d8014442e20006408800e94644003000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 819904172 1250 819902922 819902927
    0x61716080c04080106030b041a0613021b0a051e28030306150c02010e04020c032a0a0b0702120c0c240f12070c0b0703180209090a110118030201 63
    0x80a070541d00001c008201c04a81e03030500340285402180b16051604c2c151415040910710030051860140c1e01e0344417001403051a030f0701d0090300e640140d40c90400603541c009030801003207840c181c5207813020a4080d2518031414400041141e840d05458801000300280b80704110790307201c8200003030400e50031040e001524042101241c0c2d104046e071190a00280031521182891180a0401c058400183c0c492046004550780300f030741560040001e80c3c2c2903042c980302910380382d06e0f402996030750080310081075904900204003881010110b075160081d0750000d01c0d241002c00424204641010152083d071302510f2403510b280044421304c52407800504800c0c0654810000607800c01c0b002c801c0150180820048011001030092001c0701454043c103603603200c407450707091506400030541e9080c04802c0c02c50002040d440001a64402001d07e80040d070500380c2d840303092020080c040040e403c0f503410710410422400000d41170381080d001d444510341a0290400444210b05110690712009503200401c200550 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 819905422 1250 819904172 819904187
    0x1050412081012050d020c1c0b0a090f0c0614090d080307030e0706020a11030d2a061a040515010207090e1c0915140403080a030216030801061716 64
    0x1941030740b0696030969411081c0d0714803d40c0c660545280c1c004103240c00e90301e5010030106078a50420380341e800da084c1407803a04610311803003050058200e41d01c20001803420401c50340805002640f1841e945031144940c20b122000500034000c800128008441035190a20044182c459504d4002c1c02603120014543c1c406005400c05400d080070f02d83c880b000c0c2091210280800c03000303885d4581c01003c00c0b943c83d04045085024516505001e03801030b45c0d100318003580c0666456903981d00030301040c650300024011515606901407010b0810761520095000304030313044142c070b040d4150840d1305114075214812100280c005110486005d40d01c54481003000320559001295031901c40011303100d0307081000d01001c0c001140080e003c80080e0b808203080c089040001111a9a40b01c1071501400105001d02901c019106a0101600f01c0710040b41070765005109404940300100c01000000700561280340c040e09101d000c2c080c0e0700216804401c101c01000c20400d0700c600c01c4000c4804075213018140403050b110754 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 819906672 1250 819905422 819905431
    0x9030e01090f0e0604021c0603200607050303071b0c06090e18060f0702010e0f07030201020f0f030901030f0e0316026403150e03070b060105040f030f0c06020105041208 74
    0x190680001c2c0c002287c6138031852005501032691f690780780c2e504135080d204007018901030394440c1501740010004a2000401d40c2e501503100e040c074100184c061890700344400034000f030042001d800b103a40405c45590040140f0100d8800417401010350b22200e8000b81500d0051a40900700c0d80500000340f0300d400302000b03147d00004940000a11800c1c00181d031b0b401c4c103d021036040090703170141c00100111759040100c011a040f1240241c40c0d41100c54030050b032240301d5145490304258991f6040e03207425075a613003c0c0c1804100f0400301d13030751004c40e180c0844a07030329000d000740e2042c0500504a4040c0080318051500881001a0b0170030308900341d101e001d451104458440703030380950308400d44003500401d241c1111200b40030429194003451803503d1009034843d1515603009509000c0c1c8080e40c0300001003a1006180c3c0b0405240d4143e0b18200100c1e924040d607400300c411800d205400000348024107000040700703400b502a004c1d000c5c0c1c0366001a42a100c042c0c4008182d0001c603691800c00c24403c07001c95400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 819907922 1250 819906672 819906697
    0x307030806150f0301050f0d35120a060e0702030405041a0405010b0c060702010603020a060f021005280b0108160e030a0b0618010e0c16050109030e01090f0e060402 72
    0x40390b221080036629000f01d207075040b1079140080117203c1480c00c0c1c04001c1741504100d500720b0280541e85d032043c42052580c112003801260406031011401e03460131240400a80850307080d038651341a0006601c21500945114400038a040008103038002c00d01505485208141c00030b6240034907003424000104402d426085c8456880702c6680d1441d40c56000e928000c00302c00d5075194030b4115131146182412400380041d819689031000401c01600c5182d4404c04545080c1000c240c0c40d003048000742d050500e00003000040c24507000400807184083d00a09004034000c5081304595800461000222041440e1703040c00709203400002072018840300041101e82419280560f820b0800c1004039207020003034441101c0c01040703d000c0040301d05000e00d13600400540a10019281d515201014089480c040e03c0d4401000c00060035804540285101071000c59004008001035100780c100244480c080a504c0b60000f0640e00000844640d000c4280c42601c00c1001d0440e0f064907200c040100a500041c0303400f45 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 819909172 1250 819907922 819907939
    0xf071404120606050d06060e09190215091008071805030a0809030f0105240607030e061605070f080f06070e0904020a0909050d0e01020313050d0c0e190b0109080307030806 75
    0x60b10b4403011042e00317485104207004602e07c0c0c01e0501c0c841b80f102d8010180f1120b80d22200248540c1c10349002c0d00c8a001360180c03141d8400301e555184d40d08052080701c010070b40002505030036103000c0ea0700149092040e8219a51226088080000000c0000c0c0078456940d0690240f120000030440401c018120604010100c2e03c05d001000440c900b580c0701200c1801001c00e1a002112034030003800c880c2c0e1380915003203c47c103141ca071843c4c0e0040c0101510a51040c051040401e820141118428541c808640c03c88102e9600f0b95854205003202c05007400b500c00c05000b07903910307a9941000012034a01400c11903c482c1581c1c11410180700952400500c03d0340d109101450024911100c0e200705072295020f0700180c0107200207200041c042028400d0f2441c1158030401655903014a802180c41c15202c0448161218100500304280c0b164034a8209500e0309602d1420b001400c102443c40407041040c003442441442c1400c4015100000c0d2840f8298568200f0854100002e00c940001c2c1e0388940001c7c201c01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 819910422 1250 819909172 819909179
    0xb010f0e1314010b04090f0203010302061c18050313080715031109040c11010e0c0f040b04020403140319082e03050d03090b180a0305160b0403080f071404120606 71
    0xb16003000a0b03010050440c4000303000e0020f010305001d00c83d02015051410340c034551455020601a1203810035210170000c0c03000001841035002d4100343c00c1d000481011580c0c2844504025440307a00c40603c83c0c946402880c00000c410102207000d80440b00f01002003094810802d105801800805034026000c00c010020503031195200c0c0300b032078101c04a5940b1206241400f0180317601710b4841c2400320070260300401b001196951140701030440d605040d140440c40507150300120300640280d0300000d140c4d0000d0003804a19030320010103800510381080c241c1002c8900b100e81550780720000c2e039054184007900b18002d0340340084000318103042140080c003035070003541c1d948900c4c1c1404081d65070040002d481300139000c00e0187d20b41a40743c0200101c1411450548103c4a40740d0301c40810b01c0040502c0300c003107402c0000040b0042c40303c1c1c100d508001402000d141c90701d802800c1030406c0754408444011400410103440c800c0f4280f0350300c1c0f0303e11300c8041d1509007001c106241c0c85101130421201e0036160240030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 819911672 1250 819910422 819910451
    0x30904060609060f1706040c0504030510020712170406050411210115050a150c0b010e0f0702060f15030a02040e010b030d050a05040e130b18010b010f0e13 68
    0x401080740e5074542c0091030420b2001428640c2c01103141c010045640b21413040b0b504070703a90740c5070010f40c11076000503c0c102d03601c420b60783d6005070b900c09005800b0b00c1401c0400d00100360010001c117441a10b01204961f0f100c1d80644a0312282a20100044890b50000700043c01d0303540b08a4205010303000c05180320901100240c0801c040355200254030540600c4d0703400c1c454003405612024003059000514150608010828480d424070940048a100f04400044c96000d801407441594005495903202c0da115001000190390548900210240c06070014112074030129209000b5030324540100100e07200c004050700004d006040c02035141c058a41004010783e80c51046c1c0840303508003c00031500100c140209810680c511100e1001d1010400c5003a10265203c000c9409442d9291001101d544441c1c0429000d54032070f41300109455107203400d01010740b910911401c94100748500920103912200011200c01c0b08525100001c128032640c0c0780e500b45400c040340030108101c0300300007440008071800e0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 819912922 1250 819911672 819911681
    0x905100806180106150c260310080601050906010c1b27110702031509030904020d020306040510050a0918020d03090311010807050a0e0a0503060109021c05090703080705030904 77
    0x44030640449440b01e8000082800f40100500c203242e800742d0300c43c4083c00040c18100901c2c1d03009003241b482140824002e00c00e1122100b840d107245034820b0312490105826580382d0010302402980e0b00ca4070340002520321384800254403488044e514445803080c6541c41d8040040d103540c920b00e1000c0603440210708110754000c010000041e54030394800803942c2c0041c0b0411220340028624100c00204501c2c000b60700e00041d9000c0103003d1841581c29a0b4502c04294210b014211481c1c0e07201e8000258403040d1701c1c15030003841c05444221070411a6407203540e0100c03031900707075841110707001106503900300604000d942c005807007294040d220800f040c0d250341c0020703e0304035985030450208440101c02c0c818048640c0c1c412070142c50030708200c801400c1c440005041405444d81c00802c00c04850303420000c0fa10703140d401c940148030140803201d180d42c5a0900d48080e411003450407540904070f41c4552110b0016000e024084e20204003c0d00089096440340104c95000c58000d44262000b0000400c264036180328 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 819914172 1250 819912922 819912931
    0x51003061805100f0e010608030901050d0b0a061106160f030e070509010806012423090901180b01020a02060d181407032f100306081615050c070905100806 68
    0x9000aa90354049803407000c40d0352407070010040d0b031f00d400000e00c0301d00f40000440b01143c1d801d08003103454500c12550100075020700150180c0000341c1d12030011b0074642044800400c13801c1c01040d05c500303139204400303015401444a0274500090a40c415402641d01a9008420b2045900262500f058544010403040c12080c0c1c8240c0090b484600100900001d0003200d0724401145000c10803c54644040109600407a0050303200b1070400e078403c400403c2d1400202e078446080a02078040c05d40e941c1840074141c3c101445180551803c0c010b85004135032002c2000b40205034014040b0b400c00ca8448009402418144032008030500c05080040228000c10245080380c50181c004201190070340c90460501107864004584186204600148400c50143d00e05040c0381c040d641201c5880e8918812000350285501c40d20701c41c025044510f03805591003000206984044005081c508c8041d841100d46101e0f07400041141d40008600340003441c07842d00010780010f5810081040c2d07907118450303a81000010745 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 819915422 1250 819914172 819914203
    0x30207231c02030111040b0913021c05040b01080304060203030c2b091509110108150402040e0915010b0a0c020a03200901080c0109120f0f0302061801051003061805 72
    0x407140852400340075904800700880c031550700b440c1c5441554030141c0504d5850310310a00c0144680030489502d64162800c850802100d0300c04e002403224110010a4192000e840305080c4600104100f00004111000c44003c0d80c019482c40d44c420a420200742c10242200160806044820801c002080c44500d4401c5680100180505003498080ca00e04210540c8400250503d040140441e0741c507803d01999410a080c10780b5560b4603225140165149a24480c4d44203201050106007a01000d080c28841c525160840d10550000c036100100c4960900c0360400b1460204001d4010074805c60340030412038405402625082e480340e4070000c500d0f05121402555a01c08603141d051072410204080c010104000034208104514000a011310054002d05100d41100d030400410020689a400750b00d41d00100d580580b0f140c01d1070000e480c2c840660343d81a0240511117000c07030418042c455513005040c45949511314514542d64203001e8015484918a03071900100310401041d024010814030343d4112 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 819916672 1250 819915422 819915469
    0x3210203060f04050112020f120d09060f0f0f0c0203070e10141516170d02030f0a06030c12020f04020409020a0f050a02060430021609051b09150a08040c05010c03020723 74
    0xcc000815541101500008000034408080d41c6076801c20f0110040c041c5a00d00000c0c80d0a8a0021918195842d84654002d030402001c005032020921105000d440d0700061840c0301c8100d01c81040055120340890307030044c00040104c4520b00d1158140340340064807039440030351074410940d0300000035004010010b43c1541c0000400020481000030070307520880140302003080a0942d181c074280c402c1140100910b42c6c22110180f01555203902440c9083c550041083d0f640700e07190441ca801940041c0362060101d0b410080b5038020500075015901ca0740b40590080010740d0f200c0d103e0050b010f00034180c010482444021040500c00d0501f41088220705580043c019804105103a001080349940005c04552402090020b4040b845100340029407484030b40680b41c441140014071400706000440c4031052001415280c00783c0c0061426120700d0107400c42240b030681d10001511210b24400000700141c1051506000c0701074404124141c080030a07001e0609220048046121289440c02060100005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 819917922 1250 819916672 819916679
    0x18010e0a06051810020306010e0604031b06080f06061803030c0c030c010903080f030907050a0e07080f07120c120606050c0601080d0801060c03210203060f04050112020f120d09 77
    0xd42c01840e8200c25601c40209040800c0201c19458901d141c051409507a00000800d0881e0311aa0548030b090784010540d41e03865035070745014401000ca2180d1001904180340d4000384c0b40340101460380c49203400c0140c0400d0745d0b0b2103608100c2d96910042c4a110300c4404100191040d0328100040c01940840b04002c0c81018010000c25140082211803507040150102091001581c64429182c0624602413103e459481f400030a81c28040d80f41c00c46600400600000070745d11004040b0030780070369132640360720802d07407143c0315694104035040355594013080c0240c6070005040c00c02d40c4042500e694600c0d08003075005842c141801338400550264000502c00308441c81240824400746004000d100010000050513401c05000544140316190a1004032810501414000c2069200826030707a2507040d90f091a20445600940083e00c20303034014807484081c1070050078a841800e05840c04800b02c420446984c1d801c012820781c0a400d5540c228080100340e1144140400c100c6500e40d41075205c4103005410b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 819919172 1250 819917922 819917933
    0x3140a0605090d0e1504030b2505070c0b1c020c01092003060103081c060b04031505010302030309040b12010f09120306050604151803030302130e100b0318010e0a 71
    0x1006007810b400e0740c1000c0c40d8408000c0c0c00603211001030a0941380030343d0380800c40100d080940201e07403000d0300e400740170010440e055120764455410707505010107409001c40c04000898150248480c0241410000305040c00701420050141501c4c002817509200f4445800c2c8960082c0e802480c041c0d110740e915454580200030242000442c030382c0b5801c1060010040c00780005e0f80d00c220620016040160024409103070307598102c00f208081c0d5603810140142ca940c0c56a07403603542e05c030348400d403400003540c2041c0300500024040c5c181200d800400850509116808120041800000c2554420503403010340707056503400e001d41042040c40500004403980c880c101000b12040c0e940c102c40405107418001e111f5655070205071801e0343c18240800e0080b50301d460003901d807045400b0b01e00741d801e040e065000040513410340040034035081e0600c520203840d076680040e00c11884103940311089200070f20014442150140c029561040b2503003455200d400303541c03d040e8211940020400203e81000c0014414040c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 819920422 1250 819919172 819919181
    0x29043008032406040b030c0705010204080706122306030708070e01030b161209082104020109090b030705190f0b030103020f0d24110d020c070e07200703140a06 70
    0x140c6070056002d4044410700091018807840c00b4089618501001251200d9402d5098400c01c0e80d00c03070001c5591725204c4038a66030b225200d1040c44001420071440381c181031090b020f440111116011010201c40181c2100c0d02000002030403150140308007030000804807810007010004010703032212a85107504505201700b40080080032003403401181c0c5140b952165014841c4a071400e0409000203852100b460074101c503205000da07001801c0c0d032a202070f264441c0100c40b5203020701d100b6260015401e581b8801013066522140b0740c6581030704258010000d6081850300002e1383e001c08500321144544403107a002180c020354205d800c40300c8010006000314240f0105417440b40504480500b088009980d651303040d1180d03c49e2445207500f8600c1070018002250300400128a000e41099031150b114010603c000c0d0098601c1c4551440b42e013000140c107410786100c0d80d002d140160380e0501000c28a40e0384610717491569081c40824400c00c1c9002002c00e00910f81c00e414140b10402410440d600c0341807200a80307 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 819921672 1250 819920422 819920461
    0x50f07150f0c0503280204061205180a02060f04080607080a0e0a020a051201060b0c160f030206030705070314070c05182214060f012904300803 63
    0x5a00d441124051a40c100013900c0d40030710301c00d12225840201c6024094005d413010090001c61b40081030201d0b50f9a00544030040240c00c103041003140d80e90b01e46c081c802b440d09811000200c0e8200d0f96914015050910041400315414a590ba02e419a1110224a0014212821400144420103003d590202801507030344000c3c2c1000200200c04080e000a050021280308280c0302c0c5040050011500750207400040c02085891046603d40462010303564462000b171180d5101c40c041e1410204000c904072100c04256034000c0c0c0810b041d5035800703d00b80c07a154407007101541484144e003d021039103096080281800e62142004629540c0f51100780124000e030b00c42c0c40a0080c00c07450810034501c040d286148441a00c03901301c201500000d040c855580080e005d00c10996004203410040e5180b40f00e0607080c102e4090001d00a0081030700008010803001404035090b012004220810610101349130002201030b882c55464040c0b61105003600e41c008010f001100d4045005c07003048009420f40c03150070720b031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 819922922 1250 819921672 819921701
    0xb1302030c0301090c0e0406030507050111060903070f0c0e01031a0a0203190b0d2909030705060f100b0318191a13170c100e061501050f0715 62
    0x2103040c5880203001d54081405009140c079980c00d003503044148650601e01c0811342c042c2081102036100e05040d80c5030405030162a0119500c48081c03081c070400042c00a119124250265080c46100c1e540c054599203440c0e41560b6104601d1004a01c01d6588c82c0c015000b148a204442196112a0b004c580070860040000b40c880e4410301c00c016480c100b0544912114a412100040c3d03031320340b540000d161907690311014000e0440041900960201c0d142c48203040442074000040a980e5142c0d030035503030b2040603402032031364100c04081003441c2100840103400001840802039243d840d109810365a800803240c440d00ca0070844120207400c034082c0030f002204203040200403e9103416454410110010304031703c1d10400428400034081e4001c0f42620001c150f4011030041d07041d400b0f011011025044448a581c0d07502803400b480141017018800c180c2c00800301d40240005680d000320342040207032111301d03060501204010810710814000c005000d0184603800390901610014241c4003200c80100c1d00340c10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 819924172 1250 819922922 819922927
    0x2061b0c100c02010c05070810050108011d0a08090315040f0303050a05060109032d050a0309090b0a0312171f0f0303170a0e10050925060f03090c090b1302 68
    0x50035485800d1400294083c00d01900c0d05d40c0d140340441c07400c00382c1d6214003000c1c01008480141c48849803c01c50407618108003d1202d881509071011500851f4516403070a903001696400008044501078066824010141c5074005010400c80c404600700b1181102d4524080d000768041642520403660050104a010009444c0520010f081c0c0d00d034600000d05852420620443c4580a903003541c0180d0340020000324218101e1f150181e9107410403601100070450480700803035409018400d01542200c010320381030f88145562510340048911000740020082d80c6901150190305080c0c1c007074000c203002000142424125000100d00071159001107006000e80d5004001290f4044650b161507112108449015101c0c0606000244030400582c0054080c1448078125000d2650101c1c0c4101211800d9814000300400d86448040e071204801d01103500d42c120500040b44030b01c503c1070524155040018503030400d920360aa10a52950041400030303154144402e6904104c00418440c01803d5000d50 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 819925422 1250 819924172 819924199
    0x904061e052a0d0e0708060c090d12020a0c2301050c10051807060306061205370510090c110615060d05090606100c0203030d0c03020702061b0c 63
    0x1e40c241160101c00c0c9014048200407011049204030303803210300302c00760801501013130140c4e0a885005601ca008103a000f4480000c1e480d02c18039049a8001c0d41c0201108620720803955070132414600c52003848114401c2000c2c0100080c40600644041c3c80074451100210906c0c11030741a9007400a80210304203c8184404004240006075610b51f111041801040e01d54402a41e4079040710000c814018070300c1401000544140c02d83e00c414141e0341c581c0e07552010101e000403503a040c3c5805540781c8000c055066901c091b5481006c0200368101903007804d01c2c4000f602c00c8199025140d00f541c0804d4006034003001084803035018850407050081c0c4d41041e0500c2c0c0c80d0501040e8072502d000303000141e10304c0c062441c1e06117541c51104a45940019001c100228105045440e55807031007121100c0c002c444c61640058240d000b140403020065000b0011844c0038a0301e542900507002a00500040c19024410880140d40e02e1001e410301140031039904110380c82511916241c20b000d00e81d80c0780100c05003402c45 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 819926672 1250 819925422 819925441
    0xf03070b040b0604090507030305120f060105030f071e0e0405060904030c1e140109050d1107171e03030a0c03061a03091609090b09062e050904061e05 66
    0x807540715030400b40c0041c41d5501c0b007010501403d4082001400c034080d01001004042c2c010001c4c1c141625041c10b001501d903618070b0300000c203140c2518154003040c0181f000601084401100c10b42c01051391070703d2080040400f20050110341c07950f82c2e10022404a100c1d240c041d0805104895000000b242da016550401d0348024000f02d51418014258000260803084580030000342c24001e558002c80b404203154071451f02d03a0013490500380c21034440c000e105010341c3d2248189440107a13014400c01503c01e80e40703002030441e50324100e013900710f80c80d020b030070a02c68440c800c1480e41d0b043e0088400c051035403031a03c103c0c054119180d08280b4020305182100a0000419114016144191420f01c0d5996501d070102028507284400d030310761035001e003880c0001c10000001d0700401d03a46446901c00034420303285d0304507d0b521403604903040250684100010a003110500b00c0c008450403070510300e107407200e0b100c1010418518040b54161041512603070100391800b4000341c0401e80310b1503100200100e0504240c82c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 819927922 1250 819926672 819926693
    0x301050c0a030e011808070804030503030f1504091e06110c030408060a02070f020607030c021e12031213020105040b0c1606020c0109060e1323060a1202060f040e0708090f0307 77
    0x280c25406c0c042400800c101520003181d000c0e54018003140e03103910707000f100303061a070300e08441d662040c08410820a8450400e40031b4914150741c001401003100307194940000900072280000d4074000d448071100d0403403103110300c0100840e0030a0005196214140040701d850200080c0240d86030a1040048002040c441480a01c2503941220b2031903440419040440b44100100e8001c8d510800541c0fa00181c8074440174020100b44081e1089a2440c1007415080d0300c070300032004107514081220000a80b003005c9807482c280a28814140542899200e840310401c0e80c0105222807000c0d40100d02d0001c0440504054030006d0200d80300420041c240c07140001c05185e00c610601c8103111851001c21b00c01c1e0341d1150f0310100c5103c1d03070340c0400c50305000104101c031800d1100103090070043c1e854040354050900720000010303500800540c00c03442c0b00603400e00c2050340c0000e0181c903100340c2c10300c004101c1c442c0760303c4c03018001c80da5681c81d0b40f000d05140945508010003d074008110350710400513400042d400401 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 819929172 1250 819927922 819927971
    0x718060503152812030e12030c100b18010506070b07110d270806041e0b01080604033510090e030406030e0106030b190b0301050c0a030e01 61
    0x60594580d00c0398089854252008480030340c0c45a40044151000500903e58403514200801042c40159503543c6030000c0240080c00038000071182010300c02142072a811018080840104407458200d0103202c540c1002d10700740d0b00c0c0410640307030941c0da00c1b0b038541070390070410311008002110155450710300014801c0c410020018415161100042c0b1f010703018030790480c0344c03860700c1d0107842c030100b8010001404d4120002c000c940e144000d403208065036901d01c0307000e000d40b28558024405602d4944030300e40604c051000d02d00d100d403081500d075000074202044850081185400a10140c1028a4064582030220010004200c0745c02d641081042c8140c0032038100282103000d4aa454881d4035070104403400da5000500458101000290312981c00801001180c655940402903840602a01400d072406803002030030800710100880d804080844c0803125120345580009181d04460010130f094484c1102d5202c0c202901081c0001d1964042c000c10004001d07140082210413646146440100c143c0384 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 819930422 1250 819929172 819929177
    0x40312140a030902041d0312100f12080f0d0b09090627070b0a0207081c05030a05061f0203030a1112070503041511030117031e09060417060f071806 65
    0xc2c071000035925954049440031005515940d0706d41611280c450f902c0c0d111400030710b00c40c0d0b0100c0010703591040b1b014240e01524101410740c0030316442c1c101290280b041000c000d82d6045800c1020042c031001e00741c02401c0c1c0300318404010600000c508104152104001c0c05035481d0780128040081070484084456003805514400e0205182070202c040c0c6021032540112581d00c000041031284142c0002c1c0d600d00300c0b64550104d40f120300058095144a044481000300890014004074800726410340015070b0000f0041d02002085100811000715019406038150140c0c10000600800e0340c4140500d541b02211114054a006c003a005620b811080081c60031007040340100c04603081000f6a035100c1e40b4002442014000b1402122001d01c191b4428442e684000b210005810400e007008002d03200015082c06d010701c030712600500040007651104860360360100c002c1202048803805005203184000850005000c01d11344024051414807010f40a042809204a4900750b101040500c0740b09550491 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 819931672 1250 819930422 819930431
    0xc0e0105030d0e060c1203040c030c0b1309200d0e010f23060111150106020607110d0c02040e0a15150f030311010b120d14030601020307030c110411040312140a03 71
    0x2403e0305003505049000c1c4142d03000028402031003440400c000980c2cbc05000c16600b400e50300c0320110b940703200e0001ca0301c1d481c5404c12000c100f4481a64803081c20781e41050072440001c0301c040d00c45911a8000d4288080b40b40d80d42040141c141390034880c44520540c2104100300b981580216155500449512600d0643c18000011302c42c0c1d00c20704d80c03005a412158100c500d411001122035400c134031309004210041c0709010011b00130706e214070540103070041c0c45000340a901c01c800204035503859000c5070598115403698049105504100070402c03140d402448912820500b040604068a4104690328440c074180b060030b00052034441c1d844400c5030f5050510300741c4000d5a000281c05000505103180e400b450b08410500d40c5400400c40307440d51980d5507030b0111188011820600c2c81c3c0030958005005901c1442a040002d0059110000d002e0250b0800745c2003505400c00501901c8511100360741040d07000c41d04004010741c11940310074143d09400e003e12062100e071288032050060f0502034040680b02c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 819932922 1250 819931672 819931687
    0x2040b060d09140c031f05070903080d060503060c12010509040f0803010e0703140403090b16061a0307060806030a2003101a121002070c120c0e0105030d0e06 69
    0x502044a0756800074500901103100641010703506003000d1400345005000f000004922481c01264440e035900800a56080409420480d05d0041c08001c1c104401c0c04a5240048082600040a4402c4180080c030108426040c4800d1609103580a82001121107043c00364200e21541030764490b0560314103949600c004c1da900d04003d60131404400c4080c1070300c0000400455200c4101c02d00b18490075aa0b1030034401c029080c0008040c030041158042d0014100240c03c1c07102e001d984000f005881c8103e000c0040400c46030b1100300c12240040300249207241c41300c8000d80c844c141801840002c1186051280b82450b044000c40c2d29401c0240004044022140003500b0022205291304000c410180840d0051501003113140c0007000240710550400e031450104070424545180344642d2000400040c1159440329100440650854501201c1741802c0758804035000746d6408032a10703118020404c03410002d182c050000c0b1174034010780140340207812402c030208000e038100e40900b51a00044c0d0745181d50340c02 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 819934172 1250 819932922 819932929
    0xb0d12030203070212070f061a0d080306060f030f0601080f07021b0d0b040c030b0c0f0f0a0509030f03192c0a180902030615030604080d060e04060926040302040b 71
    0x16041e01205c0484004619842840004000c0700d4006100b08002c1144142104044214503400314a007903005691080240c001074000010315008040504460701344244081c1451181e04100c1d162001183d082c410840f056900000181d001341c1d8141c188002c2e4100140000d4443c00b503c4000030080d92030701030200c25603d42c05480c07210030350002d0ba1001c060900c0d2500c1c80d81500c0520041d00d292200d030011031447c50a00e4119102c01c0031f0000380c2c521f01450005000c900303030804400030b024494140050099601d00b80050000020140702443d0781702c281e69108070001d40d44c00408000c000c1c1001d85c00d06410b08543e200d210944441068001100689000034960310040c0c0000805c020071108911040b052034120050040c821001d9401580d61910144154031080015a070f03d60311910106000c1820b6034000d0010b00c0d101d14002c2199522002c1149243c002034400700c90041e45e4094030360610580d610b0784a042c10441e240000c55080790840c8440d18080e60101912517a038421103491540d6 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 819935422 1250 819934172 819934183
    0x41a2b060203042102030f120a020c0601080703030305070c03080c09030a17070309150804140319050a020c011103040b0f09030706050408210412031704060f0b0d120302030702 77
    0x3940404190b65a01e400c0c9000d5080c25100c4441c1c039203062580d4080760501d070006c0107542031880302035070647c20510f07000d12120f40c904e80a4105410b0a40c00c004800c0005800d02100740a8140c1d5001001b01030701d1450300604460008121404100c4c5011001c00002c4c0d00005894000120704000b9031540d2800d00003d08066000d01d00030005400b5040341210b241030030f4094031845000b40c80b200e01030381e6204007490320740d00c3c1d66201c05c00107007550380081c00041c40c0400c40f81c2201c904808807410329840040c0503e05241c480000d8001c50000f00f258070340168104800304803c042880c00aa02068012000c1e6030b0b404ac500480c800c825000c00c40340206022407050758503003903000f000c03242b22950700d40e4081c1541c0c1c441d020300b05141c00741010094641c401541070100b04514203005924013441c000d450700000000b000e080741085014007200403100c0300e29240d240258010840000c2c0d542c00036000c1e00c215440c03a03e01c64003a4102c01440000f148442112242044080c10301694035038030100100c1c10320 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 819936672 1250 819935422 819935509
    0x1b0607060209030c040c0305070e01031422050106061805040c080a02030601050d09110328020103020a05042d0f030515060d0210210203061c111201050402041a 70
    0x25186c02114a101c4d90b040d0000750080800f51101400384140000441c203031403000c012003034142c0b0030030041002d11040303030310032a1082a40030000c1c20401490303441c0d81c00e4416641c010300015032500d00800042c0c003001158002450211820803651102d41006000864014050011242d01100007005640a18112000e001000d032003000024030320714180c0742c070b89400e03000640240300c0e00d05041c0540364103091064001000c00001d50b45951560b0044000c1e6015860301e004004083c000094404d4405920310281c0d50501c5010428403441c1a400c0c02840f040e0f48110f02c5103420a004001241012550402c141034001d0076190366580c1c2401304058410b1210001d4100c8401441100b05aa00401e10b00d01a04008004400c2c1c10460050100f23a000503210347d540301e01107505800c440b200c8d414944c0150341c0304042a03d525003803000065445147c2c00c102d034400380d4441040000b1441d151041c1c0e0940703000e109607101e00340941d0b4041204085000001400920745454090714a0050440305554 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 819937922 1250 819936672 819936679
    0xd060504020903060a0510181a0301090506160512070e01020d02030310050f0a0518090601050307060e042414010210060308030f0a0204081c03050702070b0f090a051503091b0607060209030c 83
    0xc5003034a1903072800900219000c0401880c0700543c2027540d10b4180122221942c22100800664444901111030207503190300103404d200040140d841c041c00c0c0204124401c8116480b0202804405030029041103402801d40e01150400c10803c07400800000e4100107450045d100c4068800381301011a4005400f900081d5221903004020b40d9215114060a440f0380421400e640d400d0342d0310000d05039207120500400f00490f810b480f8407003d42c03d0580c070090b4218454500d45c042101004222110b1358103903000805240b04010ba101240c6d40c041041c1d880c03a81c0080c20400c030217031450711004664000603040304803c08210000c68812403450b01910f000d2304541090342c848001742108034200540740700181001c2410640059626800428840d08503811a94140c2c9000445154a011607010f0701e01c05602650301000805d50780ca91170307081581030780541d903181da40c0e050141d011441e0a03810707111a440784014000461042d241e9501741e61300c6a601100246c4c03601c2200e0300180c10401e500250070340 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 819939172 1250 819937922 819937949
    0x7020d02071401030209040e0a03120e06060405041a0c030601140f0712020a05060a0603020a0602010e0a03182117160210120207050d030b151b160305030d060504020903060a0510 78
    0x3001800272400000c00e0b80b00b600da0410013a80d0405040945060104a0700560481c800040e01e030704054020a40c0075205086e800354080d41c0039803c240141040d60803520810010040140c1940c02040388018240c141c40c40c0c90a0011101c10f1281d50710511000074032010364442c050305140d00030080c041a0342e50143c04e44286142120041000b49142c0c4026489400aa01c5c009070b180e0061144d0703100c2c603001001400001402d610b0540d16600ca0f8100c140901000d18000100741e8000c608018011031400906107503032003e820402c0b0100c0d01e229880c0130320802044a100e01500303000d1114a1243c4c180c400101300000004140c4180c0103104110350868000240c40b801c005001c590f40e90348000f203880c10802840f0305003c0c0700e101240f1171442c180c030401c1000310301e0100248101c0070030001e00f6002103904000c140308003581e02803410b9004860607440032034661849801c40c007410300582000d403400c50400550000095a03210003603d1864100c7d46c0340c002c41c90070000d20548501034104d8654090 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 819940422 1250 819939172 819939191
    0x19120f14030c10050403051e19020c0f03300d06060c030815062704020c030c0118020d141c090f0e100b1b0d0f0807020d0207140103020904 61
    0xa85070b40c0080414001802105a21151000b20703200f52809260541d0311181000310000800d1015240d82140c4403c100062048104168603c0f41d070768403444065003d003020400c51428480d0314814075440f1482600b0540700000321035009a0542ea00300a1400f50701c0306100f00e2030400e40e0358816491912002414440080b40d03241e0001c03c441d019620a56800f02240e035080745008440b50581ca489034442800c112045249503d03004c6050801481041001c030b28440c500010100e078060856601107030030214400f0160031080c851a415200c04102e0301840c42000d034005403040c000e80a00418101a80d00444d03107980003002624101c40b650a0300c4a181c43c52000c018049c10240c0c4101405c802030200041100e10303000f25100d003d04601c0304102072540c10880f070151a504038038502241c80c5000c20741c80303200860801006c8100c020039120051441c1c1c0180e030080c82654014a0f10703040d035100345407950a8079070000d0810300321013508590001200d4a03c0040b0041c0c4210758980703501034244401c08 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 819941672 1250 819940422 819940463
    0xe010b090316060206011202040b0a0914162a0c060801140102030f090906130f020409050105030a05062805041b1d04020d03030f0e0a05010b19120f 65
    0x2065021001c60440e00a010001c510441e0380406019100c0160041401002002e0820340e100003803910041c80403a101400e01d01003641c00401d64030461400c0c0c0c9907941c1c0701c0f0b0700010000858000d42c03810142c0b002114401c001800082c0020810111020410090180c15145074a0b1810813030b44401c0b2200c4c4681d80303020003001d0300030a000d542c002145008203096507600002c1217451210b1040411402c0120060407c00101401051607822085440c88211080c190303106101704040042001078079941484c0d492811264142c00150180e80007042d0100407a1000441c0c5601003014000e0058031800c29a80c0c0e01c4a00613a660b00c01c0090400f01403204000d8040403503035070040d1018020018554400031104000316945a10103100124004a0b025040801e04880f0460184c01d000c04d80c80c1464102070100c0f00075118080790340d00701601c1c1c00304001080c056504120012120f20040442260f9001210282da00c100755004041080304020020300300b481101d4144c0011445191810030000c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 819942922 1250 819941672 819941677
    0x60e0604060605040b010c0605180f010c020d141210080d020714090402060a0e040b18100b03281b080912030103080307030e10020c01061404060b03040f06060e010b 72
    0x71125281032001c0402c95003058825041e03c818140c0d00d05c804800c03191560801020b0182001c1c1044030301313400d001010b810030800450440c60f208000a0210642e90b0b0003810401c0301ca0390f080c100b0102c1070080c002c6124910070b8520203090030b10322640c144c491506410a07805603500c900b20074003445122000044c3c001c6003490803201c0140d034420008075110b04000c50b2100440c1c009602c81e13414000100d00500c25880c50064030800380001880c1d21182e40060491428602244a010300c11b00400c040b64429001c001e00404a03800e4990840c100042420041c41c060440c00341056050121882042055001881d110000741d6130b0283d84d2034190002404980c080702c4011580c401c000e10381d82001401c408480c100d0340c1280103581141c41307500c0110003408400016519910483c400c84c07800d04441c0c8014400b03840044000541c42e45001c500b03401c41c403401e010301845145004400c02c128140706080301e9002e40d001c0b4140d482c0924902e010002042d5a812a00305554080004030303a54014100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 819944172 1250 819942922 819942931
    0x4120c0c0605090f0303041a031005030a060501061205010303051602030304050909060402120a0b0711162616030f030c061505091609210503030f070906090602031213060e06 76
    0x52503d620044213052513070300e01c603501c902c84400f034107002308210760320500000e190805082c2401025841e982d2001030315001402205803040ca60b0f400c010810310790840000b001080214100340700035851030b1000381540c00360050840b0100704000400301150740500440d00036103001071418159041c400c5441c1e54403072040383c0490040204180d90845400c001402c64601ca50144948080d1f0b62081780071280c02c3e0003400f10803501d00c5200c02e52855a6480d1650b06d001d0140e4100c414050441400d030340400d0b11500c40d071003215800400001106508407113200e004d6a810800500200d03c440c901218910b100ca44082d1149240000c102c80d8245039401c1d00045460441d09103000751540d103e141083c0d40c1c034506a00c0455604841040380c05007480c2205103400c409020200c0c003107416140d481c00c41d4021150f010001c0202e00c100014035400ca141d5101405491900c03801c0c1608008010703550340300303404200d09401002400a9800120704034070003030792544090203110407004100c6180c0e4030901501d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 819945422 1250 819944172 819944179
    0x20102040b0711190f03080a092309102405090607030807022815111602031204080d0309060615020c041406030d050304150e030703090e060904120c0c060509 69
    0x80c1c0c0000703140c036544c141c08251156041c090858034a0355644080381d500500c0c0d111b083c030000031000a25034104d0240350132510380b50355030303085503e0906080040c0904001e10160390300c0306030f03041402000349010316094043e81e0640c0d01c40326100b06040c1911280149191150310840c000b888130704140e88031031010301900064003100c402e0189100c481c2d07000704403500054401d00382d24038024003084035080031014800315943d000a03125020b034803264542e8461100f103413400c00c0c440120411070804000e800042e01e1803400702070809040281c01c640318002d540c04a030415071611b01d40300600c1010381c4600b0041c818020054009192040007070f440d902310025a81c40740745005200e115540484052520a120060107880c06141c090f0081e10079420280080d201c0c44149604c802e0b082d0010310410314262840d030020360701c492040c40e00601c04412504001c0c40c0d11040e209100305a03c0d081e003641d820551051152602181c0000c1c1111100c4a40d08050030b4014403160009203160080e0042801c40010f8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 819946672 1250 819945422 819945439
    0x5040f0e04080a121d0f150411151606050601120c050913090812040b090102070f020f130515010f0305010b03060114190201141f0e07020102040b0711 66
    0x261218103410000300c030064168001007107402c5100c0c1c82444c0302d220001c0c11341d02c00a031000c010b04681624400d400200189a0b0100c0e0a465400c0001c201f0100700d00142c00e2001045d1901d540d8460140c84c0003000c45000d40440604404840d0808040c1c4070f064058407041942c031041410800b0141406544190101d65490f0184600e400c0e64001c030b0b00b0f100482e4076100e213403640310414440e034070742c600c0d82d00e0010f1541c4012810000e225500180416a01c007003811109042038104801e00070800b1741040d4071030b8410040800007450040c494907070603404656805100048102203401b04001c13001e01d0018904e0075080040401a400c202001c9100a0340d030f50207643c2a8800582c1251310a01030410218400d000103411988a011800181e000c0c0c201205e04025640b1410200124449440d10150351510010100d402402c110355500c400210100d41c0410348070440e0a42058041c050110030700070a07400922564002d4048030002c2049407440340e9250818205182e90310345c4242d18a110f003021 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 819947922 1250 819946672 819946679
    0x6150a0320070308071808030c03090117011203141b0f0c0105070c09050a0b0a080d1202040b0304030807030e0f030c0d1806050a0e1806040b0603011d040f020a030305040f 75
    0x8200c1030b18642941603d90031203035155a003090f1100034044a45210403000c05030045482007040c40603043d01e542c503400541e107030103a02002500c0d40119520180c4007003891401082180c1003030f6a50619183c140c00e040d0300c4041603010f4080c1c0c07440781072503043e41b10303104c01d03c04142e00c000003e00941b0302d50b0550944044060603001110079224600002d0500440d04105002c41036255101c99007164000400291850310080414a2204030307174440e60b0aa0058541c120140350051002251100a0f00c01103240c00c4c24006101040d0101800c040c0c100305010740020b444602076403014080303274103002c100d030b40c80d1fa02a144a035890340182c4000809008040c03501d140580918030040d043c00440c030030103800c20b050400c22220341c1c200d1490384007005011303e01c01da8207807103903600800717504c0b900b60702491903152180500c0f0590324000c940c2c41c05544100010040c02003860f490300b4400d10342c804545081d446a00700304690603021032000e58480400d00000041641140080080381c0c0d46280c03190b041d81d40c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 819949172 1250 819947922 819947981
    0x90d0e060d14180c030d2f03030916030b070c020f09010b090f040b0102070e070207030b1005011d100c0f0501020318150108030f07060222061403040c090506150a03 72
    0x70205880c64044d07110000d0701d41c6c000c0c0118901c034000022400402e40850f0a1203007584810752200e00742c00c0c0d03500300105210399a0000c1c0840a600d0610304003220141d45159250184118024840c2c010411500701d04800c40d0b0b1002042180b501c4000c0980300d01d5611804185510360042141a1040103040e8180c403807418540240c011114058001e1b0886520300405403002001c0101b2403002c43c0180040440020049400e5a00601e0055410203c040c01c010005d088507030300344070851050340242c0382d00006642c1d4a10401c03100520745031150340e1000d5840d00281001003000006e04650000c030400500030b00d039802c0031442d01001021202c018801322070a50781a04203005d966681c0e0410005003651031840b8000f450203910070035005242061000241d04425046604148036250545081158662000803c2101584031000918500341303030342c0d0480316442a12a40c0202926080040c031141c3e01e000070744484030741000c081c0342d44804004c4010010180b509461386206068040c034000c140 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 819950422 1250 819949172 819949183
    0x30219030908040302270901152301051605030f070308010e100e1305010507020d030f110306041a060301030c0e01170a0b041b0e040c050108090d0e060d1418 69
    0x20b03046200c41d07140ca13046400b80888103035074a184a6406c41683c1120b001c000c1640d1506100b0507001c2c00002d102034001c0c001a0394110254004410002e0a102c440200034000028404045003401c01a64aa2603403094003503030100e2040c064158040480c0c54150368071448010140395109035140d45550780c80d1145d4103141141a5050071400700c40c04c0f001d002050301d041d50342ea080554105603201d8401d5036518142503450880d0f0304c000503004010300f88403042e0540540349220010000a0000d2072910841d08154000100201c0c421600d82c462400002814003110081100282c50969290303164140601000480c1c0700301030640800384d000003440c8200c0c0c0c0001070080402c40c040c000b000c90a403160410f00d207010780192485034411091080c002c9007070059800070903201e203812030345103454140307810714807515405281448101c50401c05e000d140444d5500e014151800c0c00134106201e0808180b0900030408200400e52070b10700c0c2c4415881e071101d45184941400248000c4080026000a8990 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 819951672 1250 819950422 819950441
    0x1b07030f0609061b030207060f180321020f0403031206181509061202040b0301060e011719060e06071409040c0c0501090f02030f06270a021003021903 66
    0x1000880c030200155071a000740030380501807040030564031880c2005076540c00480c2c0110020950000b4107404001060248041d048807032032040040c584041c00c008140f60600d0b9009003000010600301c40c508090320010100105100001c64451844d901450841d912600040c0e000c1590215000030030302c020f0054000342c0c2c440010b460203042030300c02a0800303812410402e2007845500c0c80d02181260380b40c403420006003030000001e1006162030041c40101e030b508007429400f03a410b10f038050205c1210004074604451544000200540d4007498542c24480c034503820110aa244c45039103070600104e80c0142c20f10044117400d17640180c0383c0c1001a40d40942078540c0c200c0358075092001009510b816032003120400104e040c070315001040f983e00c01c1d0840341004030440b0784000e400c86000650808003c02070140c1d0200004006600300051003090300180f000c4072008051512030f00030107040c0184541d0716842c0c1d020301080701c000d00b081c00103400b0390010540300300320101d00ca041c4400c1d03a10034010948070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 819952922 1250 819951672 819951683
    0x7120c1e0501050921030a031d19020a0e07021c050910120f05040c0314030c120702120a060501090506010219140a02130c09050d0206270303040306021b0703 69
    0xc80c035041c0150707103903003099040396888400c0c01c40b5a00b0358034148404840240180000e199680d5000102404540348900304441121040c602221841e1001032054880c0300844410211203c26100240c80e8080c5030300b244003032003d82420b01192640009600e46000441c200440350001c2c041f2007142d50380554843d540d40148102e00303103001c26015a1504081d00300c1d808000c5801001d0027400700964006a60440d81892a40b0003001032101c4858100000c2c2c015402651600c060300701042e50f60441070050030069680010b0480c00c540d11401000000e0400005554030000681000307030042009104485003682848000341d165840841d883e41240004594030202d00d038580c80e1640d1741e07404150b92004d80d00c070709034487c005a900c040030b055801d03039420f0005c50110240e242c0100201c65030703803000d801800c200817040700690b11807041d038052a41458a40d2109080034006d251910943d40905405010001d804414040070341c00404424280721003501c141101903907076a5480d181c41c070002d4036 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 819954172 1250 819952922 819952979
    0x20a1d010f0f0203040b0f09040f020903030d0e0a060c0f020601080d0215041b031b050a0b030103110a030b09070302030c0603040804060807020109080a0e0108070c1106160507120c 79
    0x4442c05407070306031000c2c4607520449050a071142c003040d005600414519400450104860409283c0b60045100c1c1c031410030401d42c201084d110219640c2c1c01120303950102e003615a0000790b1500d038100403000840382c0108052020302c0b074612000c2c2c03102c410f8490401c01070003500700118180314009a8405003e02603801840b401e00c040307000001d040800703002201c920b10030302e40e014494100d0121505c003550241d001c240701c00c010b80c80c202000b820283d12081c041c101c01c100401003c040752080c3c1e41129041740c05480c401c200e500c0000d110501681004203a0001003050040340c0c8800541c20054901c25070440b060b6184000400c081d5000071680204003030020002880090310551600c0e402007010f00000c0ba070b407003d90342c404000f50000140000010382c0d01440c00c01540e801010311b0740001043c00d00d02401c0165444034200504560380c3c10340105400210340c00c0100a0481c07103000680c0003801d844c201901c6010401c843d9403001000d54003985445004a0410220440c000e0040040005980d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 819955422 1250 819954172 819954197
    0xb06190b090105090406030b010e070f020a0204020d18060204080f01060321091d160c150c050409060e0114090c0307030b0a030b040c210f020f04110706020a1d01 71
    0xd40c000c100701810840140801000d5844074001c80010f148120942451581085c00f44000c21034010590170821074489043c40f01c1c10707004a0180309468060358050f07611440a0a004041d10422105031180408482c4a5041c0581c0f40e0103030091f106c180e42540c00301d0b80783d9403070a800c0e00c1546c08041d04d0034a241300818001d00078803070f8030444555581052682160389400780c1c0b0b0008c0715100c3c1500c51440e040b041026803c034002c02c21100b410581441c2098015585440245c0f45210110b1821255103a00c131000741d9014609803401030107000b5042c4030094807001184407024080c4641091080c20540c0d4000901d82014250301c1242c00860090071551520411005058601d004a0300644030a2001c0045540b510115201d03038081c41c8241d00d420719100d01c0c229501501d07454884414000c0d82e034080055800030900c6ca07015011981000f490000500080c024200849174207c0000c00148440030003030650040c211051203522140d00d5000e858030f084210551404520740000c2c2d2003020300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 819956672 1250 819955422 819955439
    0x1a01051c0608061f090c02030a14130f140924060d09050d08060321030603031303030c3516020a08010b0a05030d020705120120070b0619 60
    0x1a51840d00c40031032015510700c0d00300c1c10a8801d80e00f10380d00c0302e9040c00c43ca61400711241500001d00810000700b0100704c0006000303440b400380b503e46000300841031082050b0725200c441505d46070001001c0e207000240e95009100311034051482a04048080600924a180303000031000744152041240124102c0e8110b80c1550345100700031650341e101c0310600203420501010320810b141c542c03040e4001c000c03d03e401200500b60b01d1000308100c1c07080e030000b03c0c0e441c2114a0500c0000d4500d14210f0116102e4441c0c80000c5d081d40078104039aa248540c42900200b8154050b800b050441d010b80281401d06082500e620440000c00c003c26a403100424410b24140c0c9142000340115103c0400c1440388881c16800500b092580354451b902982d12021001ea031032030410342036070081c01c040740186284001c0620207503c0b81c4075485404c1c41981e440781082032a134020b4000103480c1c180c6000e45e070a201404800800c10790000b040a0350040700310000242541007a60200c42c281c0c9040075100001032900c0d480 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 819957922 1250 819956672 819956707
    0x170a15140c0f041e0519030206090f010c0831150e0d1a091b1011070e0403030507110c03100f2004140a061b030504030b15041a0105 58
    0x14102c06040070400090203a60002d003120100b68880130b103030b02003413900c0c00304a50b100105409030203e6155400400059564100300c4110200c155601c161115050f0016184001661006003000e10005004070341103620181a0740450340d4a41f1143c402c4542084a0818031414054800039407485d80071803030128042d440c025601c3c03200900f1030040c3d400139600c000d808810040e202c071203485104140100030350107000c8031912103103410b40c050420011200080100480b4440c9100b800b49950704498004000d101c4440034103c1c412402c1c80c1d174285403030700074000d1000725004000103106c81d2074171507400c10125429100000c0100200442285007010303000402100c005080c5060b61114ac5c81c62012004101640200726080c2036a181c0e450418010520986c03465501c1c42820040c2c01489519000f03000e124100d2076401c143c2003024106c0c07900352000d110340e0b000030b0000c00011080100b01d4a4140c12400010400da03018020703003810720442e0310404e810b94012404180c013400030340c01825010303a8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 819959172 1250 819957922 819957937
    0xa1805010e090703152403030809010b1302030c0918041b060c11030c04060803120c040308070b043002070f1d04111903032a0b10170a15140c 62
    0x7000581e900003521814010001b9150aa4400328409820824150030048039940101d00d0700007400f140822900080c076181c150120300218036404004690f490407500280c0d4043c41c009000800a0401d5001107801c0e07150846045a40c84640c0c048240300000e40800c0504540c020b03110600a028180d5071ba080d031500e1a9242c0b0380611401540103451f079184c1c0560401070000f0005590750701c4102e01803080010006003500c070301200401c82000050400421604500c0c0c011603d450390340c440d8034105101003280b100c001504403901401940102d9406520742150340d1603021a44001c2c2e8504441c03031401183d21510381904600d80c408840c15188184441d401441031000c01c10041c5c0707035000030362089006540c040d240d6100d44814810150440502c0100402d0f2810921040405008095100f076880c1e0b00100042000b802041d5034050481d0103a02a003003201c030308082d00c0171480e5a240d0b41c02044100f60b0760b0141000b41d844c50042144194441e00140d01c0c404400ca070740d40011940c080e4440b49 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 819960422 1250 819959172 819959213
    0xd18150c0215190e012304050307080403110405090a2012030f1308120307030b06070512031b070f020f03120a030f0c020d020703030318020a1805010e090703 69
    0x1a540c0400c42088042c41c45002c01001e4101003803110714005040b5803203094001e00c2a8504941d2910b8075041d0f115068100250621202c1103954510b4042c0c15800b032440d00410100703000c9004810014616403010010500350380400c0140d96141140c4d5a174500d01502500040c107054981d8440302101d003010500c814080c0a50a400400c0340f00949950b1007004594062080450082c509403540360b03011008260344030081014004030750b00d02c1c0942c84050014024190b03100c401140780c2d114803042c1d80000b90000180d50701c85d0f0200900114a90048800241010301c200c149812803142c401503c024a070000c4d07100c08071941590078404024601400240e2520408070020050000300c80109040c007080d503004228213440c0103400c0300759804659408155081504020b18160780090484101e03501443d000c52458204a0800c0c1170140c1c1000c0a034100e4000180480c2e24840002c1e61101009000702c100840d81ea20303100f070140200706072018000d0b50401c44041004ca10a1226403c1218005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 819961672 1250 819960422 819960433
    0xa0e011805030901020606060f180103063c081f0b030304080106030209060103021801270b04260d0809070f0e071d012705060f0d18150c02 61
    0x1014500c00c1042600d03046809030300026160300c0d00d50b818000d590708100240c3d00c0a041035008409104580550100300707a0300c03408009411246d80c481e401200c028500403200c100790f5122a42d0440c1c03074072424001d40004080100c48134140717070f14401803401210081005050380415130580e110880f280c00324620301032621042181d21580d001c1c0010b20080400500000d4901d2642c814040d01486c000e1030f050500d481807102c031507007001d8008440c00c24a02403801d1140c180c504800300c01018030402c0305d11400d10b406407011030326004041c02002a40c602e80b101c800c00c28102c1d40c684036a0200d4410024842d04503128606442e4000c00c0c90942203002c904c15100440e031178112001018243d940908072141da42028080100d4100300c681c00b640007800300840c0c1d080d42c100c0000c2c00b4080c003418031042076a996014180541d84040c0880080e02005083c03603039400c101e121166282d001420800c031001d2030a80c001b402c00e081900e0501c1d10540c010403a880701001c00346403e0041544003000e00560041 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 819962922 1250 819961672 819961691
    0x905060307030b010e0f0603012a0c0b070314130c180605060307050405011106090c1203190504170303010609051201020910031e0e0304031421121501080a0e01 70
    0x280d1030b4032800780c9282d14080c4164035240003c21074880c000381c8201c1c0203900d401c20ac095003500d061840c80030241481500c2a001880304011500c0d40d0040e10041d1800c00d260b801d201030700d58160003003064081d500203014682c0d04c80d5402e0320840c16688100403c203d2002c0c40c104580204c2d8801c0101915000c44005946580d6101184040d4001c03071311540061000101032000750780050b0401c13a4620854010403952816518855541c0144151144101d00c140010208041c0401c1140c589408140c0c540c3e0b02c039180c1c00c3c2d010b042c94006000710600640c4900c10004064000002c0e01e049030800d60780d41a5452505d02440700114100307000b5042c03075400300103040c5540c40f0090a074070020040e076400900b192445921030711440000c0019040c0900381500c820500348000f0503101900d801000c000c1d0064059078115150100007151003800782130b05060341a100b10303844050940400c0f03100302c00c01d442e40e5415031010107048801c400381c0410296804542480300c1e03540001d00a105050001494540303 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 819964028 1106 819962922 819962933
    0x72d0909050405060c1b0322080616051b15040b060a03020603060609010e0306190501060f0206042301020d0504120504122a08010219020f07090506030703 68
    0x60101c1c2c032031b698164103a000383d0b68514601c1101d590f84002c8040345511070305039100c00145807004400049031040860594404e40d0782c04500040da801e40c2d0740c00d0700c140c1c10903200200400040b040d510040c1c2c0040189007940c08003000d011040d8605803030440801c10000300907500039282107208000681f110025039810600454600c0d4503444540012907035620b0003640c1c40d5143c41140203000081100019400f0140d0b600a4148481d0713803201401c3d50071200c074404403c01a07000000180101e00b9a0f682ea98007121024a0200801d141e000e1340c500760381082c590895800d03035483c1800104008541580c0c010070540c00c0880c1480d182001100300c1078550302c1c02901c0e00c1c0014848215845514010f4000d0810681549941c152204d000341e00035080310041c0b4000384405565400c00500005840b090050b8940052040908180070b0001400000e442c164051241d004003000080 = true := by decide +kernel

theorem cover : BRFrame.Cov 819784172 819964028 := by
  have h0 := BRFrame.cov_init 819784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 819784172 ≤ n) (h2 : n < 819964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
