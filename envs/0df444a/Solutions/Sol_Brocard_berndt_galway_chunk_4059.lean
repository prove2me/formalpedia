-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4059
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:27:05.82698+00:00
-- url     : https://prove2.me/submissions/a55bbe43-bfb0-4083-88be-e87e8a07d616

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 729856115 ≤ n < 730035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 729857365 1250 729856115 729856123
    0x1b0a0e040807030e060306010503072d02070e0c0c060403122304110a0510030906380603060109060f030b0915090105040527162d08062205 61
    0x50100ca2000c0c1c006480010b0503045201c100301c1000441d0050300c1c42c60070b10002440c4e4040602480c042c0b02042d500c145072400d03002408410102c014000201c2d601c25548000d6680105100b80c40c0740e9a440d20104480d0a4500212900044040020300031501c0782c0d80e040b20b980700c001040a800503070f01c041d102c0804040b85015607003614200c8940d0715074285800c14400800c10ac1c1c0300310380b2407200f0000c20041501c0d8910001c04400c0e03141400202d42078103062190150100b4907014285003112250040390300410310f02001c8070940701080a0360229a401072115911003659a180881c40d05c100c1045000d2044290041c0c444842c540414101b40d4440410880081070310f01d9121800504211401e904240304154014803040341c0901190901c0440b0301c0e40c09001e002c000840c1c0b005045d4200340d000c1c081043c1c09096018001c105541c42e43d072154403003681242d0b100544824017500c0d00807904003000381c840b030699086102419813904d0f510b002070480d15160311144c1d501c4c0080d00803980850707401c0c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 729858615 1250 729857365 729857371
    0x329060304030c1509050d0306180e0a172701020a02062206050c1510033003021206060702130b0310020d0e070f03050a240e0109020a050a06021b0a0e 66
    0x2400c00300702c0c1a17140c035156007805114000309041516000f0204040c503510b0140944030602c0101c0090400c200706109418610203500207884800c00041c0360014403110300c0100941c4448541c0540b41c0080c01d0766000f40c901903214500e0040c0c1c440e111190142c6041c074010f010a495400c1c40c50b4800200203100303da2000b4503031000c2e010400106803403110482c01d000300c01034140c2e0100c0c00701191401c42c5a20740789c946240000351001001059802c12000c0e22051112882c25448003091060072a10b40100a075110900d080700c008a598081800c90520b401610140340e0700400d050101400b100d4098002e0401c96000d0703915106000c09140d03100c64610050040c110b02000110347c4c003000b4100240707803410903404843d448108a800300007003480403443c0855030703a001e0f0b40c01c80000c3d8040f241268145000001c1d5502516282000d41000c0c015400b0b080c04034802d640ca414915a910308100524016108200158006481942854240001410030403070001e0800c03064644485107030030040006c0b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 729859865 1250 729858615 729858653
    0x5031e0c0a0f0302070b0c120a050f13090f0c08130c0b07030306080d0f051207050d05010801090b010b0a0f03050915040c0e09120f0304060b030d0c030329060304030c 73
    0x10b501010700303256050040c240605400d4034150719001d140448666550b03d0300685905002c004225229581e02c103600f240d210071080c1c0d68954a0701d541410b59014141c1c240710703113084136180c0140c010090300340d801880d60039026611011942d42d600d069410500880c80800c4414144183c4046a5a420900030f00301050182c0d0300013864504104541d0310b44008030b8404024444c0f80801116060391080c00c40746841010070400a4544a00343d0a40d124000e0400c0d1450765410240045140360b415030000d01114054107260741c07682da9600e4050414410700c429000020144424060418065042140c000d0b0f0204100c4940b00004585084116001d5404854080364940304000810000c241b82d03400042da00701501030700c040e00340d07000800d100d80d483da03402403200070000074240142984140c020f0f9201800b07440100c007801600511010003e0f40442c04680b801290b000380031b2120355400d03100d241201c14501c0e5009134104001c466040240110200060700b4507040000b0401145d5844c0e40c010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 729861115 1250 729859865 729859883
    0x2040e0c0301050a09081c020c03040b09190311120f01050c03040308071e0807021614150708030c09031204090914010e07061103070f080406030b0d05031e0c0a 70
    0x940d04040c01d4540182882429604040b59800401c0c2500d080742c8000c84a0307440325110650005419001e8001c00101400307038007011a000500c0c0003180e0013054403490469036920040d15a00d0100301c0c1680d24007010f46203802101c00850703a4101044282c504da440b00701103481013800140141c1c291032048609541c4004080144810582c11400d41508030480303040440b0b4400780b8902d044281c50f04540400c04102070714020526140c02400010b481c600e90071910719445481700403074080c062030b208405000e0500c01803c0302c1410381100680d1052640855031900e95107594030054143c1d0030000f04135030305005003900c010210034400000c01c000c00300000c001c02c02071180e0502d4042c600c280c0141c0c41c65641003101c0d103019940007199940507500d540c10948503151075100c16074950300560703000400459440d410401400043c50260045940030364040c440c100c0d4503000d2002da204c1c1110018a1030340180b02403060400c4e80e1a0145c0543c00c2110003a0074210340c81901c924100e1243d5056800e210 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 729862365 1250 729861115 729861133
    0x2a110a06090807020306060607050a0f0309171e0d020703020409020f0d0606050108071b0209090304230f0f03210f03131505070f180b040602030d0f09110f0d02040e 72
    0x70280006c6a00400c1102c64500700020354580b203403030304d0300003070018040510b28601104042c02018500c02501c400c41c0d00200350341c00880c006a83d00c000418440459415113000745400341c000aa011921240394081c00c0307000c0c59682030001038001503200300d901c01080d0203d1200c540b2000120b42006025010100e1131a1402d4009840c50802500200c00c201c0001e901180c07204c8091007220318640d040c0d4403e0169903410100500b54041e54000061840310240e00205d1514106800c420126044801d1450701e0310600c10080030715102c2c94100e806801c0b084016000ca001d00e1104079200c218280c0c1e05181107400075480c10703254001c50300c14203d00e90824118013440310362030181401c07900c18502000103040450740541079905040f0703503030104038010128042070680d161180c001410795101c1346446a44841010751241c11440c0d50805080c90308455181c0c005980c000c039421183c105449002e10550075040c40003076600b0442083d040746161060000584070341c4550b40b0181c1351800a072242803 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 729863615 1250 729862365 729862369
    0x1209010219261e071e030204240c0b07140714010f05060a050f010507020907080702161a07081b0d111513021306080304092a110a0609080702 62
    0x1941600d042d411011850030070483d02c85864562943d4007980e580e510746a542d08800302c0b10842180951062021040c0312400340d0760301900948107991b51041c042c0b89502003500300030800c241401207030300054018806500070500e09042c01e42c101009103407903900c3d02c403d86020403051703000c0ca40445201d42c99400d4040216000e12801d00c0d9506180c40503c020704184000501c021502e000740c0d8454192495040791680c0a10b040b58801079002d07204002c613251180c1c0191108004a03500030243c0034103960700407052040e0031841d003078903192200d642510010000f00c500c580c00199003102c400380200000c40c000c500c08060075181084c0b000003070004100000f4014181601c1610b040c48d40c2c0e200b00208404503404440d8a80c0c000800d1072001d10f180550700000705001080d60507481c0752442d101d0301040c819400b0004000383c940203c0300780300080840a52503030440d5030903440d0f59075500c18100e5084c0c8030b02ca0f140d041606600402220080105503c8180031903980c01002c0700c20300302c000b03203440840c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 729864865 1250 729863615 729863657
    0xd0b340807030e120306010c0c0b0c06010e1e070c021f020d09140405150616020f0a061d01030e01020d1a0a0e0703022a010905211209010219 62
    0x85036500d0140a8000f85402a950756240c1c2641d024071980d0110000309907910a1400d0742009420011030340300d5917661403100030b043d8410603d22240e401820004520019940f10550066030102080345d103111108840351350011001d048181007001c0041001c0150b07445100041d103001a0440650030705a03864000303803038106140c0800082c81014501041001d001c8400c071800284283c07030104880d41c034020304100d00c64240c1c000551004000c80e980c1550300e030400c200345045100344c480030089151a0300700600400c592040d140010f030398261440b02c0300a032550208135554181030100e0102e840031461400e903001140c040c6031040e03841c0c910101c1c2c2406038103d03a40000c029100781c4490745c00e00c050a00c4030382004190300c0a041e000a603000c2100420b4640000100843c0e07030b410078200c000345485010303000405d4160389921451250074541402c01d030b01102118003c1c141c03035281a15150302c1451001c801002d14030b40d0356080c4a00d500c074032841c05501c261444160365060f001d0390030420081c08 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 729866115 1250 729864865 729864871
    0xc0f050d090509062107030204020c030309070902040e0106051b010f1e020f0f0c0c06070303020a18080309040f0e0d09061d100e04090218010918020d0b3408 69
    0x40780220f41e00380724460300d51004030b085e00314055031901d1000b001da00c50145028001d40c802508584001500010050048040d5024001c4141524401580c90035801c1c2607014038090712405622030700c0100402e60040000300b612461008100c81181c0c050100c1a003158a0000049181c42d15160b000c00c00840c0c81d9018011204580411401c00310140c41c00260750144035403100c210f0b0000102c0c0601224104600c0e0100d860007849644d665030523280040203900071500d40c40108051a09818680b0803c1c00c0319416100040000d508105600c020032014004652884500aa6640b412071110105104542030b1480e0743e1910030070640340c4000203050411460b0403100d0080c1e80e01f8201410f5468040c11418207507145491010480c69900080c010b220f1100001c1d80a0103003c000c084100d000c410350360403991080030400c4120f411103500c0c0160340d49002c2c001e5201c00104000c03c00614040368150700003400b032180b04491010b0b110006041084002041c00d001c0c3c500d030350014425413084416078 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 729867365 1250 729866115 729866119
    0x5010801141311010908100f0b030c030c060a0c2f010503010806040b180f0109120e010e040f110d0b0f1519030f020d020c010c1b060b010c0f050d0905 66
    0x458034200403140c41c001401140206075a10381c601200e0b4503813140d0042400707090300000340d410220b1a40c1f8a0300040000080800c40c42e4100b48003000c0700e1602042c50000d412010340900005c000c2d51007004442e1784003403171400c28001040041c00c082210b444941161003c070760049800c041959120800140c000460141046000c100500c0010004074646030000c2d4010400001a01e030622803c40036a0800f8142c010b62041e030681d5040c0e22415082205028000e1040c1c859564901c80c0465800303000c490514040f41e50090313070401c681002ea00c6a03081e201c2000c00040d408802032940206030780058981006075854101640742403402e4180090301c1c4100b151030705500301c280074803010b5078000c1c3c110300c0c00300a03c01d5580c01202c2d806074024510500c2003680840d075036004200d1140003500461420811503282108d4440c0c0c05010f400e01c482403222002d20720458102603926071000d0310100d400d043c100f181800c1d840000501005480740750b03510400c09403c0701c84254800070103160356540114 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 729868615 1250 729867365 729867401
    0x1005060405130f0503160302011d01020307050f0702040f0c02030d050c07030806040b010c020907050423010801050d11060f091815040e0a0c0801050f0a0606050f16021305010801 78
    0x300d10b80d000300041d652201d502031010000071071941012400c50107050000d02c410300c00030403003204165065010240c61400c191b0038085407144150000c0c04c0340000c84910b03000c030f5000c11040b540d85120f0000f411106200910100710035074181400c109032141c51860002580c004200703051440401e00610b0b40c00000e0700c5019040c42d58640b401000500c0140070107015541da84040355282c1d204041410b5000d8000d0301c1040941090300e0014103983c0644030302058801500605c418201c91900b1044200005954a2201340d00b01004c0080c8030702003010848080042600c440b40070388529024142070384c030040340e141d2503109100a00c86c900484208040c01c180c0c000041212311001c0d0300b90a11081401c0e10000303010071810300e015162032164440600b03541d905130350000d0146c6054110511840c2d03035071a4690307191210341c42c0310144c818500441001c904180326081a541304400079140c1e8100e8494000000c000035008108140d080600c0040d090391140010701650341c0901800c2906080403040b0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 729869865 1250 729868615 729868621
    0xd020c030703150912120b030601030b1b0415081005190b09030313030b0601030b030a030c0312062105070f0e0f09030c030c07060f0f211503051005060405 68
    0xa03460718480c1c04000d010048001c683c501500302d66215204c015030180b000c00d9986010303403001e80908001040310701070303504000c11002581030201c0d0441c101c1c3c0e880718000b04a03480e0383c1072600c011300b100e03205150400418840042e0002c0144143e190044040c1c5402c003440c1001c0c2080e001e0781c0b21a4200f10b001d070141400303001c1d8451b0102d80b034500f11a51040c003c0d0700c03041d112000901791b21a008000b04448546440030040c041c2c0c02c4003c502802c426201000380549481c203064640801c41e00180c04a2030203071043c800300340600d04103030003118500400183c0f541c8410001d035450546100d000c10312100c036480003081200401102001d0408805550f40f0540f038025030b1020140001d158120201d4250080740700c044080050b941d624041c4400c1d240c440800d4141d00e5960710052086a00003500082000360581c003074450058900c0095450480c4814500201c0d20340500c60380c080b01c0303850380e5101001c2e04c0303005181d00c240156100f4005085896400301009003660400381c2540e1142e4504414 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 729871115 1250 729869865 729869869
    0xf01060f050d0c0311040603060e1f0905060109050d0305070b07080c071b0305030721140a05070c1809111221070b15090a0504020109090e1e010204080d020c 69
    0x1a56042c0d6000e9101203011141018218094500d100c0c80030031180300800d000c9078158040d006081650300041d08581c1c540c2d944140d110a444c41c44030032404101e0781560500100c02642c119070743c0224181081c14206035910082580348000301030a500084011515608100e400108580c204291780392401c028103020780b640c00c8500c5800e00003030000c50300200c0310400352281464540110381000030b0329126090303030400c81e02d018004a5039403855024846001e00142c003407045810140c91800f4901c5c10840850300c1030380d042c0d10404054a83c41c811010005a829001c0c10254000d140f48202007029819441e24400010500450301e00c034048001414540038000581c0e00390b40000303040c148030a055a614200c00d18414010301512214000703007082204200685c079200f103036105680b10f9809540e008241c02c12660f003911b0081c00601800003c0100c00030315000840951280d41c2940c61907640e6000209400701c01c2218202035940101d410458030360709125840740c030f03507179400507000300c001c41c40c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 729872365 1250 729871115 729871117
    0x70f02060c1308030412050706090807050108090a02100522050904080a1707050a09061b06150e0a0504030e09010e191d06150d080711040908120f01060f05 68
    0x44807003a07011503012040703454400240000d01e00070081e20790340c90b1200c101146819890070207503041d2048000020303490b032181515404403803108002d000380c0c0d42080011a41b0810180c0511302922803254540e026940d0407110100c07451840d03c80c0383c0c1d58001440a140c42306442040c01c1942201320700100f0a644400340e0607944198040450343c2e44008040c0e056522030b04000001c130060950400308002c840c0c10800508a90105858200c1525a92034080355180e640c00400e441c580c50b881d40038800244d282c0c110a56031220841910865600e596034200000d408645201c80961190240006e058000c3c2669803c85402c1d0750450256040400c8112000350241c070503510b001786041e0070202d01c05607501401820340007044500351005101000d541e20542647c0418050911800707884c1107103041c140e611131040d03101600e1400c1480c0c1d078952625481001d94010b4103c0d45441c8014009070881008100c0c9000c00e04801c8035034103107655040400001600440180092a0441854160400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 729873615 1250 729872365 729872371
    0x1b060927071d0a0911040e04030206010302012d0309080c0d050306040b030105040807030e1f0302031807120602180a0308040e06010c0201050313020f150903010e01150632090306070f0206 82
    0x2002041c03000110b280079a0600c141d0340001002c0320714078184000c052b804108941280d000f42d0310689a8102e668055a001800c607802d07040c0c0803418003500600c2c5000ba001003c450780100c1d0040d00305041e4210f444d0138150045254800604000208a15490a4400e15140e580140c0082001d441c1581e214170380d9104800002d024420030025240030390b45d07141c5144440041141c5010b83c48a415030010740650016103107a440e00640c20001c40c800c00300092400304540c58079104800007800c0392500e200079400038082c030340b0f02c2401541420550700c0e6805094015481341d031200f550f442c90b20400d0035010308064901d03410401d0500c0940050707030f070000175030b03401c402503008003240c044151001600b8003001e04030383e130b4000480c01201c880d19007105004e040b03081800d900a00008500c0c0e1100381c202e50f41101c1d0b45a0340c042e5540c00f03001c2c2500c1803000b03680000024507003540241211111b00044403004000e0030210400103200703002418240309542e00040f1908110090a56522010b52507260003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 729874865 1250 729873615 729873629
    0x7061706060708070501110f0315011404060f05120c0a0f050f03061e0904080d060b070804030602160f0f0210170f070e130e0706021b060927071d0a 65
    0x1c1510750174000c0a51001124000c0c0c0ba6140c2e59840c1c0d05420201c294204550344040b4149031414a009540144039102442400016a070319040c1070400c1a2903070f0f08001d03041c0301001018042d00d43c0e2100800071040c01490062040c9860ba040d030b050003452103003800710040c00c0000c11310450400b605024252030300030004070307559a10007825036001884140b000f404181e01102640505c000d00460380010300704101044402d02803181c0302c0300030152038403031818000c0482c9010441000840c81c2036000d00307030820f100e00fa0f001401e1030988408106c8404400140d54100c07402503c58114904140b08450060b054145a240d0f0781400b10804940f420060080855454560008020780c1c421103000782032040081c0b4100d0001982840d41c1c00078441c0000b06540c40c4510100442c01c5400020211050b402d41d12110341240104018400c50780c103c4201d241d000491650880d69030100c6155412104104601c1c8950524000100512203100303503c5004c40501e6041440c0803a0b201d1172040c0c030a584403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 729876115 1250 729874865 729874867
    0x6040203150a08030c2119140a090e01050103090803060907020c0a06021b010804050a031d04061d0f0f040f1b030302011a0406060e0906060d0c02030d0b0108102c0907061706060708 79
    0x42c04030030303200c150188145440c0d048e0005a002552500305146505a51142c0e003031010580c3c842005404440390040050800d20041c00003d0840ca00b1400f0a0740c00040c0788199a41001600007003540a8056001400541c21060392002c2c07901c6850300700340c20035500346000d000030706158503410317169411243c01400304440307000d03102e4851041119803040104007400810890f50780b40c00c1104c01c402a640600030386000c010104940c0d094001c040f5000710100d2403e250380e80c507150754442860144240807221036202d082d00e1700e8440485464440258041e40000c500441e40d241d071b204c580260030300310a10807458032100380038640d4440002210142c0c1a07410032625149c5c4030000346a80200c15a40c000a81030051449120703502001130700c01003012500500010680d8401900c85520840b80040030400c42c030402c010048190146a030341242200f0b1081c0f00c3c82c05002da860f0b00804c101e640500f81c0d0301000b020044158010031900c01041d0b041e03110405810480d00003011489000c0010b0701c0c04030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 729877365 1250 729876115 729876157
    0x604050f042a090605040e0a033903091706010305060712021312020a0b04051005030403030f09061a0604030804050d050712112706040203150a08030c21 67
    0x141c8804202c2c2c1090401d07042e6100795035460014003401160142c00d0142d4182550307003081c480009200c0c0511a803640300c902d001980003004041c01d1814540f8001080e000d00300c0440605626500c40440c41e000781c2d110350040d81801c0480030000f03890018040e295001000401c0418000308810380c01104600d0203402c50710650348440080d00464a140c2000c3c9082c4100041032407503047c940601034801c0d254900c0c51a5249192112402980701d2141c0011100d1074080c9103034480e5000316440f0b8802c0c2400120320081142003012111507a40c125103060307584c02d240d4260800c17510200000b41040390541c1c40d090541c4d407a911240030b684942da0160541001b28820844180300460103403e110491605414450800d032003021880f441440c0101801c1c4554102c03080307000680e0702c50b101c100307150440e141c1750601488001c3d40010101154150900b034902d5056817a203d2003402804000d00560301d03040002481d40c100340a41e103a00511100d08001074045031010415503241c4007281070602c3e1092 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 729878615 1250 729877365 729877403
    0xf061002150907091514010f1403040b01030b130c0515220f050a03020d02100519030e01050f040f080d060b04090e160f0e04050a08040611060604050f04 67
    0x15500c102100712800c0541e0030451820800944601111602a018005e01e45c08607244100000180110080d682005d5011007995020f20015004608a450002c80349250f103001d001c0581c10644048402c6109500100244640f000085030010208442d11400031015600e844c40341401c0d1141030f0041d24900d9007011599240d03000d0b03460341c0b410250402c401d01c44907980c4040e45410307405a03124040d1a6100420700c0d060108002050329030252004961034256000c000441080500140402c0410482d00b09000a002c0140f4a03c48050320081054003a105000d42545c0c001009503c42c041c2c0d640400022035007140d1164442c0b60400c200640d0b0303920300354485000e8007072a0492844e10000041c00a00380610782e0001c1000840c1a041ea480314180c90070b1340610080c544038036240300c00500d106009840c110212182c01c284103408480380c1c04c07071950700e2512a0b04950302460220780803034148010703080188000742e44448100c90810036407408180102c00c0f40400b40003c0c05103014140440800c0c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 729879865 1250 729878615 729878623
    0x501140909010204031703040b070203090a06051b0d03060e061203190309020d0c140a031115040f030302060612030703021209030c030615130209150a14071b0501080f061002 76
    0x91500901c10106c0d042110301561450751098504451070170b80360340080d0071548040280e1b00340d00300051203280c846260280c11501c903040b100b05206140f6040c030b0300079003036481003054010511540e1000701f01c6904e4140d512a18880c010201070040b041c5080e00c60300f906021040b689202e20000300c03050901289a0210010404048001d40041100700443c06001380040728508543d001005220900c05410038462a0076103403100411141c10300e8100842868000300810a54408a5006003880d070340740c4030056030000c50344c42a809600000140115410102c5403242001468802585040c0d0b541c3e80081da5984280b240c09038034680825505083e070303018030080c034030050001c003202c0c4507040c2030b00346400000080c035525108007141045007010f080c0900a4403d00c01d402441c00092003030083c440041944a03a181508008554100098914400d0040c2c40428000c0465480b1040e050118000070500c2e030b08070505129407041000061520003a69551000054a007151001c1601d0026460 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 729881115 1250 729879865 729879869
    0x100b06091008130c031b06030e0a0b060f06040b04060f0c15020304060b03012a0e0d022709010519090206090d060b03010c0e0a06090303081b09090403030b01120501140909010204 78
    0xb1440d20f03134800024883d81ca0303007240059800070011005250f0719030741a402c4901c007500003040c4c2e40004aa50300490884211a0350081c03000c0c00d11014a480c030b80000b0015402038002c915101c002140501501d94040740320b0980744031030b05065090320002e403104074019001041303460340e05400100003810030055401200b20508090000e009001200c582400c002c440e640c907140f030000c1c0202040c0d0107a403003142000c1140740040d002d48182c15682e0207002071040790213101c190400040511024620307640c00494858030f441000000c090070450100552400441d4050301e10702e007410002d0300966986402c40d0301e10002142c158080000a00d06a0082c0590401e1560b143d403800d068048126081801c5040000003211403c0362980c80d104141e56001d514080030300020b8001d4002115850060090298100300461785400c065412000407103500080742c04134000383c1c54926070442c65802001003108107540c4203080c009503050061005500012040c43c0e4850030800780400c900080c00c0d411a00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 729882365 1250 729881115 729881123
    0xd0b0319060b0f04020f07151e0e0109080304030903030212030c030c07230709050906010602070501050a090509070c061d030d0b061c0608060903030402030303040f2102100b0609100813 81
    0x34513a84086d400000d00d0304910b00030b4031501e055804410081e002445407a05003a07500c1002a61a4004883c2178010b2100e20304401c442d65841c032040300800c1001002e507120303034072a6072030007909400c42c41c0083c1002030b81c002d0b44110300d0051003030290f25101003060340e9021040c44075081d100e00442c00d180a00c2034600030060b01c6104031303000c500c2803000003152130401e440c41c086003840262a90300a05556400901c296001608122010b00007507115034002c0518209a103402d01c4001d40b214000b51941505660b40c2002c0f074a24944170042040d1070069051810154038003070036841c420180d541e143e215643c0900300f604d50b200c1c080700442d6220400d41320203401c0da100301c042460161180c400103200d24000d03d2540e11441000a01280000040328851036019015606680300c603a030b14003402030104412192001c000501988450000c107842d9080c510980c0106107415407200c80c0b4045900e441c0c6220f0142800301700c000c0303c43d1100361599282d4005443d0107040c81d40c9101c0c4070010b45c0c1d41c0303510040c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 729883615 1250 729882365 729882367
    0x90b030c12010c020c01021b0d02060d020412024608030c01020c250308030604020702120a020906010905010503010e0a0b0d03030606021522140109080d0b0319060b0f0402 75
    0x9040c10150f110905001080c0c084a80500810005982c0d40124201c40700341c907100d00c0755251050070903419011540b803024040d075003007004500c280400ea0300550420000c45c810f41d460001903203802c2e90185100d9250481e0f2400b200c2800c10381001804042d8404444120a6001c01946134003108540b00102102820742e0b03110050900007034041c0d846103e0f400b80c140711b0101401780d8580e9030446940d00c81c4a58113518980343c42c5a48040c0aa0002809664820303403c1c4803403405078541a14151000c540740014181c80e0390f0a104000d1200c20281002d41044010134040c4400e0360440c00702c0381524500c65000b034050340c44600c91006403c020070b500c2d400102c1e10003202c1c10150940c201d24241c500c16001d85042c42e51007010b10460100032540441f05501a080d030790300c0300075904400d6210310b02034440e86013140e00d0545441d080d2841c403c0e085511010000d1448200603040c42001d8642004801070910318240a8010340b0400d42404007074030441ea14108001ca55445100c8150501d20150080d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 729884865 1250 729883615 729883639
    0x10080c0409051f1a010f020316030302040e01090c081f030b04021c1a250c020f04020f0403050606060301150807020f07180509010902100c032706110610090b030c 71
    0x840500300048032840c0d111051085613100398094000301c03401c402940e0056040601203014010000c00c0700e0815410300d40c0c01c010203d0490251170340180139040c203201c045200340f1400300080c80c030780004020300c00c84d40c443e031285039192040c4807900c022213802c0304207400c448e01c8500005039503030000703c1080400c440005440c400c01c01c00004261040260385060700300b42e9102200031444c105800c040c015404030030450801c41c50f01468210240d20300141c01c50342518805c0700418201e900080102c1c003e008003250070410440c017080075a0703201005441c128159454608695243d0280c0b001110620240c2000191000c2c420400081007401410441c2d0300c640d65507000f000c02012803801d003d020741c10034000440552050048454240e405071801010081d4403404880050705084c084040202344490f03035200c0140f41c4025000108075106038a80f0700c0c500b080141050007401c08029040d0008030401070f80c8c404981c0071400319420801c021a001d0340080002c0d050122050034203501c02444150f07 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 729886115 1250 729884865 729884923
    0x306061b01140615120613150b0415020304080601050607050a050307080a030c2609070e010902040504230604230f0106141c111603020102030f10080c040905 69
    0x400b03802460150b81c0c10000014203003010303809105044000001d12950408903086081030342644140340383d0300c0400220b20f48043c0c4115001003240d402a001d0a2010405102241c1e4114041c00200001c1c001585401e1900d0702c1d482e203403141440b500c0c0c840c3c8404140801404028070441d680250300c5003c4d43c4e500d0650b0715014417150080710400c80080d1509d444020180c1c0204410340c0d01d9080840c0141085d000700c0a90f1441c03902c0104049118090554005000c1080101c4940a041244400b6881e1420300f42400101e606014045402d6085841d02880c04032603005820380202080d600841c40c2140d050780303442c1c0e6045240ca4182d050400303504100d482c0765442c1c111410b03220681d507054034029407480800c407940030f01801d060388802d0666201c2240c190350347c00782a130b040483c80d0071410301c1e440c101d0100506403102012b0b005031350000700b04440a00100304166014201a0021403030608042046a42d225030842d1180141d545008403424440200201481e8a14005442c3c1152001083d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 729887365 1250 729886115 729886151
    0x201060314100f0207030518010210090c092007081e04030b09010510180203101a120f1e040c0b030114041a1f0e1503160908030306061b01 61
    0x145911001d1403c0322040140080e80204c3e21401d4050341d41030f0900c60b00c6400d54511800450306a4190300c240c404840f6580c01602611102500031f00314010344614200506051300c81c0445044810002d8454103542440d4200079541150340045079192900c3c241045e00196500300518071420307002c0070a0000403c1048001c251140903071400074030003a00c40c864000d14102690060618420f42582c80c0000c58070316078055a8059020303000c030354400740d03104144101181001c42140d0244400142e10008043c642d20303003500070740046940d41003403500c035207030922a1980020000399050600049401d00820340c00301000b07401c0c5104c8a03552545c0d24145040b1411102c0d010b14021030600311950505440c500c003500e85440d0140485005007410301e41c04c003140b42c40340303110350900030041d0300c80e00c003611189030b50300301c044200000c25600e04007a09c480032000e2400d0400b00400180072070900c400c1401205494200c40255440c5803030783d1440c3c50072642250460980a5035600e00b0b186507004035403042c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 729888615 1250 729887365 729887383
    0x709050a0f20040b211806010806100909050f0f1b0301181707061503020109050907090b0a030e030c0102030604060b03090d0c03030212100e010801090b060f010201060314 75
    0x441002485480c4425003010718110741c1038a0100d81c00d000030018400080010141c1ca080a88043c0f002c070310b0b014690304004c00070b0303c40381644011801c06c21300403501003101602403c1c0760002840d8503c3c20a410061400060241c082900e407a03a011808101c400c000314034981314174006681d0b581e0254014259a0f6140d15041e6188240c1c01048481d01d04040c41440b064003140c83c031074400b000b01911200101040035501c3c0c035104008111280c08198a40305e1081e44d02c16160000078401d2442c0001080b005076030300a24440c4400c0414401e0300d82d0041c2084044a20340c0031441d4030340749020780a0780200070185c2d0341c03a0140000503030440c4443c810750056228040803142001456152300603420640030440b03082e44158030180c03908a40354001d01c004a800c4e0311a02c0d0140c58440e036203038000c0ad01d00c4140c2e030f4003504409000e4140443d090104c03a4a0141c040480200043c3d4560f485210f01141c019080c10701504a506c81c14015901c00c6d04000c000d542c03c51580000c140c940203c44e6615035070300d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 729889865 1250 729888615 729888641
    0x1b060601021605030a0f050a02060409050415020a05030a0506010e0604030503031807030221010b1c03030509010c0f0c0f0f0503040f1e05010e130513110303040303200709050a 77
    0x54400c4202e2078070007003101c10b490001d0300411078550300d40d0703813800303071a880641c1501c10303100740d669050040e503c1400500240c0440c040114040c10680b803d030103516011811240907a0061200d0f202e199800000e40c1e90081c81058040b6903a1184401038540000c400961500310b04000f901006103d00000118002c100b501629405040c4800e0159207030102800029170101101086038003400702040b14260030a20030000154420044001424503116002032880c3c0d00d17a048500c4040c5901413060701c3c0d00c20400c000030301940717002e18001031202c0103455003002480704424002091284840750b030032015501c54000c0204803140c0c1031096483d00035104040c6070820900012580e0099040c0600c0040035108890314039034144001940c0da040e91205140c0c10901e0182080100c21141c01030324003584d889500910700402d1804e100d081850003001c01ca00a900070013080001039801080c101030409542655403541d46117001c4135061088550228100300c1c200300c144000700f141548841004445 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 729891115 1250 729889865 729889873
    0xb120f06060301091109100f060c02040506030109111504050301050702032206170604230a06051e060901020a0506070915110d030509030f0c030405421b06060102 71
    0x1039081050f0989400210003410702807001401324641c100141842d4010901410240e802074607201e420615070091b03400741001858032100401541454811150440e8040e0001d200f0303540640c459105518402d03540502580e00781c0c0700801d8210720f0006445c06414018002d02890411010082d6070b501305400c11100e904071003110b115000500440e11080300c0582c0c0343c0726683d0076090203c10350360b1402011250001d4455240204500203807108a203104603000c0c1c1c19400b414020180740c1114210381025029020320f4665106038174480c900d40d913103480101e40086c0e541c140c01004030704000c42800300070f01502c1500d007448161382e004a222802d80340f88240580440007090000c41c1d407041d4555550074940c0209a11800852017600714580c0000300304220780c1740007070700c20010246034002229141c2d00d82000c1400c3c0818900080f1040036840180d0391800c200c00c41e818903078119100140c1d10809195a41c980300b04040c403840980380e40c020800c441034000f0103103803409500d44a00300d4806005000b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 729892365 1250 729891115 729891121
    0x30c12070801060c061503151d0a1e02030111130303030c1416050c1008150d170a120203160f020601150806060f031f05010912150b120f06 61
    0x211030101d0700d0403140d0395034885503240c1d0181c4a0b800100a0003460341540010b204010000c101e4045083c0b0001d402440c00046900b0003101c030308010210b1184124240d00b00c50f503c1c0c03001c02d002c410120a2124038103903d072a0948a440000d00401c8240070303c0230440b0020403101040c50b804910300c4101c2c1e00a440030b104072804140116000c80110f042e85810b100306000b110030452006000042040c858022182c5844586000402c88a8922110000602e41100700498030132101c02a07518000146d65181012213540d591035500400300e80d417801c03900d401050780d424462013110130304420901c00c0350031981e0340ae002094084103215030b000900030130107001100880c0c520001e00310b4100c41600c003240d60000c00410b0308440b01c1001402e01d9a020900340b00d81d248207030003000194042c5207040700100880f409640600f60a642c10f40c04607043c0503104a08100445c002540c0381e61150b800507a00d401e00b0924041c0c0303402001c81c500c04580041500400038944403000070b040d841103604100b2600995 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 729893615 1250 729892365 729892367
    0x9072d0b121518100b03090c0a0f0509161407030305150114091e04240902120106050703030e07030c05130614040903020304080a1101030c0f0806100e06030c1207 71
    0x15000301c2c0c4464015180182504604060b90300290b0401c010034150302400b0381d80c170700e080c8036a04140c1c1d1410540d040f107400841240380244120f002049070304a0f640e4018a0180000d14200c8001c14280c0d1400640e01058540c52040381c03151481220302c3c407420740340e44050500030010320302200d1640408980d042d170903105600480782c0f81920070100c4400c0c0d141c11425800e0290302c01a0f2040d400490700810741c810040da886008a80c40c004082c0c0c0f850740450f842c604071180d110030a60040c085030740704124900c0050380b04e040a0f81900c2450170500d0780c07402249002c800412107091030000d10701607190080100501c10b40340804451003240c0050240d6a040702c00700842e03000d442281100f040d01c040107421810103422154105000740103403800c2071f640740036141c02c05015110440d0501c0404005807250f6805104480c01a0000d03e80400e220101c13440113400700c44082c00c402c0c49103120207000781780c5620603a200e406c00c040180c48181c403030600f03c1e41c1ca1400c0d08103540d80b911502000c0300264001f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 729894865 1250 729893615 729893641
    0xf0e0306040213020901021207060e010605150702091008011a04061502072114012016030c08040f08060a06050d03080f06190b03070e03010509072d0b12 67
    0x210b400a0070442c07203203128949140254003030146541980503d10707031040d00c3c040201c0a41200d5000d20300108000681e0300c13089007183c0458110300d1060410350000340d441401c100036606440c0d0b041c1c41d200844d8440300300c3c0c40141d80b1980c2c4440415800c1260360b441041800c00b00740d144250584081c0011078455056003558030b070345020301005078004641044110001400c0f00048000c038401c0601360072040d11000c3c540354295039000140d07915100420000461109015458060b4007482420300c9140554808081e50b001c0c005810072500542a405028040701114001e20355080210704440d96803040c141c03101411101401d004e441c0c031100050505100c6034200d4031382c0d40b6030703101c880681d9409420002403070098500c90b00541c0c0c4512403d801c2146000d804084c01007608010b4480c0750805000340401315001d07a081c0264107140500c145000005003400680784031940c0c80c40e00d101d03c0c140da80c12180840400345682410b5000004003c40800002c240c2101d000d848100c00d6a54140c0c0704680c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 729896115 1250 729894865 729894871
    0x10803040510030b06130f030308060a0506030f09010b0316030b1b040b0a05040b1614012703030b1905030f030c0303011701020d0609021903050603030909091c0f0e0306 74
    0x3000c400102c00405a01c40d41c040d04514400800140c00d0030601c0c01a0003540c02e5a07042420155009002802455040f6195650003034040b41d0603d885c9007401d004c0381160201520100e0b0194452005c60504c10f400e400000c0d44c102e020701100c58111017001d0740000c00200380f0050f5100c00c960b00101d1940c070b003003401d50300300c40b802d40e100189024601120310309241c0c0049100f0040040902c400300c3c2442d4600000c02c0440b001102c0f20203481110b00702008841c802100b504038582c502490507070001c0d4881c000c0b00700103480c00d00b24000480182030540c050540019105d80c003c0c8540741c07401c052210407502e10300b034030000d400303c650710390300140d070319a6030f104840d0711403c01e9105100400041c0b40382400b029003010400005800d200540b4113a80a43e00b854101d04081a004580303418480060f80c0d8521072481c480c40c05003c1810f0440100c1e03160b00c03d06110743e000f030400340c0001d10021030400041500084250018100d1180c006004085802c14081a0f0000c2c1801c01d10b9402440c0000725a40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 729897365 1250 729896115 729896119
    0x39010b0604051207082e09050706030203070302040f030b0912180f122a0d0b0a1d07150e010806060d09031b140601090501230d02090c120108030405 65
    0x481c1c5810001046011141200e1901e8103104440000c00ca4405c18024180d103128114046124081c5940c0c5101e50700c050b8a00380c2034803502c4c100111010400c0015a06d0849599082c0142e0300d46600308210f000e481030342c01290328003100580000c20402c0200042d4414401e01c3c0c10340e5215149603540e80010300c40c0000c01d11900e911050100518580030b208004165001020a40d01581d6400c0f1941441134144480d8180031460302401c1075009030b400c29896144044038003285a42d600c0d82e0b80d103003034a40a441584500d03a0f07914841c0c0005940103500c00d002002c101102d10440da0b034210000d090840680c404005000707100321100d20f50241c40c00c14041c00b0300038001810107006a207914014000b222082e0200903e1245400984400c1000c3ca001c0602031503152641800c0c03050305518090b010781c8040100ca14090040002100c005800d001c2015001907090441c148980041e0001c141e01c00060b41c81240541409148903452000b842c11007608040500240c2e80ca810307240d203c0c000c2e0721440d5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 729898615 1250 729897365 729897367
    0x1b05030a030f02100c0c170406091211090f04060b040204051503070201091407081e03030610020703050d0806120a111c0b010b07031d0102070e070539010b06 69
    0x2000079000c1c0b180c0d0916907400340b049804030100071300c1c43c500740c07800004a080424084d10b551018042e41f0510143c40c4810391031603910b0240782c00c1004206511522034840889039000b022410080c0d2140c00e05584040142400000c0c1011110800c02180650f000c9034268688240d0600a051500a44044810003000d07142e00c4841d60303080c0561540000c0480e4115541d030301405000590300c40030b582a4040d40380040030074a00708680180707842c0b5086c0c074001d210000c2c0a8000c01c0352100100700d03540100251006980e20100034010383c40d111168000078001e00032a140c0720403041c0d101c00500d100e01400c5860128079544000160b07100c1f00240d0024082e540f191550742d4807400d103070b141e41007510003070340c11040c5445c15511040914102a0894510b41500040c840141580000c4c06080c40303840c6e80141da006009400041d43d10120341c4582000c1103084800502035602400665200a500d00181c548010b000194800b031600e0404c5c400c200d508021355014507031380301442012507903900603200d2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 729899865 1250 729898615 729898633
    0x30a080310290a05070f240603020a030f0c030b070822050604060b0f1305070806090919081c0e0d020309060d05220c0302040c0e0303030f0a0b06040e041b0503 70
    0xb9185680c4264201403c0c03000410002001540d00c08200300701b540143c440000c4190a500340350329072007000200c200e0130303405c0400c107002598810361000200e030341c09001410722807658605501c86425030f0f48040c00b284039510800c21101c4c0c001c081032b880341601d401662031000b16003001481040c0603070409401d0740c0c400d40024001810a81c49466108402021441e061118800040200001414201e442030302c51003848600c641040350705030071203001c48200490340303000d1990a58403610580200c1188500c6a01c40d01484903a9049a008044417a808a0f00014024401c0043c006004d5000f0b03081c031410001e2501d061012055419000b4001c01061030070103008a2036014000143c0f40103110740d0445000d0b6103541e0b903100543c1c03c03d4030414802c5d001078918010081101c062003028010b100d0900402c9200750f0300417046a40c4105400d400b424692100c1a4200003001d510b244240c08c0800003a02003866005540c0380c82c0314034421040781103010323940c81c0c0400320080d061059507010b50122010b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 729901115 1250 729899865 729899939
    0x1e0901050105120a0b01030608010e160f080a030302090d0609112404091d011d070b03070e0d0302010e060c071103030a0c150b150d0b030d050423030a080310 69
    0x101045a007170500d00411a41d448101e0075085a940b60340301551b950060a101d00d8003a0310204050041015200c440203080c071b0072134007603100c2c059080c00400705030b030020b80c03400982da031160040320311030300700c0c008202040880c0f410540c0303100c0125103039200b8528a105848608640187d00309220b04919030340d41007a2606c43e08102400d6800c4054001000e420102404000244144c83c20408500003c444412480d080c003414085140c114200b008030400c01c2203000d64011020b00d1000350250f0745a540700c101c03400c0403801009481e890001c2c0d40a1401805a0034000e170002c1d1020a025250503518055504c013056500c1c4134001010010070714940300440825040350aa10811500710380108a141c00c0d0720000e1710600c10300216134019480807030007425a5019200d8204240002e0740108000384003950040c0460140b031149901080080c007003140342114184814182400c0582180c115441c103141100d9650811203c03621380004596000034448400fa0001d541e1402d020341c1c07507209440e0403807 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 729902365 1250 729901115 729901121
    0x623091c20010f020a0504180c0c030c06020d2c07030f0f1b0f0e0a020304030903111c1a07050301030b0c1b160303031a0a12020f1e0901050105120a 65
    0x540c42841d5640c881031040c0300f4890004040d80d00041c0c1d01c072650386040c003500070350345040c03242c6100600d4544000d200003e40c11501901c0c100b90141803880c006031161410902901c42c02c01c055a034a800c261a400d030525000d0100c5075800ca0300ca503034061429032110707816624121807201525a0020341c1c00703180840d006e40c024107072140c003a034480f058a0010300b04a480c0d01100c1c1d031003100450a0703981d0400c010b140d045a55034100701960010b5185040c07a440082c8403040718000500507045042001203180d40b82060841d41c1500c02110641549290800100311030340700b40000311030354885000035542c500c10400c40e4141c0c3d0b03110412042e6038541c51404080d980103410345450f00484802d4085040ca01080800150a00642c811030090f0a41c603005042d684142c0c24450000d5940e60001d08603650154080c041da060500502c804d05641d00004401001c2030104d69001000c0300440c1d2002108040c00130410b05c07050390380d01507503645e0307000440e0ba61050350390f8003041000c07103c08640c400030a90 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 729903615 1250 729902365 729902417
    0x723130507110a21092705010e0f07141c05060f0d2d020a08031b0102030903180a24110313090902030c1203040608101208070623091c 59
    0x201e4050002a15801d10b54402c20030140482503811a0785540100c1c00381a025803230240a110070156030740d00b48070703042c3e00545a000e00f9000602144c0150880c0040c0c841c404d881c800320403075445040c000c200b005900c000f007030141c07881d500680c0760a2144965081c048492700c42590700101c4180c03200004550b4000c241048500c00c24000344603ca48c0e005688d8480d0361001400000014643e40c0c4c040044081400840c10f5003041640d0041c03041208059010041e2942d006083c0a250361080720180000c0b496006900091030312034480d044501808040007403504c420080b0340b1655082183c03000020707030783e010b42d941ca0f41c0d9418810740207000324052a04440c41041c07000c0d01b12440055140002418400d1846040b0003a5201041c10402e15a01c482415040603411020544060501d00e0034002c00f10078107030203413029400150680030408a540f103900d040000100f021031004056100207040b100c1619051031034440c150072003170303a56201007041c80c10010701d4962002612041d0811001e0001c0c1c4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 729904865 1250 729903615 729903617
    0x3020d02011103040906030605060906040e1e16030302160602060640020310060819020c2a0112021908070c0204020d05061507050723130507110a21 65
    0xc4c0000503840403980202e101441c411000400c1da89469001d102c180ca00061940f80306504007030002540c0e06006c01d418003040c0d45e41d130102c5105644041e58519001d41450859406003900c1000414154040b41445080650107d40c480d8943e6078201260b540d441520400e0b0300c400c444200000c0c030704002d01c0d4824101e10141107032405040c0d1281143c0042c1d2043c1000c0101d80c0c0000070800c02650307031420000609018100000f603424001480d8240d0314030a0042d43c0c080354001500200c40e80c04025111a07211010620080454030202e0f20400c01d00c10315465020901072120200e0042990081c0c032813490f80030b005402850b440302400c0f60100c4020b020354080c030807a0b50002c00540c95500003001944000c400c0410a41030482c28000c005009030a500103580080c009403002810201e1584115202c3d14881441c1502c0c081120421590841c6e55961001c0c600e22410b60914036a040b5a00c00d000c1a00c3c0d03003d8001d0601c10480e200e21042c440141301c1d5aa400b0410880103101c5810010035685e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 729906115 1250 729904865 729904867
    0x9020a080d080a061d0c0c1207061e0603111302041a0417030a021c0e041b090807050a031b051203040305010513112101051303021603020d02011103 65
    0x19805209060500740c2111000188190040006204560140300010007100b404c0192488020840b100d000002511041400c000091801001c1d030713040000b01c480081e81801556100c00902e0a04000c0468801000300004102c1651815001d98441ca10880b50080c54420b424600b1008111000d03012440b20500035900748404a40011980f14110502e083c92140e0380d0340300e04129a41485001d0524800700c20350041010010480c2d01207103c480000d41040341c440404089441a0303401c4030702c0c640300e0f80c0140c5400719501003404c002c140c403050f03500c40e9261a20215100c0400036217602c0640545604040e400c03008100041000501b03a49801c000c150300210292201300240b00240078148410442d03001003424801d0101c02c0c03140300e4010700c940d22000e9240b61242d440d954201c0d118154503200d102070125080801800c0310341100c0c00c0d408400200070a1070500c410b86102240c2c4a001e4005103d41000024020b0780d1a40c00816250000c010400e81441c0e80d004403030b84400a00c1800141c04 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 729907365 1250 729906115 729906119
    0x703020d0807061e0e300a0c02090c0301241e0e122104080d0e0d020907030c0f05040308030a0c21290a050f1c08040501140f040909020a 60
    0x10300f124007018485003014000c900d02400c840b0080c1b80482a512852904a41d2481008140320150f41c00394861000c25040352500041c10f4181c5c2c0507000620080c1d008100070081045100c9108003c0d8140c0b005419035040a0511081d0008070280ca20b4415000c200400e00c1c10844003000e441481c903c40d00ba01d4004030056184000c160321010190a001d4140d101306403220800200381400c8028414441405040c0791900781c1443e60395401d46201000e2080a24401d00c0a032110b00140c0080c0ba000307030282e02c039410f041000900800c099500480010320900d0b081914a01c24400c840446c0c3c2c10144060075034662943c00c0e001032019104000500c0001c2d040500725507182c00760640b0000301100c00160292803400c00c4901c580400c111a5520280740303084c090300f595403008402c25204103850302d1070781c143d920f4081407a13000c0c402a51084040300d5400f40040096034001442910001ea0310a00d060b151180005094056030400387d0b4010030600080c8030509a40d030001d510b080c0000d0400b40c050b9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 729908615 1250 729907365 729907391
    0x90902041e093317010c02010c0c1208100e1f06020a11210604030207060801050406120b06060903100519140103030f0201060b030901020c010e030c120913110309010b030703020d080706 81
    0x407130000c031a26694491020041d120740a10614404001e41c0c1040c0ca00e450300390f0b6a200d49810681005000c7c032481d00b0103d503002e00c0d4089030718007a003441c404e00ea030b19050020b07103030002c1444402005001e01c180d48010840b41e00c08984102e41d203510070451681008200108a91403d00c0e41c00c251044200c0d020380814030f40304000c483d00540c06900074194103820481c0003010040140c00c010301890415904004449040e4145c03601c0580011080c0101c1c0c0712440050218440d21140c15418403480c3c0e05002030114030342c40305e030099500d06ca10016817100181400142c98400340b0641c28000704900401c0464084c1610111454851000098250703e88564000c603070005e032010100c5a60200e03201c0003940b02446510340071410340005600f401411400d00707540e813105285090003071401284140c01510340410002c2c0e030102c01c02c0e040c0301000040100e104141c00c1207039000003540c01c0030410403040c140840c1d000c00703482d009408100c2d0001b880c0c480410b1580111003c4403065561403000b0504 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 729909865 1250 729908615 729908639
    0x32009030a050d1106070813060e010902031c1713080c030d05010306092a05100201020c0a03080601090e0402090615070b01030c0617100312090902041e0933 69
    0x31500f00e032a44542080301540a601d000c070001e0003402882445003d00035590741080c00f224080354000340203d424445042c8150140800040084d05881392040e0b040001050703183c10442e06416541c2d0340c40d803038007804540700021010351f001ea075860b03424100940868812401052286100c07404c42c3d1510020310206400c68900764421760704296030743c0314034080100286031940900021b9103566034000784e00140d24160400c0e40700b403500c20000c0320f26080040b4002c4d01510700c00d50208054030461103d904024050f0001200c02e40c2c00229110790200e0760742060070006002d10340140c1800703041d903074a40510048444403201c2000700d00e801d000070790010b0210041c10f0b01951090030341c1c07005e651420b4006000846440640e0588003000000c10094048a4512800b140d4010411451001403824251040d05c01508158041800018042000c082d00134042e52034840c2241c501425a0b614144402110303d02400020407104405100080284d43cbd41d5000c0421040300603039000030365540f4141c02d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 729911115 1250 729909865 729909883
    0x13080708190806130b0109030f0b160203120a020a030e061e070f0206060d0f0b0109020703090905010602031605070b0c0a061b020303190f050c07060c032009030a05 72
    0x4004400100040480601207101004400904081505050110008000e05229000c00c52425900c07260038403568070032038646006503044280c642003005036003071403a5203c40840d458000c2c9400b00060010f010710001c201c501d2001d001c81c42c0c50154442c51074441c06984031300d00030000c050715501c9000c0c2c1c0d83c0091000c01d00031109415031202100c107407031480c503081c540181400c090203003420f001c42c2000d0b0003007440d80d0300c02c10032200011000001e1402c0003c82d0849000509607980300d5001140b0900c0c03035401810750900941b01c06a40c04d586200c00425900f00b4003d0704010781041c810b4540c0b01c0c900b03400d0714003294411420340b48240d4945250500a80048518200a900039450801802514456803105204005282c5503c07628884040c1d524840506915007110078407000c07115042c0298441c2c2d44040a80f0820301c450b081445040017181c2101606880303152a1120700d24078540644100484c184400340c0100280c0301d072410783e40c541d401c62042c49415009102d044c000048052080a00c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 729912365 1250 729911115 729911123
    0x9020f1b030910140a1b0507031412030c16052104050f040213030b0c07050a030c0210030608191103030a031e06080a020603071725180608130807 64
    0x14a0b041c00c107040142c0002c20a40142c240403112122105005140d000c4500d0384845007400c2400c03013010030591000c200c0d00702014185020b5220044104001c254449001080d084c0450b5412003245017001d0581c88252a500c1c50300c41e0030040200000f200c5248604803d008005070b0380041d800120345480700012030001c180d4090f001406110500e08070050502a280940d000c6040c40e440c1c3e29034801d80d51841c00301404082c5890000765450450b2800c84044a50200540c0c09208d2145005833030704600707a80403441440b1140c05002064402d202e17038412503101c00c0040c00d004c40c0d200d0f139002091880400a582e0881d91030070410301502d003000201500040d6079030028000b9203c951000001c0b06442074001300341d040a02c01c0105c1c04d000034040409980490f903069480d180c5140942c1c0302181201e00d10320719884039080080c400882c602e0180351034807034945800c1501500000312020300700c80603035041100401c2d5007441003e2281d105180d021180c1006071115011070b072079100098020440840d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 729913615 1250 729912365 729912367
    0x90506100e2d0a080a0515060d0c0603021b0606211612020a15090506130306050a0905070609030807080309070b13090b01090e1810090302010905010e0a0c09020f1b03 73
    0x2c0c0542c2415190800101662409840b6060040d541c05403513208101849148107040300109020340d9030b402c214004e2a40c0728007001e0305a40e8403030010f0013035002640c91451001c003c0044ca011070310041046845900020310804008901f60740040c0341108480600c1401e1242c0c201c02d0301c241401c54030000c090040020001e8495040703204000e181d03811604900f0040c403464981202c4150841d844a083e09c004442203a01d0300c0410303401c51003800284d40003500690811051007a02c5459034001c41541d805142503402309511840b00781c80d604030714480100140c400f000000003040d8040040e40e0804034ad2800e84416a90701c802c180c030150050500c1d01c0008488000070841032074540b184110f906400e00344140c0c01481c1c140c00d6a00280020150f40c1508080741c2e42001c2e5100a02106084080000c0d08004003000d5083c028000c1a5980c0b08542941c41c0450f9413101e902c0c000742d01c06003d9441101c8100d80c3e400c000440010750880c07144201003040500224000038104000b4101d558a150019 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 729914865 1250 729913615 729913699
    0x140c0601081204030c0e1909060c0e090106090b0f0d0903020f010f050105061605010f1a04050609061f09030803010b03041101080105130209010216081501090506100e 73
    0x10500b85981000c40c48481c00c0100400c1001824652002e402c440500d48003448540e1003031202a0302d5078928007088100d62501c1da42600700103141e48550200325141d07680110900c01c18041c4070219000f8082ea101007240f82604102d00311074140102010740b00d900242e420321080040c01e81c2a074003548011400341c0c00c00070007d02150001d110301c45400b0010141480f49502d07040c04254140f04400f809480e00c00e0420015051241c00d41240f00c08010400e41000041d00548903a0023460103205403a04ca1030501c1b011646614140b0642402940014655100c05a90405030102100d10440c1c800600082c800004003003210f4202960080141300b000540c0c0b03217001d02d041d00304a00c44440d41414000640018401511000012100680b401c40010799070031403040181c0c5020b400712000f994050b1500700100d0001b8000c2101401e080c02000401150b0340c89110800507903c088944076004825107210b41107651143d10691260300010b461013810b01502400c0c600c00c4110600091400a890050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 729916115 1250 729914865 729914879
    0xd080903070323011811040e07090b0406081b09040c0314010b012606062b02040e0105030a0b1f09090b0610111f020f0a11101a010f140c0601 62
    0x8419103a4941d03200812514001c2c00b0b40385d100340400b44000d42505800ca504148686440c0d024050200d068821590041d0ba990401009403481d4228503004a00b45980045c41050000d05c91403c56628002d1500c00f11071344050000d400002002a61014083e0000002065202481c501600c0c00c0d100007091203011b00001400c1c2403009240740794043e035100320045c103034502101242c1c0c100c80c0845040f40d5a240d00c829148010310ac0e182d44241055011403000c17411801580108116a40e00e07280e0300b101e80e46e4100701078641c100480f0107005d0f0000c00c00000d10500020407040b010340e0b803042d80100c109455928810480302c4565013229811116001d2100c1d910b48200240400300320b41c6043c0c20068070b170050464941c9a10380f2403186c100c100c0c022044c2c005c1e906805072024009403403402521106c24400080101c000849419428000c0c03250b600c01e802d401c1d0054408246c01d1403418905101044011035101081c05100c10130466001c12100c440351016009182c80b82520008011075414445 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 729917365 1250 729916115 729916163
    0x2030f011202061605032a060703270303060b0307050c0f0102041a0309070506160309050d02011704021305010b0a080a090309030f1704091410080c0d0809030703 71
    0x101c41110400240c40140d40340e81c1102d0203104440e9000702c0b19512031401d940355010303480e4800744400d00d10426a001500c4280308070518038214088620701d484000003074040b10514083d10b8609031900354840c0506402a5a101d5650711070724001844960355407450354140c01c184c840b44001000010155461310040250201d481000002149840c5ca401041140710700000300a160104000c0f000450252007400765000600e8042c01c107998400107000704065044584004034042102554081404d00b04176400001c100c7e4117844458601d8168444c80348854001041260f003c9404120ba000248040c00b406009018142c42103031100211032014080f90310007002c2c80c0f00e16180000710000300e54000f080c0000c40b03400c0075074115070003840e003441d114203440c0c0c0c0d1940260000014000403000002e07030052820501c0e101c03001d00d194803154608404514a442160042c1d405054113220078a0300c0d60041e81d00178410602036140041c5c01c4046400d15049034403c0ea200d91145402c0c900c0070301214 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 729918615 1250 729917365 729917369
    0x3031b0602040924060f030e01150e1611060f0a1808092b110621070e0613090c03060302031507031103091f0b03011814121608091302030f01 62
    0x50340c0c0c5071403170518a0040440b80d442a1880402da240c100d0403d240f00203521070250024060106052103031220702101c80c800f02640e030b001e4034000d4410f0750b15040f032180f0940b2102040280190000b034444002c1d00d1600a405801c1880842e40c81c4c1c5c080c0030900142e1904030f081c9201d94a12500d134002c98007080790360303001e210941c0c040710070601801165040044000c0100e55200c01c04808801c1080d000c03e059024581003404c9440c00b41032014203080c007280b80c580c412440740d03803641c1e021500c5a090251138025207801d042e001001c52014047e001013a0801c1d041443d9529001030321540e00d40001e80380c460791030041d081022005040c40399043d414010741d804101c05c080100c0c9103091020b1226960f005244410302031030030420b01c00ca071400268006045008c0b00400070301c40e1031144204a1250320310b196048551203c16500c21a0360303000410085860550740e5517490070540507140310014400505011580c42104000854080e0f032088d88040900c551824010b850303140c4801142141c10040e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 729919865 1250 729918615 729918671
    0x30c0303090623040b24101704060e011515030e01150608010305070603180b130623060909071a0702060a11010e070308040b0901180611240103031b06020409 69
    0x911601c0911840301c0c001e00c406c0384140c07020b00340f00303c81030400c69031002d00e0918103400004440920040c010390380c00481c1031a020200822000c0540050500d42016a01c54200ba2103c042c20070503080d4000c0d40301c4251341105500100f01c0c0b06010104200035003041c0c0005000c15084070044c41400b01c05c01c660009031825080401c000141d049507a020750b50311500c01041069100001022450b90214a100386a80320320b0500c0004880e4070240c08900d0038a0a01640d90340d20400107045260864100b4044c0f0b0341a000351549a0402c6146030345c60000042a15000c0c004200c07010041e00c07400024503034200f40c0da403644070101da0040e925003501c11140c1c052603c1c5d840884144042280e58080720b044440b0ae901e5687c1e2041d1080c016101d111680ca0300c195140e5441400254540d00a1040302d8044020400e96410082c4003e86206070111900192110704010005000090092014800c3c200c03201244505080070380d51b1340c400303a81c13164016428580e240c04000d0740000700d0040c0340c0c840b240c1c0c3d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 729921115 1250 729919865 729919891
    0xe0d03060e04030e100e0411190c0b01090903020a0203061006091a030f15040c120f140f060d0803010920070317060d0203070f03021804030c0303090623040b 69
    0x1034030000e052081300c166442c840c101c41c042c1d0203035003030240b201003256440c050000e000311040f91011514a4101030b440c59a540a44000503c0c0d80384640e5044800d6a8030401c906141e90a20b071010004104100044040d0301c6800b0814016a904120491240005000d80301513503007010b078001c081c0c80040e0f02079552005e6034120040000708242c19a80c3c0540c0d12000080700e41d440309440f00b001880008560780043c075000300610020750001d200b8010310038800707080c03207001c0442107440b00b125403400303510400480d00800300c0c02003000700d1582c5802050080c480c040f00b138035070f0301c2c0c0318403030303842a8040e81c1c400766605070f01e0007881c94000082c2c85030071800e0078640c100303600da460240140c10070034218004200305030005115550f40140a16a294000e0100c40d04a602d90240003800c80e45404140d10134101c903c1600242c03107001040620584c0c0c950380345024483d40b85c4d029009000b44c20021144203407a40008070f08210b421210312595004c0500300200760071315042c04000100068401303003000034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 729922365 1250 729921115 729921121
    0x50f01170406020904090b0f04170c1005090102130b121506070b180307032a0309090b0a03020402030f0a0e1c180f0612060b03070807110c040e0d03060e 67
    0x15005040ca51142c1c00c141e02598492907180000c004200080d0018002451481440100700c03042d01808c1c443e0b8442c2180354812569084c01c02428002c04d150514554004040450b80260715001650051100360002d410503035030926034110f040c0d13540c00002d001200420800541c500801605410900103502c00081045000125101e0300c60304002404281c3c004000c11031610750040041840038100068035200d03103403071034024602a280b20050058807411040740c3c400c00b07006500010041c0d07043c0c0343d228400c0d01d495181c1010740300344001580d106062070000005a259400218410b118201c500e055600d054048074084407000c0e03803100c0ca254005003c00141c1c031000303003400c0e200765281d082c05270b004040410b41d21450310b400e4101100c2010f00c118000740c1c03950026000c010b841d0462000f8024241c40380b104240a001c1241c0d00800070f2805004186140d0059103074003e13584034401a14003e203110000700d0141c81e9010500e40a90380000c0345020803980c10b114090141014180b0648141 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 729923615 1250 729922365 729922397
    0x50a12030f1b14070e0a0b09010509012402100c0c290c07050c0409051606020a1a07050c15150d020d0236100602030a081b0708030a06050f01 62
    0x540c0b00c00740140034503180802402e000303208110441c0203002c003442401d81c516248481c0005440b212040a0203140d4450000c21b69103411a8224180c6007280d0305c0c0450307208286090141d505103c01c41209500500200110000e1b01e4040c404400c00a40c8614540711003a180007484100c0a5208204800176440c0c0c1c1c000c0054920314aa41144a030074981da2102c1050401c507081600803042c48e540f2600c1c00618204006000ca82066503c800c161001d07415581d80f50181d03120003841d90004c03d10040c9100f00b007880e030004a6065006070445c54858100990500b140f4504075650407e000e0568141c000c01070054040400c0384442407007901d2102036200035602080d010400c0020003132242901410420312139001f8074985441441c1c0c07210121000c40b0b5108165404581a9502c0c4907070380c2482c1c00801c0340e90001080f43d4482c691513848840603503854080f034034402138004890301d025200300042c0c0d000c505400d0185010f5100c8100005901d8503200820000740c003540011414401e030600741d87d09032 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 729924865 1250 729923615 729923657
    0x20604020f010e040b06030103060b0411072612091f060b040504050402040902030316150e1f0e030c0f0705120d0831060c0809070b13050a12030f 64
    0x1d142828160030780101c0c24000740103000407181041d0400b802000000911003181c000091200c0140c40402049079206c109d648548111a4007805000b40d101c89400c410551010b103100e5a038449001600303042d02e03c0d0354070380a24810b07038407204658426144d401843e60082d07440072850b950f4240c00c0004515001c0650240e0180c0c1c800c03948215a114002030954a8903003004068640c01030a69a9505142885840c0c1c1030846030140c03400c20608540354103e504511514000f04800750080184806103102d07540c0300e541c0904941d000d10b89864440c0518041000a00700d1400750340050400800804002c134686a41503005034400c00c1c1e6074026a03d1240c01082c842501c640c40c1c6004117031036544c0304c611380b003a900041103c6094601e082c404034425030000407240702684103000c1801410f940000c00c41d080841030318400080c2d0480041004820761079001001030801c0c200f0400b5840b80c0e07401c0000ca1144041d0701c42080300c103444c64800100742d40641c032200340f600c4c1401c00942a030b8816182d1480 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 729926115 1250 729924865 729924889
    0x1090501090e06040204030f1b0603060b1c0b04151d070906120e030d0507080a0e1c2a0b0c0c030d0911030105180d020102033d08061602060402 63
    0x15440b06400b01d4000d07100c5404550144d038000d284244000000d10382a40c00c000442500c94814103840008690103100b4040c3c0012502d160314020b05005100000031180122030702c4a44065548201408080c0c85078000c02160f0b0380010a01640305241c0140c1102c042d01a200449405064404020741d20b40c11000c110141e55042c0341c0001030301c2d00304400000419100f5088030f118400850a2041da481c0b64014901c90345d07007642c46c1c4043d030322049442d006070307680d010f000c0316240c104401c03405d40040007481401d1036401c5440c01e164000030100e500c0140d00881640c030361641703d1904d800014041039240d40350b00320000410440ca0f003e0500d0f0baa5443c0e0280600c4005030a17103500c801c805014160094a03400d00000700200a5810103d0322403221070744000400c580c03409603000180005006200b628815090079112045c0d043d0800c41030041b031000044c1000050001d240541014030501403824040c0900c41d009210b00d0801c0c0d03d40c04c080241b444440301c111f502010030480183c50b45030180d43c2c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 729927365 1250 729926115 729926129
    0x801111813060b0901090605130509070306050a17010b06040f290c0f0c062b022a1e03090108041509030915050a1b170c010e06060109050109 62
    0xa21a888000418818058040541050400c02c021455080720340003000d4095003600c2c2e02022a544120070785035405003e5112126030402c0c18108800d090251005900c43d0305494001135281e15400010701d1188141c02981c84110480007200401d0003d20420900c400c0c00c0764114281860f002580a0300ca02c24060080c07414000a0fa580f150a00300c9420660b00c006001240d4070382091030516682c507410000041002d01c607050002d1441e0600c40100c0e20200c520340780601641c2e40101170454820303840c982d0200c4d6690f00f08800100707540126400c0103148803007a18039200030460305074540707081c0d290a520604c2400c080e030401c8000f0000011200a0740080c02c240000ea511411304000941191000344440e81c20045e030001010f50000200c0b054401e01540050b503100d4101c012100e500801700e52201040b034219a0140c1e00624550502001e13103e5029540d00c904e95526070401c540029003c5000c50303440d0b1501483c001428820168414420701e008002d1900d45000208a44000e108142d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 729928615 1250 729927365 729927397
    0x11090a0b07060f090b090d0f050d020c0f0a0c17011e231602070801050105010801260a0b010e07080c09040f090203031b060c13062f1006080111 63
    0x5082103000d400c4150f44401c044010000000181003540014100b210445183d006510260794154041c8041d40b1900b1a2541d52900348003650040d20000d5000d0001c0c1085441000c0000e142c6040400100e0111403007a11041e400303520b8004000c0b5840d5072422840d80036410300c000490303010540da9440540402d1541c02062210a9981c0c84100d803c0c10169909555240e80410610404988901103003824680c212081596600751032407c0320740c20700525000410501c0104140c44800c00300b05003c00c0d0f04030740010491b414044040c5800402d820481d030000b408001040181005580127030b2002007814410954070f000aa102901c0c4105000b0310b1044e0b55600151400300e0f426400741560560240440e50b85031701148010640180410440b0103c1c4245000100f1024a0000760381380c24141c84448000c460604d00d0583d0740035880301c00c40351103018150880b40b51400d2107110000800b94003019040131002c04540d0801c0d207001c0c2e0030040303203607040c042901e010320060f42c200c406500b0964040c0b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 729929865 1250 729928615 729928627
    0x30f020d03290f0406061d0a0815091c03090309060c0b0406021e070b0603010b0a0f090f0209040c1119020d0206090a030b0c12070906080f0606090a090e0111090a0b 72
    0x24140f10703180c081140d0050302d00391020130300c00e4200181d89103c2c40f90044504404081c142000149459170164001d9904541c400841c50304c0740c105616003002c903820a40d0380011062400c2c03c03204984010160000340c4035140002415040440c02e000f6001030702d00074241c0501916405030603500603200130555980019000800b4a0484081006d82c028036140d968075691070500c090010070517a00d03184a940b0f4501508030a20f130401e5550100c1344610483c03010700d40750900960060100030340b08041e0310707020400701d41140d4492180301e001110584031740e140100b1380303034074207290500f19522180c800d03901c01041d40250341e440c004215200d5040f112140d45000c4240410007100056100520045502c3c041c440b14010041c090b14242241c1600290b17155980d00e000c682e81c0c0c9180c411138021804920110b038075a03511440c031590000b0054403292038812a03401264003078080c0e41c0040c0079665031b07a0036007030000c200703025000e45c0020440c041c41c20400c024001034024070003031048400c2c0c00380016030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 729931115 1250 729929865 729929869
    0x90708070e03121206090109020c0a0818091312030614041526060f0f0a050601031103010f061e090b0a1b0b0603060604090506070309021c030f020d0329 67
    0x10300c42610078100c00c0592648001046203131400b07015030340c29210f00340d0400081030302407482c8203440f900c402201c0205407510082c3c50784000c42d44036a0601005403a071120102507070f203800707040d00c0c01501c100c000c84c1c0c20810070341803001c0c003008032284820416050200801107240d600006a01c221b1003218005480062142c0d404490115a0321040582a2126403005003000090101c4e02e9002c08006450199036503440b000c803410004c0702e030381d03402c0440000410003000e80c45c1e1010b41e0120060400045c09a80e94202104c160030903841011516000031082c042c460b440f291240e0104442c08540c82c0e00707540d940300601000e8041c058015010400f080700c50407140310340c030f0903420121558030040c0358100c0c1c0d040c500034034074045901a0180c46080301281d050300307040c490070203043c0d0801c0250115444444085024049290007640e0180440481c504003816a403000b00e49984a9124540d800e401103034060f0a02900c4882141854034001064090391a800080300401d065a2207a10505000c900 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 729932365 1250 729931115 729931123
    0xa11040e1516120e010204031502040e010608091024140f240415110a03090306021803030d05100803030f0a0c030e0102130302012312060402070210030b0f090708070e03 74
    0x9200b1069013011400040820706500a20550340030320240644504000000f0051388191312801a005030b008004028039031140c80c1568000c03c5400c20f0382d60f4000c0c621300c81c109566404030746000c0c404584c1e100705c01142e00c00c3c0d14007004144550350440f011100c4000109145100754406004424080080085036000c80f0009240d50780308000e180c80741e8803002c0484030b101d66081005c003c54401c0000c040c000b81c0002d9005042030385569084030260a5980300c0020f17421011800013400040c0900044640c0c0500181c040113240c0d0000080c0c4d49030404c1400941005580014100d800400070320024081000c41154004000503000c50f208407805012801003038104891251548042800e080790503001c0b600c0011a4002d0f070b211f0713044840c1d0116070b41a80d00404c0d442c90071518100500303800030030000c0d9407503803103000200700500f0318006801003600d80d0960407112000940c0e030400c0c14818904540003080782e50065030410303010325041c5400740003890003404d202c003400300020030f08005a40402c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 729933615 1250 729932365 729932387
    0x901141b040f0303080105090c1204330207050c0f1f23070510050606120a09020a0b0301030506070f0e0405092104080f0c01050906130302030a11040e1516 68
    0x203085103110f56a0a00910072402800340e548070f01190004510300102c018103460501807042d044440f2905c6d01e5503015880540c0b14a6a482d140c8071031020f0a014460300c44100c2da41c1100400942da179074241c640715042020704100d95115070462001500c2070b4a0f8a1007003c80d001c540028448401600d920aa80d804510766004864a5250980c602c019001801602d0340314850303030440e40c4101100582e01d003600c5044039200c3c0c01c0f020038401d400d00060036031031090b0410a202000900348199030003050005e15941c007c075040c44400001081045030402000d940710310245400880c1c580c1056000b8010100c0c0517602c4d01c00c84e00d54001c150601c0d0140918096440381400602c090854511132034503d0704141702c0e44ad03950190f502821000840031400c2c052540e0705030b5525190215420410140390041e0380b1080e1205224036011006850810002d11207902a00c0b0b00d0465001d181c04001c15200c540d007800b0610b4000c00a892881d0040c594115000320460304030740352108589208403003103400c003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 729934865 1250 729933615 729933629
    0x50111070506030112050d030c12020703030e060720060c03190f0923070b04032d031812210201090f1b080d1407080c010c0210050901141b04 62
    0x4000601603d1488104140c644206e058505541c0c000a082c1c0440f8100c20b803420100d444040400343c004031560052170142e103e400c001840a61a5810318030b8404100e4000e004510f14120b21000414507400c0c1c0248080b800e4000c060342c0ca84030880940501010344240d50070140004024520303100c942046400c84642c1d141000f06140c0c600705000c5030038642030140130a4070401e0000051480206016043e2080c4400c0245010310f1940c422840302560304aa110142080c0025070290503044641d4581c180665168030348407044c0d280c0d206064803a5031207551100e104c00c01d00c0c40001c00741c0711035006440131251600c8889080c5081130380500341c107180081c030840300403510500700149910321418030849480c070500e888c1c0d03c41e5146075840302d0a56a07a0041901403940c80c0c080400c400c010700040784a000c1003802e040c5c0d00c001c543d00f5116070050b10409070304448403903500608c4510031903501080302c100030302a80b01b0202080448400140a02107400030301d8a60045a020f15000c540090105c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 729936115 1250 729934865 729934867
    0x1207030c0212030d150f0b03042307080105071b11090405031b030d0606050913091a090d03200d0f0212160305060a0e0114030709110403170c07050111070506 69
    0x1015107043d00500c140c41e5414100c0802d00b00128154001c650306c00e09940300084030070f1440c2c0b2261100e0a00a40096248866618210380381c460400240720740001080240004280c41c240954003a2030039060040501181001140b1000455908016011820030541e0717401e07101e4640303040107400e40c40742d41c0c040340242c1c1d120920440320000020040018000c421810441691070300e1040b1228807602c0c000d1540300e03e450450120001c1243e210714000c520030864600714062000300d111b80c1000860750080c1c50b070031a0200130b40c0503030140100141c0c11f072440c8a103c0701c010004680c1d0410701602500c0100c4581c0c4036240000310031300b40e0454003400125100000355150403c070b500c4250342c002d1140c4000070b0500010420310b0401c4da14040a50ba88010081d081da03007440c1102e50800f8003600425030600c00c20200040c2030320207100d40480d804591100b5943c0b64198204100781c2c106140441704c100700304101d00c448103000851440c0695000f40791811826410510b031070300d4038025401003644070f40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 729937365 1250 729936115 729936127
    0x20c0f07081e120405061c14090c09060603370c02241914090706200322150302070204062114010e010e0303181207030c021203 56
    0xd0001410201125064803102c00911488001503c6021500d10060406000d120030b1203079161190240c0390000a41045030300e0178040281030b806a90420781012020f0041a041c400031003814025a80b032801d0580707070074280e07088c079034040740d61440000c0c2a001036010094a48880101c04807505059680000040b1901f46c05600d022000303085401e00701015100d42c0c40945a0010408608852010201944245951a1800509592203060301340e41d07030540d600541c00501c03a0701ca00642c000c2040c1d600818032242007180c043c100c000c2d034603401c0c4000c803c400d4841c404410004115040251038170f1014004c2550045071000740401a000b650105009120441d01d03d6070640c09821128002c0791305001050340c0741850010218800303038003003070103058440940c04079992002c1d00702c2004070000000b590000400780f0070300719a055880141c0680001091208010000d9071281040c0e07900800707010404540203600c138480c800c90900400b07201c0600050b070f095503208040b04101c0c100500a0f40ea07911 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 729938615 1250 729937365 729937379
    0x15040b030a02031507020601080708030702090a0906150513110301230d0506060301050a0e030702090426040e0702010c1d0103062711030106020705040f0e0a03050307030b0f09010603020c0f07 84
    0x80030132113480f001440303003400004001c0c9c1c002441604403080c03800607514112003502072010307402006000084164486060f90006000c901c43e043c11500c01075074442c48103040604102490030921031200744d4034281440100401d5000049a0460303800004410024810202c4107901b00c0c80101c20503803110b000c24048040c850040781c410300c5160100c008001982da0008104100c5441411114040d4001d00041d001801c010140540140c01801c0070412610f08102144a645003d0815008000041000c10408980e1030b032441d0840150300083c0720988064030020041200141c415046000b98141c0d90126402548408098030140240c4c0034500041001c0741d0015850201001070b09180640001c00b03010020143c9059415a50190010074036145c204070141414101d03498425a444181240388071042101c20070491180c1c442d15120324241c500502154044030841340151000140044650390340720b00b0506403030340da040044c2c86200107140b4074038000c00d4002c2403005203d07205003ca030711 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 729939865 1250 729938615 729938653
    0x13020a02061807030b0106050d090c06050c060f150d11061303120207150c060b090702240403020c1c020a032a05030307061d010f050412020615040b030a0203 69
    0x42c58842e8045840c1500904030556200d003184406013204049100600c02944a10028010401d40243c0890358490307684603c0d100c01d006a1100b001301e400000d003401518401d00c0b12961044070a5042c4c1450b01d44107044015184415250600c92002c2d90500c8007082440264200d20140c0600095100ca401400b46189240355010a545620080509034141880002c001c02034500d803a03540c040702d42400c0400e40d8100a84c400c100da145071036411400c82911060242c62041d01154018000c14104c1d818010703c80c0d1f1203402c511250301d806400c1201190f00019403c801c0c0e502512480c0b0f44482100c00b13440400c5c104403000303600c1400400b0010900103019905c1c03800e22414510301003082810120302d40840f83c0344c89900e1f0142c006108440c040b5200f6406451004014410b0030800c0005045003801c451002c50340880305965801404240086210031004450841c0018811810241c1c0c1801001c0b0034484040c1c456070b15050010b0071510207010600200d40d01070100c07080008400081164 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 729941115 1250 729939865 729939871
    0x100f0c030501080c0d02040c05092215031106070f0b160807090503070e0408073302040b09040b120109062906271c0204060621090213020a0206 63
    0x2074149000840c1c8024040b4034156810f000411140c8040036030f500748009000b000d1b01034414404140040c0590383c4a445110310071405603c518010040604501811101c100c0b00d03103810000d2080b400d000003a503000d459010044122031880c2c8071045031030440c205114501d4003c25414110003807042001e6880c05045209080e07440d00d02550360350300011504c4599500c101549a84114000c000384040044115080783c017684815103444016200c1042c1000517818682c108028031009000040d8950000e9007110050201545068038006081c2400e004000707100c0e102e2a504d25110a26a95800184c00c140007030400034003005c52a4202a4010540303502c0c03034a410b882c0c0308602c0102c468a00d9256401c1c00b8000c00341814009100c414622054242c01841d5050081c044400d61a40c0c41c2d94118031b207a4001c44001203000725078814030043e106158482d006001c83d0790301e08a001d40666400340c071100589a000600b0091a0001464a490104559140901c0029250700c0c01d40d01240c1588 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 729942365 1250 729941115 729941117
    0xe1302040605190e0a141206070c05120301030b0f1806070c0c1505160302190c050102010f0b030601050103020a031509060e100501020d050c150f15030c10050705100f0c 74
    0x41c0c2c1100c0f8074041d68441045921160b00030701149040c0300d0781c4c0c000c941d101c10001000e040c840c8000c80c0c0f4806585480c00030380c0e40e0408202c40707000580421008004040019140400b66803c5524660750441800b4015010b240f000300800300094001144020300c0c01201c040300104c0d44142451000a865480d80f02c0301a00c0c40e107032600000c60b81c40800030317100390032000581e1614988040c184800d1640c0c50400d80c100c0840c000d03000c048008030401e00c90b28882d98014018101755070301e03200c00a03084901d20f0600c13100340e60529800f5030450f540810b1440c1180e40a00b0050380c2d40305011000c500400c0a070b41451030400250f10049100010340d8080c40998034003100c01a0300d0b440d40404214000c10510515005074004480e10480607c12805031140680110480350380b500c0f01c854a0b60800c8088840781000040031040042894520034a491001420340c042c1505492040200b28044038500b9054207010000a01d8400c114081002c8a0f1400c0341500800401d483c0500c0040a4020f4141402c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 729943615 1250 729942365 729942397
    0xa23010b0f030304060f12021201090e0a030f0e010c15090c0602060408090616050f010905160803040b0a02070f060906120209130b040e1906060f060804030e1302040605 74
    0x91040c0c10540300607050400c00500035400c081ca000011961a104400820104004034181c60300000c09400036041e021007a044d051700070340c101040c8004580c00c00c0491003041e4412005a03000c640c2083c1c14042ca03140d2464048100c0c80307040016203800d004e100c00141406007007402000d00070020340c400b24000784140c0825281da5580c41e412030783d515040e5000b902c0418104401a10b41c43e02d00014803601c1c180100e403101d040d1050325030f00e08060140c074040469945a40d036a4041060601503081001407031307002c0149140c20403000303d50780d002c0e230301400c40120000249078122900801c0040b0042010403e014003582d12094014444281b0744580c0c1302007030003006698090600b600070340f06003210107441d610a20251500c14000f5103911a01160425500c2d580030380c58100510441a1841d10040e8501c1680d440b89030a2045405652000503018034038902400b4641d80510042c0d001605860a140c6155070200051703c8240c0d50802ca00d202c6100190000c2d80c01d030080c001d4164426425400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 729944865 1250 729943615 729943631
    0x50607020607080a0e0c0904050d0915120504050102161b0f0b09010507110a0b1c020405011413050907110d020a020604090c05130905040b0711030901110a2301 70
    0x203a81d9040103558050100c0e00f03510002d41071080c80c1c4d114010044041044509000315440810340c000d906440640d01030f04032219a4191a4000e40342c007004007000d41d90701c4140103401100900034400c4000d001e80b210f85640104040c400250155104061110788000700c2500515081d16603441419010703071a400b0560000408550092803901121340000c440c2c0d140900c1c8000450f82980b0524045400c80c041c8525502143c032801030000140102821280d030300c40c0c550300b0b8203400d4038010b10369078030391030040109021070b90303012000f541801180c14903191114182ca007040c0f043c2e4400c3c1c00158200c1c9000d8100103400b680000100d02c400c942c02c00f99008080c021004a0b282e00d1a004042c2d00144200030401041c13140f64030030f500414030740c80cac841d003459030080005100d4407407507002401c010b03161000e12041c04401c02d2465004000c5003040000251424a15501c901400c00260706002403180710309003040061200c8015660f01100303020840500546900001c40d51840a40301c80d840c0801c8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 729946115 1250 729944865 729944867
    0x3091f09020306070c0516062109020a140319050c010806190510090f03141513060504080c0f06070905150403060c05130e040510050411090c0c0703050a050607 70
    0x3a00c0d950540140c050070303c41d80d846106861110101400712074501c10030642ca0a000900c001040251003251f4644a050540c03102c0440200c40b860084105149414070100040e07494070540c0080b00c4082100d040c1c0c0c10300410000b07042c8900721030f040041224078580c0d0f00411901007544851000240c84448198903020240703c1d240349014020100300150b010144140c0ca49070103000b0b1960b803285000f540541c2c41c3d100145050780035620450f03001013402d49518503200b0071701c03207040140001e4030b00010501e2708111018003071b1140c010141200e80c3d62404075086c4015502202c001c07181180c00c4802800042c050542d41c2e00f41264088000340032800e000c241c40c0b030500c01c00010f40080080d41ea04050550716a0001080e04d122110180b010800030703141c1e400341c0414844001d00d55050011103034501414928204821944c01c0c2d10014034000411000130164040c045030100181c84070440b654400c82da000d20b900c542c40d8000c250344500b00d80002000350000d90751490f1882030090340c4043d20f039940 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 729947365 1250 729946115 729946121
    0x90906060c0b0406020405041a09010914010b210106080603010501060f0c140a21030c02010b01050706091106030a0c022505010c08070c0f1e08030a0c0c0b03091f 71
    0x114400074a400040d680402c4603811060341042c004c010040c0340c1691000000e0031a207142071107030f901c50100306000174245480b074030407030041a40a209100d03c650001c0052032807401400340c002d840401240e44100c104400701c0d0b0710f00081c1ca829021005513141c08010f404417400321417a41c420340c2080f0000c9041845000580c0f00381070140c0300c600b41c2c0b4003039541e49440c0e1035042c56042030760710403140f00c0008106103404591210340d000d140c0186442a0080080c140da069802000543e0f041c8050341c042a42e0100480e5190f680040d00055207c038640340020044080c40400c2d6405800801440049500f690140302140c820350221440080d901c5859900b84004c04500400000b000340100041d50041c80c0e00c60040c1e1043d159035140c22500da445004245954008060041035984103000c500700800c82d490600c3c4c2d0101c01d0040d540e140080640d0380384220301b03499003080100514101040008080701000d0203440c0f610304e89a05d8000d40710f940e14042410113840304a00d4100300c0c01c030305c0c1e041d02c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 729948615 1250 729947365 729947369
    0x2040e01091709040b030604080310060207180f021911160506040b0306060d0c020a0c050111060403210e030901170f0402151207020a020f120c040b150f0901090906 72
    0x1008042d040e080d60801640d030380242d0f2000c0e41164840e000000399540500c04103100b644036008031030701ea0401d001d6403504007400d5040b10b015548017000034000c1c400904d20613002d584201034045060045030003010041c0c0202000c21031808080c2c088068096080b103c6029694015021111070b410041c005a1000c01d03944166508140100003c1c01040300701e400955210f00d002d40303100c0c035010341030109000b21481c040e50007005810040e020410400401a040c0c0144000d1905a00a0f586500c0c03164903080040d00040920540c81c21881840e20280308018034044190b000b000115100c0b0040b0762250f010703040300c500065103110300c9040e501e0f610310958081c102d01c02e2103c01d940c0e00c03903007404196503a00d407042c0383c82801804902c4403081c00c0300c0084d02c24404c9034054159414644140306030751004d54121072040b40c503c0001e800701c0c0e1000940d400d0100302101c01080004a04000c6009001600030981c041e03035000030501c12049580b0010000d0410a0f0b80ba55101c5507103a00a800301ca83c28 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 729949865 1250 729948615 729948623
    0x190605150916180e1e0105301e0105010504020403120c080403021201020a02010e010203240f0603011508011406070f02011106011401031a090705130911040302040e0109 74
    0x30001280c0d440d84280c82c005895141401c042c0503010101055202c1003005510510300100104200302c060000600c50004025801002000c503504041c0050018401c0d2480700c105c210204484030070340c040000c0800c044c8682c0c0300c199a00c144522078500e0282900b4140c100703c0d5030904000007002d0426200f00c0e01125040015034200f0840328a04482c0580d00c1032041e11410b000b8071010015955810710500b820400c80001a03450f051035030b003c0e09480034445a819103900c140100270b407820101700c0f1421081c03005102d0685504c0034a0014403840744072007003560004000b00001c541001c05000c400304284a03515030108681ea2039001303000c800c0b0b40c0e0390420b03000103090220034001420389a41d14032030707441410039140010480d06124900303d402da0001034040000e8a070303686a941c0511800490050740701030200c0c40030308000410002c64000e40610204180028460203410109802401425101f00280020302650207080c6098002c2d000692150380f50180e122480d4805100c1c0562607540 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 729951115 1250 729949865 729949879
    0x5160305130c0303201204030b0703060b1801030e0a060501031a07020706110a0f060c090b07020609010f0c060e01050403171513240618032105040819060515 69
    0x11035401702c0d484c491040b450340310010101a43c6161120a206510f141d6980f118000d441e60f00e5814800143c0030b015180c0c0080c189020010321107010001d04844040c410785103185640b480000041300244a0f05001450b2406030700100c0e800c0000315001141200c3c065640d41007803100b801840810382a06032406805070707010650401c2400c1c05680a201014810000e4951103009030b03c81102c8004940c00803141d00e039541441c0300440d41c02800c1600500b03c0a0546410083c85a004c00c94a1107135280341818014004091014540304880000085070b026801b803100c40e2480a125028020036142100441c1000c4c1c0030000c0d00042c200c640340f00e00904180d610b1001201d10510648164440c0a0074071a91102c0104e01d445145000c4900480c010351640c2d205545032880040c402081039005036028154080d080011400301c51020316079a500001e89085094080410b45030f80c8101d9004a04601640500741e90001034100c805c00c02d039009030701c1404070b690781140100c00f01d900040c4065200d60 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 729952365 1250 729951115 729951119
    0x14032a0d0f08070b101205120309011107121707120c020321010509010803090a0308181002060603010c03061a0c0a0507080304090b090402060a030207110405160305130c 74
    0x2610520391050280034512440d0040700c507440c0c449455020700720035144a264082440100759500c4003610040103a41141140c20405564441d207440f120a448100940084040307480c2c2c000a40c0884003140500c00030702c0c2c0c4e5020900e40b001800f4000710303440300071920350004104040302c03108003603100b081c00d0340c1c4491107010780c80107241c010480c002a180462005000d920400c8086200005400c4940601c5014661400041107042e0005030030002e00781c1c209000300704194881603c0e40054990040d00c064844a483da01b101440c221521419405002000048041600441c0003030241100368028040c1e01421a4180d090720300b513100d0382014911b4140c0c0c3c0c41c3c04040c2c0b103020300912169481581c12050481c3c45061a010094214102ea0303080040c081000852a2141d034a0066040d200450740386002e0700041c58600800d6655020726400003100740421460300f03540500750500034000c01150400c21400e28004002d01c1c001804245807801082d114070824a132410300981c44402100c00368 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 729953615 1250 729952365 729952369
    0xa050a0b030406060e0c1b0a12050c16030804030303050604090b180c030304090507080a05070801050d030309050f24060a03030c02060706051e070f02071a09090114032a 74
    0x2a2009009880c01036540c0c0380400c1517030361900020300808901152589030035545a0507003d10114640780800e80c0d000499aa002604124000402ca400c90031324980b120b094190300341c1441a0010240f000038491a4080200000320011340f081d0b80c006d41d41000b15507515070a000490380034010103002408441c00054442e52240c201410410b51041030b29032071000c0c01c000ca1320715000b5400450110313441d0b00030003202551210406500c108a15414401824450300c0581449018069a8000c099038030200c3c0600d4003d81222041381e900c0340446803810001d4414680700c8100282c1070729407840614840300c480806940c66406010002d20141d0401e01d036a07810307640d94107940000c03a00000180800804101c8600c14107103d480303821142190090040c40c3c001c45103000800c2e440500c0000030002c0b0701c00781d0000b601c4e0207940c0c90300240d1200e282451251012401041c5040d071780310001200110722083c2e403041c504155035098080366016010b0301441452181049152100d400800e8000c00d038034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 729954865 1250 729953615 729953617
    0x4020f040e010806151804030e010c080309060106110a030228050307030903051626071e290313061b080601090504271103011b09050a050a0b 62
    0x41280101051506a0301c01c030000c5491400d82c81001c050b0030030020054041200c13090000000402c941c0d4140404080141c0c2442c20000b810140800c0502c00b400c1c1056401282841c20040d0085941070b10791030000c3c515070f542c2c0002d010705000145150307000d403048200003a88030041581500030340000d0500ca4070801a403003020b80e01d0310451020ba4030b188081942800200a098045d544503030040d415070500030301c0d100144084a0558450020030000301da095400708400141e1180c3c5401c1000d640c26109203000c0356500321403c00c0d00c4800300541d052403900f406d4012151600340d0340b004e81d0f1034900402101e119248800c80c4203e01000090641094480c48030344141c880e82e000a0320180501031080c07203a01260b0204080b5007040c003400810341e003088480b001000300721070130703c0421810030320040706021070880301100b00c001c80d64100400079040034005d0b401c0d1000d03008001103100310102480344681c580100c0085807042802007020f00f8501c0c150b2040d202c004d007520a103a894440d6400380713 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 729956115 1250 729954865 729954877
    0x30a0605060307171507180611010e2a03061b0c070b0d0203040219140103020f0c0d020309120d1d130f0e070503030309061807080a0b042a03020402 65
    0x2c54080c803980810100b00000ca140412000040205088020460302c0245198045e002e0014072a440b0b1701148a1800c1000172000d40d0303500e00d84084001c10905200380036021200015140780030390b03440703481e820b040503019403a0848000181c843e8041e5500c24152101c506541441d01e1651280b000c0514105110040c00740c980d03100c0444550031360f80c070000211030b0031120300a2880b03134001003404154944030400350780006800255000403403800700c0c0c0b0141c560107080414145900071a40205000852042d2000e20101e402a10a01e21680d40300030345036030161134031070b102d5899840d50800c0520001010f0850b22020b4456201440d00d0700c03003100f8001d2040e00020b41c4201c3c405482c0c7d10f4138800340114103444015540120707140710b40c0c410032414a80960082c902940c410700400c01001c100003030f1240c0110440e8956680c03415818051400e01c00c060b000601ca6101d207540410330405030811701071103a8000d10054506843d11010800c051a1642c0b03001c0c2d000c14481420b1015140a60003854 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 729957365 1250 729956115 729956119
    0x9040b16050f0c030d0b040c080a1d011103010314030a1b0606080102160606060c0c1412060c18010e060306011d130b090c071a0709090509030c0c030606030a060506 72
    0x81070801003103101c4265030100102e40c15030303000403c1d0007980c041c090040c06c16896041f00c0a01c813403c03403044010840d8030010500000700e912984d5980c80248000360106a5a007090000c0c04078841258840604d5402848120f450b4080c00b002204400c038080182c619603183c640e03600590600410031001070110050301030760003960f0b03800c4c0000c013a9001d1000380403510036400000c07001e404a040040403038682d0791000b001d12039109140c4001607a0920040d054840a2142005c6e041406000c41c0e1100e403002ca170350b80b0b0340c4501820b01154841c0e02d0083c00340c100e8101c080c401c680302c05c4001102d41c0c88a075032021788c100c202440415002c0d1f00585070b20b0030700c0103060303604031340c00300c041c40000c840c14805981481903966a0f5414036203810011051580900c0c5440c0076841c201d80da60fa8040007500003240302d43d0203215000422204d920542c2280001d213141001408142002660141c40383c0c04843e400f5001e200b00c0124086c0360070f01107160351194100034054440303281d0544440e0040c100c0100059 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 729958615 1250 729957365 729957367
    0x9070c0f12021507020a12230c0a0209010f030c050303040b04030201121b0c0c0f0828080a050903062404150f0303110607020604230c09040b1509040b1605 68
    0x2080c2ca0300c01021841c404d04440d80104524111410202c00c1d8150700341c120410803080204103d001540300a81c6281e038030888202c15a07640203103d290341490b007039020082d809801440001580000131200c207007070340d01034000c040e0b0080d900c50400d40d5920a0b07101d141403000b800c1c0020030266000700d134403440f0520400c1e00414803250030360b41d080c4a038422403550000301c1c940011240c240040c0007010405032042002c50041503081c42001951007404101e8503ea01c13060400c4076861511201c1c18a803411b0740009039603100d43d000d0202030010f400114885010b403140750002004a44207003956101840c1c0203a907101506401014000984072918400750b01404c0c82d4800541540d460364260010350280d070700c105011150302582030410380e0280c900c030704550081d424000030070341041d401900c038003030982d95007182085280020708060044151a910101e450108170a1144000c00244684081608000d8200c680c5080040070740c410388002d010b0130003403800030700155003505002c141065203080c02 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 729959865 1250 729958615 729958633
    0x703052a1c0e030a080a030b06091c03020f030d0c11010b1e0402070803010e0f012705070e0402070c050307050a0e0f250314010e060112051b040603090209070c0f1202 73
    0x824500403107004c0456488000092041ea050303032612408900d107008440c82454681103000155090f8a40b000500c0c60409602c80300e01094001c00c02d42d07411694441c20741c1c1d11485101442e40041486041d00000300d00c0c0402013400000040c0b0640340034440040540d0141c6814040440340601c24506107900140c1c00c0250401060405015600070001441e1800e080d250222860103607100c1a401042011140d01c1d1050513000c03800510400441c0b00540026941e03500d0100700c841420410960703130068400180102403000b8201c1e44026a0016001c4a040d03955505c28440200001d10079246400810710100d8507040c2c4418059810155007110a484046170901d5481d00c2200341c000c40300840c1c0d55060b00760354000e03002421030040000a0901c1e041d403a0510001e040c00b2000303803808507602d0b901c400043d04c1e40e52128240d6103684041810f591110340316803020b001000c00e403070180e100b031400c540011304a40c450400c00440d20350002c58a4110f00c0305a544c1010b01c0510548041580144038035 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 729961115 1250 729959865 729959869
    0x1c210623040641150a0c060905030c070e0115050717120109050a020f09010305100e280213120c2103170c1e0f0703052a1c0e 55
    0xb8414501c8102d18040892561214100c820301c9520b240c40d03440c5400d80c00402640307580d004000d140d41881d107190a9664610724004807584084040010aa08e15006100003030210000c040c010341020a000c6820090b100d00b0600c4071210244541020807501c0c400d00e50b0741c1740c86030000d094003d1042d01080800c0c003080070041c0894001508401581f6103071001040444214004c0760b4000b01c81c480308524203060180b0680092150381440c80c18103480d1804503004806a24510740202a07124641c1e1031414003065071a6021443e001180104409da1024907600190b4402ca80b01e06403200c090b00c00c624a09800c59003017100164080d100000e2000b4005444444000000760601c804000305030f10340380c10b250203044641c00e40703c020310480d80303c0200f241c42200c41c011a0000413941c000d0104d01c40c80206241c5482c45089040390440c0401f1525208058004000d015030b4001c1100180d0700e1541c802d811001c0380c2e0f4054410249074080c0c2c4020f18800710b480b81400c0c0f001c80e140781200500d03100e040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 729962365 1250 729961115 729961139
    0x1a0702150a050712050c060f040f061b030c080f280603050706032304170d0e06250c03121b0e030c04020c070e07021c2106230406 57
    0x14241c004500000f64100404c0001381003c0c0c1c4901107414000e05018600d04400d1b50b444004050b0307032900d50500b0100b020300008071884d0720380d182d02c40e04c00d22204201c81d40f03d482caa05510504d2000c24182220398003828024080d45118403d5024094070035980c160440085d12000c50b1020158890000070a0301a041406100d01030b40c015002011628608030004045a0302c08203c101d04000c840302e800e0240c3d00c08500c844d009078101c05040381c81e0701400c00041e40f6109000c1246025450010141074000b808140c561151100748414242c5c5406070a5407044103040040c811300041e0300d40c4218001a024411140351003002d01400210b11041c0c0485106500078100e401d0042944009181074500e0f00b000804040c1e50242c0d0103508011107441015a214900c1c01101d007504101000607504a02c20415103415649441d12001030500c070303590103000741401d01201214030160000007060080d050058804698102c0e400480d0180e840400090b0501020501c80d03009403682d10000d00801529 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 729963615 1250 729962365 729962377
    0x4030210020c031002091c02030f100905010b04050c03070f170403020a1518020105030a0207020d1401050c070c0303031e0c02070501021b0d0314120a090515011a070215 74
    0x1070000c0c002001d0910415107081110795850048500400080343d064a510420390440d04018090720b54041701440020b00b8014000288032092096800075152014941c01040045001b1002004480c00d12000d00c8150f030700c11540c1c0d01e00001c080000c9002d00d842100d00ca060710080b4604070704403174200742024004000030346069005070f010041c410240418101291034004100108100000c070f00e400e291001c4118050180c140980400081c1c844000c0390101c4140c56402031220300521254502070010540d0b10b0035068140d8641000580e0b002a43e4040300c1ca815017101030b400303200e031a56401b00d000c1c10b400c003400380c5031045900024540340128040d0034100350b0b0540280100e207081800092510ba0b0464694900c140e42200304141034640c04080a55180c143c40c04500c0802c41c1c9001728014416450311041c4c000c54001000f15110880d8001103100b8401c9044d610b10045108480084070300a00480842100182001e0614501d800c000d1500038030103821104100700002d00c40341c16410038 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 729964865 1250 729963615 729963617
    0x50601062c030705060c1e0d1e120f02160809012d18080a080909060f03060c0c0a05010203090703170a02030301050103092109090f020c1009030504030210 68
    0x1c1241030440095091582001003450008004520414070020743d03240807500c28580240030005248450300400c0c0022280d19001c5840103940c03030407520404d0350318441001080c1c0081c050a0289c10040c05900741c01e090b0050664411041040a0030402c00400ba02c4030041c1c00203600300070665014010b001e0300010180502c80044d00c0d0224000050005107001c82c2c14032408100c00b030389010010446082030b03840c1c0c0d41d900e800410700703021490181d0054044d07001702140d0720500400030100800b031401040155029a8801c4e12602c9000c2404080342182061660580110000130940000301019080e81c82a03401103d500300115103c0608a0f4003c0c0c4400d4880d4009920900c10300c00c800d0998101407a100645a2800640840003500cbc2c1c0018043c81d41010745944c00b1405008800d15070110503449508005001aa0b09501600c1c01a070741c13040a007846d003828952101d01c04240700340e072404481c10015203040c4603100034000041c11000821010304c00140070101c05070f03c85800c919403103a11 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 729966115 1250 729964865 729964877
    0xc0305090705150d0510030804080610051c121b0803160c0312110d050f0702060702010b0a060e19031a06240901270518060d080d020705060106 63
    0x2000c14114180440ca07045580240710001e211041c0c10480801c0784c0c4400d6407403030005201e80b109800c4143e6600c0947c07000e000c552000c100803901140110b40300d80940d8404080a080030396078001d11201c0280300020300007050700f81c03080c4408902000b51100c20039109142c880420712900c1e28100702d030848640191170404010081000b04001223100c600756400c182840595070800c0e55008000100e05506562480e880b0b44110310340d13024401c150344070543d444c0b0041c019464111000c00d00b41e18120380d1030703005104080205580c13074010710440060300b1025003081304131030500e8401d54030000510441900100d5480000180301c4400b0b0031a00611300c2021141080030652114041080300606214814600784007128074080390700c400c4203144401c0c111859120680100160346501013620300300181c520465501c1081d440b1600600140c91081b150042d4004c032904e440005c0b000100c40c11500041248154400b246540026103400d0b40c034214003510746100d60b9221410074800b03030301807008602 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 729967365 1250 729966115 729966121
    0x201060f081506150421020906010c0b0106200f032101121e0219060f1701060503040206070f0c03110904020f011808010608102703051c0c0305 63
    0x16801000c00000c01e4000002e00784080700c80000e1042010141100b4410501d440e141c00034011684255401003c100800305041c008940d40d28800d0050158100c0c0300303425000000d091523005504807804541c00c0f40342c0b15402d07801d050080d900720f8004c00c40c41418409000003401803420130420f420300240d68034081d50b15006c410002065190034411803058030b0b214100140f04200295110444a070b81082081c03a02c2c3c81c0002c461000c000d031004010350441c500586480c100112a2084800c5990ba581c07450040c088200c402c403958501941d6010b444800c1c000104412071060b0040c3d900140002e1038240b420003e0f41e2100c0d100742c00307440c0865081d080060708005209116800c84000081610340e10181d16040c0e0000d10101c1c00381d0302407810300500d03000d0f4208256012003000f01408401d0b000b0064a40c1f070b905910380d0307442600c805032845405d05441303c0610280b0484c051540c008605ea0900c03000c030039074041e42d81c4c1d0040c1041c154900401c0c03400b480c01d2180d6004170354441a083d100002c19003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 729968615 1250 729967365 729967379
    0x190b010905060403060f180809090c09120c030601080a1e05120424030c020a0f060608030d0605040c390605010e060a080d02030a03051f080313060c0f080c1c020106 72
    0xd0204084040506800c407d20011034000b400325074942c00101d4110107a41d4980c03040b0506c070f010b03000d1083d8102003800c641c1614482c0014080c018400110100d4101d0380c0c2e03c03207200b5900c01207100014041b4550001181001e1402884550801c0c8100180e40780660a01c080f0060781c0c00030340c010403030301c807000c17145e9010401070700400c842808203482d042c03203c0c801025000c0c5d0b83e588222070040007202170341c0405061115952050303002e4010700c4d050300e64409407042070402030000c034010580700b10300d400410494075009035911018000c2444440b59508501c00c0061815141620400100e41c00017070310800040c810b10885000e032000f044403e0f4603040c10024840c141070b02d6000712860380e1200d451084001e0300001910440b840b10b15000c14541d442c44103015a40780300c0a440030f40043c0c0814049401c280210140c20342020300747c0b64040c0c20703503210822a813290a420014201c11541301101d008284000028032281e03075030004480c1070312034a0f0310100c10700940c0c811210050f551568103000d06 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 729969865 1250 729968615 729968621
    0xb031e010803030420010e030102220b04050904080304060207080406110c01080c0315130e0c09090303070518041b0e121501140a0b0a1e020105190b010905060403060f 73
    0x24051081c001c506600c3c0c00d54800050106070092400d2070503c01159207400e80c401e014030000b8a0000d0000c1d03484200728840b00f49003a0b40485012800190380c000071078055200000d4508540c401020300c4115101c90721403034020307403001d0820798002d03800b005a00c000c0b52413140104010180d03075440207658034016900608140308042d94604000080060000061465050729003103151140000c5205802100040c9440001206148114141111450844004100b40011400649600c2c40e1940e40704429500c071301c41120f100e00454000e011700151460087e5480041040103080080c4821454002071090900e110200c0300051034000c6440031410081401500d285042004092080d104060488018014050310b84841031500d508101d0f591280c161500408100745920740e12414a20018400e03501c0017090401c41140e2172750422100d2051007224454800c02c8001c65802c214056030380040c05040c1070a030b0401035122408203079580c51034010001980b0800c000540405410400010303 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 729971115 1250 729969865 729969869
    0x12060b060a020d11030705070f080c100c11040905010e071e080606191707031a0609040b040c170a050d08060a06030c170415271b0b031e01 61
    0x80354148a1030030010340014032a92512150b041401c20503003034042c82440d60003160340180c164410f04000154190304120b0300401e50b00c51f6000e503580080035005000d41401c9450030340700012030011130b48010448110302c0801c1240000c00100f0a4100c0d030f107a03c3c7c20b560845508034002d803c072a004201c6190782c1c16514200c4550300719161801c5180000640c1c44a400400c010700510380284490b403e1100b80e0a00d402078001201c8800c00c0e50481e661550b62a601408100d514151442a501440040e5508140b00d071074000c00c0100b83d41e84030b680781110030501078011580d0480980010809900050300380e0031078010480180008401c030309100c0d250015403a495030904c034805080c00a50703214607000c070741500d03194100400c0c4000a98011104020b04108008503a140d10341408200156804855841c1032519800e00c58041c80e403450155180702c00c9404a50005002d480c00d0018000c02e2850f0608520050301c03000099958028607015403080b10000a656420860000202400e210305c41c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 729972365 1250 729971115 729971119
    0x9061a0f090c1e0f280804111e03121e0310060804030e15032a1c0608120c0709020717030430030c030908070f0203070e0112060b 57
    0x50350b41028071101c015803091070203070038403200d00c46410390f54190420100c0d04542404e1262036510350104030031302c40f030404480c5440c4900101c00340125002e1321458a0780e00a40e0030860500c0f590035104104080c010381e82c84183e00119030342840310a25a000d210020482c000e03510400c2c3c0d00ca03000c1c19611200865801c60480d807560a1040c403e540310b40561300303429152681081981e079100c500b002c0d641010104881980420820315900540e8002c202071400b90007001500c955035900c581081c42e02142e007000e03110454100784a4101210450316aa0340d102140d80800500c09849040380390404843d1803c50504807030002c0c4041c115601000404001c100e0f02e60214104451075a43d17083c8200104044190501c0c04008642801031815a00c12250749650510b032051052848542c1c1040c03900d1611000b20307240085000ca007600070f024a0301155809a411840c0010903a2110306801c07110b44244d80600c03c1680202c0c3d404803004819028200584130f00152886514140058802e89800c4c80c0c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 729973615 1250 729972365 729972379
    0x1f02041e0311060912120a0807020f0615131404020102071a03150f06070f02030601120305040923041a0a0c0e040902060d111801050c0303150409061a0f 67
    0x1c95101040403150950441d00103680d4000381d00010001201d440300140e11b40107031481100a200c2c41401402c0046503500e40641955611800360b0700e41d0301407c00440190004000602010ac0c8981044203070b000090182c02d680400400c4101150784000356242e03025964001e000035981c04001040013000680c0010010742d0820844044c6400050100d50302d00a850428017400c1d9120f00c400f44084001620032a15a447c2c0d00303160468403021103050f030190003210000700b00b043c20411506000b641540380c8511702460044550002c110720000300c1c070340420a180903c6589807802805011758010b800741e829108445550320708052001d07140391038141ca802150380185403c007082e524490000c84000522002da400880c00c40d11416540642c05441c11181d046040c2207030000d000b1000c411914010600e402d800152464030035a4075100082d4001c0c00019909140400f074642c84400290012403800a00d6a03103c0503940241c2a0403d0005401a0448241003081000305070f094219800 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 729974865 1250 729973615 729973619
    0xd06080618060403050d0507020c0d0501050403110c240d06120302070617010302040b0d2f120312040303090b0a020403110901060f03090f08040f030b09060c19021f02041e 75
    0x14101e031103071101b461101521000041e02150013800f1b101c5c0c00a034040d2142c8010059454200d000304401c0320308402080e1147c40d501000385001441e260b07012400b0b00382c49502002800b41c000004403240442c42e18140c00c11080d1407840b61809841d0051111641c000b816000c145000f074145210b0b40c20000811654008120a00002450f194110b03601544d0000e0b01050b8400415020130300302c034000d092072090241c01312500c5810440e01001588c816000503a218248080080c01005004034054035441888200d000040107801c4d150858070a0800050003c001d68802160310021600d42010a6005c40e0400520034401d1000c0b03028101115250025814504050a0b06030f460100c801050b0391852000304114040d600c00700d88a41046809440c0d0360b0700c0310500500445030004849200700c100100700242c00004d5068010001c88040e5810120340c1d8596500c441065140c50702140b0600203007858402010100b156141c40b040c1d000b40e0303680c1c14000403800c000c1c3d00b01940c04400e4010803003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 729976115 1250 729974865 729974867
    0x31e05060106051605010c0f020c1804030e120a0f0605070c02030a030807030b1210060b0301030f080a030f02033c1f0f0e0402010201060b030f0601140d06080618060403 74
    0x100da81515001e080507500c4507007050030700b10301d9440203500400c25860070781d4181c40b05404c6403801e240c018050f800c58000c3c5083c0818080c810448034914124031000c2030120700080e000b1480b40404100281141c42800d1700b0b04216032a01c2680003080d1081c410380000320b0103100150103102d60254030350030700b030543c0c804580c0440ea80e03040e205009404c2090540201e507981e4869000120035a000400c100000d20245080e035896040c02c030104c540141c9003a8000420705184410f580c101c98029420010303c0032191940203803544001440030801d6a562000500c240030780c4051409000c0f80300900304100b803c942d06c0d43c1454081c2c0820b04001070707800c40702c2e00c44a1406c1035455001070402e0100c41d440600200041170040941c0144a0b01b412185010800403c690a03442c0315a000340d00034016281e940c08040c02030710059401c01108074081c0c002405650080c410741c0296a6240f82c01031600e0821000417080301d203135230007051043e0020340c1840001c03407403000f40c04034001a61010341218142a94 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 729977365 1250 729976115 729976123
    0x9060a0614182d040c023403032106060c03050705190b0f0f1302010302090d02060a080709090501061407020a0308040b04090f0c0504060804050723010206100f0909020d0204020a09031e05 82
    0x41024490884c01d0001e521f04004a40c003510b468905849444c107181d2a0724016080030b0301c20543d1042054070381c0d0340e01c0042085000396400c03a01d40e500d0f4014104410f072001c507280e51102c4403e58003072040404590013403c40b49060300350240500c0caa0406800c00380201e0309068005811070240e030059500f03124a8100e041641202c0c5542402c1c01a5500c40e00300104404080a000103580078101161b40100d032034010380f040d0301c18840303540c3d0411001c0e158085071080702e200f80601000540c507442c182030110220320050605a00007400c105d80142d5903941d42c0103960154000342020350000c9410400800d240c02400c8401030100c40178052100c0743c040050041c0264410182004002d0001c14113103c01030041030060889113145140c0603c0440c43c80e03505070003031411107006201e100f00048500882442041c1615800e80a05019034030b001c2d44000908003060060303034080c201011102c010303600c034030040138609815103038104041d145062039a4680000c4400702e580c0d4981024400016070086 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 729978615 1250 729977365 729977383
    0xf090d0e0a170106030501050103030f2003070f060b090405010213060e15280309031b030207030b0a02160f02010906090e0a18050a0501060509060a0614182d040c02 72
    0x8403440c9841a41c0e0b10380e014101d030b0390018005528090001c0181544964100c200c0846502d403071014642c032081c940810b000c6e0070078801b040d810a1020000050008101054042c001c00000c81d104010304c00050030000195001c55882e90b00082104081c100410120000d04850030806e60300d080c4080414075034541a0746129a0000008828000f4249030010341040a0999600b0000b50706100f00070380101042e800c00e034003151f107083c0c00e40302500b03200e00c94080c29545a1301401d4441e2a41c3d5606207080d03400740240055980030f0088019075558816078030044d034090500304018110500000d0300c01c200540016080200c0c009061200046001e0f08541103a0020000a0b005140e06818600740b403901100a109000300c200ca07005000c2c1c150448002c2c3e0341c0403203844002c0d0300c0d500301b00080c84809108000109014040f40782d00014090050b000048160740c0c030060590500703000800c109080070200b80402016014460069003080c0c1002d400101542c0404c0070248088010350b807540c0781303 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 729979865 1250 729978615 729978629
    0x5090901270501021c0218060c0309012a0c151103040312090f090b03100b2409040203090601180603031b0c0902041d0f060f0603130b0f090d0e0a 64
    0x2203004404000b025412901c08070a0309140d01c0c038a010b581600c81c003a41c031070940d541010b00c0e110415102803400740102c8250003003400096240030038031001520800d030200380340c1c1c040021642000c007100000c0c0600d100c001e80310714030a801b0b16050100710a4540c2c0210003030303403c00c0303600801040d400d48000100c0e4266a0030081210022542c0281100c10721a0354105000f070104401c400103480c0c02a801040f905842201602d0418060414007401c45020401c40f90340156088441c0c084034001c0441c02c01c41c1042840b42c4c501e081c02150110741660320590764060750390309c054010001408900d58403103030590209004e00c4414a10340f0001c2560511503048010354200c4a848402c10100c132202000604081605544582e9105600c0d040d110101c1d118402c0e2440b0b40c2d001818410405100c28452540201070a603180789107024071840307800042031540001900c1a118010820328a05c0358071038104a01d1416003450b00b20646800c0075284401d1000703210121095a1244e6203003e1181c0a40780a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 729981115 1250 729979865 729979931
    0x7020c011d0d1b0f121101210c0e0d1103071502030409020c01021b01021305120712022b170703080c0c0a0212010b090606040e01231905090901 63
    0x24410040145030103e601c540607913000354400059092040c840c0c64a0940076429540c00001580015100c00456034040030388d480328000d20400507051540110207503d501c0c5030140d83c03014900007040d101005400103031008031050b0120051841e080020502801c40c003000c4400580c1d010002940d640114015074801d40d0300030801004810382541a03441182d4441045801071601010040c002d40c01035030103042e68600003101107003605140c040da1000c2c0480b840241901c500c1e10000c110f01c4403140800f280e010303440d4140f00080c10f038003540c0b00e0303c80a150983d920010a080c40e00c1070500e2040710346005140d2041c4009404203800150199101c1400c401c1d8907603c00321004a03504020035040c000354018001ca08205018a056014035010901580d8004464554a04100390360040744038904080c2c59040042c0044950004400d61140581d5040da03c00151000040c0701c00c0070359080030b0000c41884108008915006645c290400802402084440c501c0984900c0305003111010a0640316 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 729982365 1250 729981115 729981143
    0xb10230402180d0605010303023c0c060c0309100c020f090403142209060b03010b09041d06070212040f05010813060507051306090e0406091a07020c011d0d 68
    0x240224150761070400c01082500d02d607038145800130041c0002e010a5006218001d107554050030001c40201d0030022204940c080c107184948200522a406481e24881d8000d00c01442c5090f200d100140044481ca80061030701e504041091003071a1b10100322110402040704d43c004003507103410f51a8001158282d80a8040303685504041d1035191101802055908002500142d4043c2030355080201702c03002e0a18030302299603040845d05031880c4c0d0182a00c13080e010401084094240d00007420002806003010032403a00a800786001011601c000705801c1e082a01048501036050144048802800102c1428141000307000004a40a0300a0381d041c04448004181c1840e1620f8518102d103500c5181880741e45004070b0028a55081082c42c90700c6041c0560700481d10724003860303100c41a00c0161680c20119079a0740c0f84d0502a00c104102540c034a40110070301c51400c1001224584074940c15001082503030000d00004001c804a24580c062518404103e203545940b181d40103036880e500101d0b2004585 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 729983615 1250 729982365 729982387
    0xc020a1506060e060f220f06090501200d03020903010f020301030c0312090803091c0b091f05090706050921062e06050d0f0501030b10230402 62
    0x1000040060040c1800c5440e54110034035581290040c0c1da400d940344400c02d24032800344603041c09a440c18590421085c000303040390040c4109140000e481740c1d40245d108a951f01c10000110300107800544c00542c80007400d100d00e50b00101e201d081d1109004602109920f4041229201c10320484600c04060300020441d42a40d0f094001c45981c1890302e100b190f880d40d407440c2041070020a40b00032291094040100d0200601074440c49081721011409940340001035006c0200031103510035601a216560000c14010030f01c0c2000d841d2040c1010700042840c05814502c0106250b040480840300038203103820000d1007500894100c0c100d901900340a0f03120b207220000030b1212070b8800140b50106034280c500c407035140000207515001d540c3c0da003655910b0203002c0c0d003915444c5610220b220068018503108000340b42c824401400341c0708901c400000c141c0d1483c10000182e4500f27034000d990401400090040e42142000140000c003141c0040200024445402c0034008840c880294807455002c04c4c00f4100f0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 729984865 1250 729983615 729983623
    0x8010602030309152e091b0801060e01050c03370504150e0d0b060f04091208270a020a0b031003030305090a0212030a031a0f0405090c040207032001050f01090c02 71
    0xb00240c084103202401c281190081700907148510b081c041e041c00c40070420003580140445a070749540c0d50302d110302d03070070701c0c1c03041d24007030b980422013810003008220448100c1e00510183c5582c985003074007106412441c4901c903852840c03c00080c422068800303900325a061304041110200c0b17503040c021041c00b103241c650a40f24132002d0444e0030f030400720300004c110030010b071400a90b21609084444080142c1040c042c441100c2c0c00d0310307006000450f01c09040480038040c181c11907010b002882c400309549242d040c40129200102111001c0b5404a4980300071454245007110180078000d040364110b281448081904201503c000380a040c0d032100460b600da14180448041240c0140c00203104070305200840340c0c0c943c8441403c0c0b00103890010180100303e4804400000260020002c1d0203540301081000000c2a0140c00d00f1028400c0403801c40c03841e2101c1c0094110759004c0d8880c007020902d094048030328183c20401d0143d050740350904120075200c591502ea4150345c00004005529542e080c0160300e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 729986115 1250 729984865 729984901
    0xa05010c02030d06060305010e010504021e0406181a040e040302010b06042c0f18010204030b0c0301050a060905010507030c020105120117190b1303021c050a0801060203030915 77
    0x1455091411109060360004020301d60080c40050801484d6941c084c110119502130062503035503041e020040100340f40940241c40301c603000c00a44941c1c0c21a0880140f0f07a540243e00c014040b440d0302d1440c0d211040d030710721054001c16402c4014445407014048a0a0070712490294240c803100d26808076003490300c02d40c1b240701e1702100500000d030789603120740070308010704980c0c04409040c000c000020ba6100d9415943c1c1c902079100c0071040805074491440281d0b0320481c41110011a6500348000004500450300c024040c034110302c8115541e505060a1000c6007100d600480c3c01d00008030010072059034000101d441340c54242c60520945401c0c3d10040724188107584000044809040020032120303001015813903244030030411100c82d4130b44009840203141aa14025007132840410000d0180480c1c40f27030050000e4401d2050b00e4070039040e070b10395002030741c15041c43c0400203102141107155550880031042c00b40c40e413800118210b1400c25500d503a41d401052021203916411000708403034850b14608110 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 729987365 1250 729986115 729986123
    0x90703050d081510020a0222060306090308070c11010c06140a15061b020f06120a05060f0f060702010f030b0a120605011217090a0308070302100606052a0a 68
    0x1940c04112070300406104040d9801d0b050304400035a641e24501d40640302a2550001d80c0140110f40e03e141c080204c00307040702a80c00d480321030101e61100d1800f458031a920146220358000070b203410301401c000b004c00710010082401e100040b82000c010800320045403481680134038001e10000e403645010701c050908228407207680503000003800101c05c55038010062801d0181e6030b00b0102e0790703908003c17070b620f00003848003050600024100c80702600348103107518030030100603001900e400071028180052507003c46440010541c0c8101340601c031b20f000d030000540030a007220381610340c5104a00140c600d120707d2400a05001c1c00c25100004139000340c1050408409c014400d0045c1e0b56504203111004203010f0307085a50ba07142100104c1c169401402690300e064208004594244013402080f000e544200440c0d5404050440c00100045107036005101552195015010a4020651400503190079422030020720406000e5608070024cd500805241c0c2c000d4034000c0c100705105441e541c2011650074010b8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 729988615 1250 729987365 729987373
    0x81204170d091103012702060732010b0901090e0a14151609030f0f08040b04091505061603180b03011a0c0d030c031d0705180606030601030509070305 66
    0x251080320036a211809490003841081d520943e0710003058200c0d00005034104400400312140c0d604000041ca05000071880a803c2038600205500c80640c1c1d04a502d440d001c0d045031140ba4541504206002248200201d000030b000f42401d81e4001441d116050242510b0395039521b404410b510b204001480249400c03a205146407080c85e140544c884101c010103000c520b90b0030010826100e801091001c0c1007120f503490000c101d0450b900d8210861001001344c40c1c0202030120100807501c1180180020410202c1c05943d5602c0d021002059078580c089001d0103c11109003007003203484090403907243d0709024440014a01940c90151450003054203c18980c48070190041213902c1c801d4000d6068070060215180303801c603466a480d0440c4620440c844154008641c10340380c5a00030303009104510400d00700480c0c00d000741c100103105544040003003001580144070400207406c0c000b000c1004101002503420041c50854081641440007814a030304265440c0f002030140d074018403480c0302a56000c0151 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 729989865 1250 729988615 729988627
    0x10309140705100203090f21010609020a090501020f15101208030624041a28030b040204051c02040b090408030403090e04120e06041d04060f05010308120417 69
    0x280ea52800c95000d1035004490050051841c940000240e03255400001c0040391950350f1074003070044e04003030300c96081ca50300440065039810702c0b400e009030405441c4501005880d0755881d500108a02d045520042c1550000f852500702d80002141102d00005c1c8003070701058907190205050b99001640d48083e20300e194011a15040085500003180a9030341103a81030003802d04441c0300c41c2012041250b15440d0001040f0810407007644800c1150040c041c030360a1400e008005480d80c802d180000c019699540036982c810a070f0b1030f01446010903002080c3c0f030441c00c00341400081f58100222413001550740025000c0d000440d500d607040a01e00040151505446007068030b03200d41960011740d4114003003001820049116040500d446100e16000704c1d14003003886c000c210a032402941d0054064214108110200b0071104624001c0d02d560481d078440100c034541824020211034401e01d00591060410b0700420209482c401915404131048484441c2c90f01c40c2e141410485181c0c280a42d103c01c004950 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 729991115 1250 729989865 729989903
    0xc030c1f1d04020a02071805010b1801050d0903050d0608030301080705041104050319120f08061c1e0b130206070308090313240305070f0c03090b07210c080702040902010309 76
    0x403104440308000015607c080000e450301c25501c0034040c10030902c205000b00783c038007100308212100c10b03801810082e150203044484141502d00e0088181e0100f0b4001480780c3c102400c07482510000c099440203036045506082d060f40c9c58a01d9889098451358030340540340307121500402258000c1800030100d8680d480300740c804400680880406980a14900c100b402c20140502913600070141e40e50b48004507941d601040003000c40007010304c482c3c1201c0c90114400000c1d030245006202c1d000c1444a5001c00510345050f60141c0e81c02850348110340090802c03000143c0720207042c0c031744150b454140303030320f081c0d0701c111180e03241d0b00500309683c014203d01c00307000807000d0421100441c030500c00002c02074481d54000c002da064583c10344188001440b42c01c0c4861031144940c881080307081c400d10b040d00d0b8090ba41d1841d8030341500440801d6036000001c090040b00301006695880d444030b44c0b0700f401800d40302161101c800718002c0c00c801a014644814440c02160321aa204440c016402899440c41c4200b60704 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 729992365 1250 729991115 729991123
    0x12030228050706020a0b18100903021b040e07060809030f040902090a0915030b0703090827100f080c0c0a030c0203070902042103200c030c1f1d04020a02 67
    0x40d1154000d00b0000f2411600c041903000020b80c021020410325250342a0102101c0301d02510107009024102081c1c0781542c0900030394400a02a500511034001900000421214001e02c401c1c440d600d004012184490003058400c22103586003402c2e0015038034400c0c00c40c1184205000310300d44440001d404a20341407140d01401c1c106a044c1c0740c0e2007810703031202c1a65007191403401028090080c80002000000c0f0000d202951100c914078012545040c03030b41e60f4004c1d0b90400d21401010480354400700540d50610a03a14a8906c1d0840c0c40344a0050f01c2007024004805003180c010401c41d41800040c021204c40c0111401000b02d202250084d000b5800c0041890031031744400c900c01e0055210016a0a1040c02900c0560390004020342018042c0c101c1c200b20180d80c04412400d100740a101c85072100f00020a588085215001506400d5410401c250804c450042d98600c070b601c6444061a0000c010b0344c00200100c071900306103c04542010900410307030000c0041660040c0002020310025038089 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 729993615 1250 729992365 729992443
    0x230a03030819050702100c020c0a0303030b120604031b033b030c0616061d06010306060603050f010909111e090c07030c031209020d11010e030703020901120302 70
    0x4000c04802c1901d5000d00300c2624410b403005001a44120216046254070781e0000d546220f0701d00486810038056070100c0c8400d94241d00907030109684103804900360500d17a41c55400c410518000e40400d04d05a50042c02014800c038100024000011040c01058040e80b8181c040e2140d042e03042c0c6904501000802144032060520400810000713520340080c203002442140c10b0390010002402d00710103100a5900950128042d24101c4d02c580c901c0c0c03c0304015001070b100800c3c02201800385581141801c4c02900c01a40c024402c05181008100014041074040c0d41550000703100400c6100c214181003c42801140343e40354000050f50300707041c205140301d58680e12450243d48028a554504002c15000c1c0900900540464072400e44800060700c16412150b50701d214140010700d21005070081442c8210078581150006050360f401c4480307680003248084a440d0490042912074116804502840c4041c8240790303100841065003001c01d0f0090042c40210040f541c10108100c03003100d102e0281c08004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 729994865 1250 729993615 729993631
    0x180a0b0d0c080103020a09020c120a09030b090706230d0e06070e09091e0a0606150e040b030a020108130209040b0f0c0c1b0117090703030905030c0109230a030308 71
    0x701803000054080e50310241261340040811507050f00d0b20308928040d41c0001b400c4401c5018103a44540365070524009002c1d9130b1500e40d101e452036421803815440301c0d10041c0011006512a00c02004143c0d441151507120000c0c2582e1017081c1140c4894540443c080d160f0441d01c6141030088500100c0320005545109044966450815880d22030030700c0b842610546440c00c42e83c103e40c43c503120480c003503209242c0404c888411104032030040c1d2240c03001c40d5007541103003044500705e0035031030b0410340c0c48003c0300d500a10459041020240d0000020b03541c17454903000a042c4000b4030300203603519000e040d4030000c483d0003074940c410501e01450b048401381000c840e030042070004a03001c06d441380f160405503801040280c000b40813807003501603040018401000210304200c5610003116644000116043c010703020308004019060951801600b4240c040d00054004d5000009110150303a120300d5400032200c01e4956990141c092018445841c050841c0e400e40006e50348600008265121103124410044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 729996115 1250 729994865 729994871
    0x504060b0f01050c0a060207020316090f0b100219030e13200f04030f050a080406030b0a1403070605090a030c060207061205131b0321030b040501030314180a0b0d 71
    0x1c20300152418052252440d0269000c0410f000004e840765008001c0580020304940600c0d4090800036031551040e040700d08220740742c0d612448281c0c0035004902d090031048404091700000c5840080d95544800c1c0c5994940e001d181708030040c0b601070320f03c40246141c00742059000e03000d011545000b0b41790340b622202e08a041c08540f480110901e100b03403041049400701c0c81c4c0c5018503640711141e4540b102d400c151848d005d02d004040c00100204010030040105071030108041c84a102007004800c415072040c8103101c420030701e240c0c0540d4003041410550705a401c0c00b5444512000c04074061038010380000745441030b500804140540c00140010403502c01c0d5541140d51000d1242e014140c070010f503404070980381005901d80c005204610010750340841d40b03550810f125501d890710304a0f221240d640c5580340484840511440758140180d802c1c4110030745050040d0b52450b130b0300810540d00282420440700700850074201c1c10000d10f0000d035401a000f80400b201d151a041540344035800329403c0760059103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 729997365 1250 729996115 729996139
    0x1908220b0909010e04030503010e0c0c060a1a090103020303040620030d050603100b1c0f1208060a0602010911090c07081206040605030a0203060601080c0c0708030d0c08011202061b010504060b 84
    0x139003d006030f00c03a55065031018256407810884c401c1801c03018003000026442841404501c05d800c011030384c03003400c000328089003442d010200d4080000c1278036400c5004142d04030041c4096180003003100c2c12559a8075050000d405507214081c501d03000244004600c0c08001010b20305902036401082c02450100c0c2511040e01c808041f0302c0c2140c00c0c000d64180c01c903008915414060b45081010030140c2d0049820030241892940c034814080d50850075840402d114400b404043e040845a0341c01070300c568002084a000b941d10340c0100c80c2c0300000c52520500e0b82c50001101051080d0541c0d800c264050442a1183e100c61012a032602c005c440560280345403400000d0140b8001501640170f54014011700040d0b21185d00460728000700800d60003000e0007c004c900380c3d141c410000c0348024000400959103a4514202032000d40751040c081c20200107098006100b161100c803941200d903036040326140e6584180008406c0741484914401d010340d442d110420040c0074094005081001c0c0440751594818 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 729998615 1250 729997365 729997379
    0x30212070c0b030714030a0e010516090504050612031219060b0306100908030c030c01050c272d03010f060f0506033d081908220b090901 60
    0x4014140c001e40488581c46040108070042c0d002103802440c90301d41106040c61013800e0059560040da84414591356641c4141040d48081c4075490b00708151000426000d1884d80d0010030305c20035401101e10441c0e8ee2008a440342e920034240f40c011750307601c1003940e44528900d112020210f6007201e490b071105542800600c2491054850001503e110702c2006040d902c405051100350110f00b10715205000042c0030120344210104040c20708400044010b5580349001391485003501e1000d09840361040c002d00c0b804220541c210501c040111803100c941c07619660365400181014400303240504a4510031480303200a40e00b0b4580c003598210168000d07c030182951880b0f04c125072580c40341d017030501e041030303000d0145140c010000c0d50810003c0e4108002210300c44502e040031488040c03090094906020a008211440030410b0010300a14018180094061460181c5800100d20003030483c80e000a1014040c1c0c40203490180c0a00030240c101d0300c0e07075101e1341c1040d016400100100d10800800c000001c00c8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 729999865 1250 729998615 729998617
    0x50709080c150304030e0111030c010902040b0d210203121e07080c09150d050703061e050612040302151501110102130b0702181e010b07030f051305060412030212 71
    0x40c00b100c41894507598540e10300f01d88400d000858203040260b0300c0c0031250900d80401c00390804c801344900010301c030031036803041101300c44200100c1d41c00b5104510b0750b9804100b20020400c000005000d10818030308141c2401c0b800d41c81801c101d803160b010100c0611a002c201a050700403031000006001e8059100d0300c20507121800221014001545d0401103a400c40c01d0910241248101c0c040c0154203011131035210000b40c4104a4100b4006581c40c103003000f0800e4111615192070380c18400380031500e0b0400011a60900c9102c1004000780c9052010030f040510030407991a41248801102c0c1c07440c01e0800c50f8090142c0800000350000e007000c294a41c40d440e040c800c03990880d11b00c0320400c040e00d1074240e00e821103400071402070ba0b01000c00d00801000c6001c191781c442c86003a480d0b11305620071841103002c00401034180c00808942d00c09000b0000000e4001042c03580100e0b1324200181c90b8541c03040c01401211103170f00300035048071010070002a100721080005818521940a41d40ca0115410440d41b40d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 730001115 1250 729999865 729999889
    0x7030b01080c0906030a0c0302010f140f3106050906090402070501060810020a0e131e05060102011109030309010c110d081b06040b1f0905090a020a09020405130e10050709080c 77
    0x1007c004008104010340c001e8600000d0040141850421203600a00c0c4165907000200070403100040015262808482c003400e0701003118000103030280030201000c51030340d0704076540681d1040c007800103104649965044241c03406402d00500c1950b640741c8030328009002e0f01152003161064480c0c203004001d498924001c1e9181144d8030340e03034030550780803110400500401e124a41038513182d483c06024003101c151109815185d6a0314000300305400c2c001c000a0071500c650403500c503070720018401c860096401000b2294801402d203803205482106040441d021391440d040c29900121022140e010080403c0103407a04004d036000c0341001c169804e81160300c0b24001c80b001807102e000d18001a01441646040e1310507000c0c800c03440c18a941d10b40682400f240c0c401e5075003606a038400341350742086140c42642c00002e4900120150304061401d03010543c034043c40422058555120002c0340004841002215407040c8004401d2025042143c4090722080c0d160003135a0b070342c0c01170850704541400e040408200b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 730002365 1250 730001115 730001123
    0xc08070e062508163e0f19030314070507030209180105070504081014060d03030207080d02090306070203040e1303180f23030a080c07030b01080c0906030a 68
    0x4600b503064003a12810500d44140741c0c0d02410203502030000b0800610203404e0b00b41d424110064190824140030300748001c1d02541c40390441c3c04c211a025204260545201c200395081c00915250104d0300000b207800c400007031601c0d04109450b0088894164181d50002240e001c0e483e024240b05102070440d81c9403040d680e003d0003640c4409810001403c0000010303a11110180840b0780c00800c80035039a0a4800c1030301c10000041c0d002c2401d0000843c01d1003103407070b0518405801c2182d00400001c001c0306c07032002051280304032800098a01414000d07011551069403100c042640c5402c0c030703080c000007504481034060081c801c6900180340640004101c0d130035550305855001440d0744003c007403041101c2c420000c6080210210010221040b42d514070809840c010004102c82420302090400c2005540010b001780c107031503850360301c2c16100403c139880f486401003001c40d550141e07030140070b180000e02c1d4402821901d054000140d00000403c00c1d062008040342c400940381ca512040555410358414050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 730003615 1250 730002365 730002367
    0x40b0f060a0c0c030f030806040b06070f0803060102030d051006030c0206280f0e010c030b0301230702030c03070302070305070b071a090c0d0606090b030304080d0302030901021c0c08070e06 83
    0x25030590244a026001d248a00d1001a00b1034890792441c205500ca03202c11404a0300b49001c0c04002d140601410307807070390ac095078080e0038210291100c804401400101500401300000414501e0348203108807840f11741c0c08030b014030444c2030480724441030013410b216980009250175241d0800340c1c030108001e40101c40c1c000000c2101030000d6003040080701c401c40458201583c41d0701d07400500b1454028250b07001010400000e18510032003002d0b007500c0c50000b81910a0340740112051098161000c050182d258145c034035006543d4070034040c0e20310703c250b44070743d4118800860404101a400901071065070300c40c2040e9070300265035400c51881405000e00c002c01c040942c00f000b81c544100d4004066002c9400b1003158611121040410003412064100b514242e8581000b4040a5014010708d00158410340084d8501860594125211140d142c25903003003540000201e100440d094040c2c0b030008400344000312002c41202e400030014002805820040b46a1a00203040f2a008182d0003180090280500d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 730004865 1250 730003615 730003627
    0x102070c14060d11030402040617030715060317071b0f050f0409020405070c05120a050714011506050c0f0f120c16090b0901090213030b06010e100806040b0f06 70
    0xc06403981c0001290400000d003d80b590020541c0610202c510705540000e581e4202030041c841a100507800c8401010021f0002d1001c807000002200c0e41c10703401040f2070b8a445d2202d42005c0c040e20340340c0e0001e00701d00e4501028500803411800185245d030f1241001c007000e0702001c144000503000da8030581d40040d00d02c1c00104101d00f00107a154060000080000400000c0f540c0010201c032010b590500008205540540401c0010414041c00c00b0410410703a0810b074010a0080031403003203040040505d4081241108070384801d400c0f865010164089000c4150f480348001000d54025030441d404070301c80c5607250504000c4c040781c016907400c5c0203005072407035800329601d18201d9408148101d010703100e5041c503041901c0420b0402000341c04441d602144000001d01003260a10042e00040030303051040000204000380b401801c4200d950050000c41155070300d90050360b5600d003010503140c0082941c0c03c000321a551100078148140b60131a01003003990b0004061152030302905100a400100401036 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 730006115 1250 730004865 730004879
    0x30b0408091806151b060a1b2118240522241a040b0105030f0105130e0313050a0b0a05072303040306050106030f020705030304060c121404050d020102070c 68
    0x2015617241c0342e045d0100c10002500e0322844c1007011580803a001d55100402c40c2900c81f891403640340c3d8040c5280a03010600d14680140303500404c40c0710074500c191b940401c1811144900e42803842309070400ea031851040b2002101c05c9888114270303402c0950707074a042d002070050f0100c4000a0041c0c10394514039103101e1516641d000305808003607010700300c4001440030a030010180e806981031f8000d50220b40306615141d01c0a02041e5808514014103001d02801000042068501c41d241126011902e400708014420045002855000f0f12290380e03010020300028107a0108144100316181991031a0303610b03507074118103405801100211000a20100b0210700810000c1c450102d00c550030300070100d81c10790100c1c482840d42d0b010340d10442d0743c15110801080141c1d0144540f0300306202c0b0000652074800309554031a01c82c0300041c4010400c40e0f03940c128a8041d4030901c0e00400d0803282100c20811a0b4044807541c41d40f0800321002c503945d12441c00000080c61041c02510269940802800103490901007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 730007365 1250 730006115 730006117
    0x80a240614100e03070807050a090606021207030509090f151005070201080604060503030c0601140604030c061101060506130e0901020903032a16420504030b040809180615 75
    0xb402104001e40f00880f8072a1303a40034007000d40102a46c0300100b21107072800041c0301d001120796100d08041783c5002c902700001c0390045541c12a221b03084504558039565440e050316580100c01e061500b001e000400c00900044030f100c00703070252420025209174003508030704102a140542042c00c0001d001481844d00550141034441c2d00060010b10101d005500d4402280c41c0d03170440141c00c403080d031042004100155954281c5091604242c800d00e1030913065480d9601c420484d4441c1004000341c00c1e0142183c600d003035001c2405410300601c03003503850501140480501c0c2a50041da081c0403001c00200e40240814800c464445070064051030800c0710f8008003c80c00b0500101d15a07654049444511a14a051020200e51035035081e1394a1401d00381141c1201154030500381c1164403140080260510b100b03001215201c805819181c3c00402c00b19804031580d028950004003200c04500c1804100101c0303001400c07540d0f40c02d496a841c00001002c4824100006541081e00f00700355050301100d009000c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 730008615 1250 730007365 730007389
    0x90c093305130e1e09070501080708041b031407060c1122050a14070e030709050c07061a090c032202010c0f0b1812031f080a240614 58
    0x161020101d030f5400c500c0012200807220701c90509400407182c82016048420141c201d508000103142417030a110010b401c2c0e14010702140c0a0014001c0040c2c1048202c180c0c10180400c15900d00c02407650742e26045c0110100380200703000300d000d4140007150461103080c95003103094222064180038070384c0741d0610040c104002011017800b151428000010b44140c000c241c010388080d000000c031100b0204441d20309040150649040040030044001140c2e00020004240c6080d6040000c0741d0320340c0c65101d0064818030000424143c04c20300208180e45446803900c3c0300c01d01c00d0720400c140d5078460780c1d00046840210b5a014001521000714044000c10840f0a00c0040c4181401d403005101a1540030109210b0001100e140e6256810010401d00011710b00049580d0f2000800150480000b28121404020f242d5400186043c005118010b0501c010b10018500b05007501d42c1c2c8600360601500144184002081e8080301c0d00002407807580e244919000c480300c0320020545a600c030020010700705202 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 730009865 1250 730008615 730008637
    0x61c11280b0a0309290109060501020a200d060e07050301091502070303182004050907031b0e040308011e140d02010314091011131e090c093305 63
    0x2400910300040581d50f4401900b000c040200817449151000035401d400140c1103107070342c5403e00004010341d980008144615a510a1890400c0d050031202018208260142c1c5540019410a04028400c00d5071149101d14000815144015182c0b02414240c03042510300905108000000b0b8030302c0790055000d00050351181c980440c8034000c80110410792900c000f0181d50706c85103d4800503946007402c9100012580c01d035024001d0b4034010001c00d480b100c0a20018051640031000c80100c017419240c9603000c0d000a103069681703802d050278000c2c4508024082c1484440105001e00c00d9201e540c0350280403a011101e00041e00013400c0c0c18095101d0311040100e0605846920060400e9000c0b9030350780c03066040d04010a4005400900e2505a1390600c60f04c4d812070134100701303039208815128213040542c2d40307d02d42d903d9203011070480907a191038203910550312940f0b002526102254000c00c60022950019444c015a41385030400300c0c060b13400f0340803141401860f1506110954001c502400c812042 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 730011115 1250 730009865 730009871
    0x4050307032105040819021b0d03050903030706090507080a0203120c0c033403050c15070c1d0115020715030f0e0105010f0b03010b12061c11280b0a03 66
    0x60002d8120984038103403800ca03011640400c8072200f005c0500c0200e65049028801404251501c1c04505031401b541031450780544020714401050500980c2118800303072020307040766036030603103802c04000030100c20f0012209400ba200d000030b0262000030f00d044140c3d4004014014018400702c1c01119a84080611200c500555611001e580d03828055003035034401002c1c000d182e00d1400c2c0081c1c0c1114203000800c0d0007440295600344041200015503218000341540c03038a020b00d01c40c2e21030700560b00807040010803400010002050300d0392248422014490a03568680365039880e51680003048801e100100c6c0140c0c4086070800c030366010407455803150070683c100001c078076803078041410940c1c040b2035a10100c0d030745410042000001a91a840040036800300c192705650403d000c2006500c26004281010442c46c0d012401c10707540c03546403503010541d1820302c108890303903441e2000c072114034055040d02c9400d04618440410303000f11102c0c806030b0188003a050701c1909203c0103200750b820807542c0c07c04040d5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 730012365 1250 730011115 730011167
    0x100f0804020406080a26040f0312210c081803070605280e06010501030b031b011704030206060112050108072c07021b0a051e040921020f060405030703 66
    0x2421700091103020700800e054482c03020311040240766410303400383c440341c0710300c04200800c807800b03924aa14050fa03a020400c1e00e0a10783c40031045032a140b140240850054180c00c50384da007a5160780c06004150307210b0300d540090359170302072181d030346440e80c48150001038008021600000d501980002c1d4080740e10b120005071056141e000c02e40c044071100c00c1742c007081c0c0e0703400b0381081c2c01004001003801404246014020154074401003515540001c00d40c5408941201e5917812030380c0118810b200b1a070340001c030708045250505000307640f80740c10b40f00b150204030305a6010f540c240c0c46010f010306a440c80360013061400d190106484181d500c4854004000c2e003500c182003041c928480c00700380140d200e035000300329002c014669805043e058481d00340c815080101c04020940f41d0302e0300124165a42c603403006007841803102140240501040c0104591003030100c1010715640c1d0310802d81c40c0450381d0700310764005510402041d50358801350380150055000b070086000284c40350300a202d03450b000e8224046680 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 730013615 1250 730012365 730012379
    0x150a09020a03020c12190809030d09080a0e0411030c0c12070308070908010504050705040b310608030c1902130c02030a4109220506100f0804020406 65
    0x40c100400341e5001070380010702442c1352501040109012910004820f00e4012120584d8605030315540000060100000c0010400e12080c0b06882264007a08810b021501d91881d00080543c0103101c4003010031003200a0540320300f403510801005000c0c10507a00e1a50300c49a1040c00180c00101e4928028410000003d29600181001e000c1c04c42c40b84c0c58804041c00c01c2440075040341d03100d07084000b0a0389800100004510000b441d00111003041d50700041c03025041002c2007980701c1113040072038900c038469100f01080d60001903203480000402c1c801c01200340c543d155640c481c8904040c0242991004030403002076520b040e18041128801483c402e81c03003100c400c154003940d034030692030005a00003245010029030010b10f800215a00d001604140c150103450403d102d803a4214030b080c40f80b40d44100d070004c5400b00001c0380c10007100200300f11050120060610450707511140c07a08441c506004c00301b640c80c1004e1215114220864444c1e07214410300c83c0080701e00b83d500600503640651120000101d074 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 730014865 1250 730013615 730013617
    0x9030305030a0914010f06210308070903021e0102060c0f071205040312020a120903031e052a07050603010e04060506030c041406010305150a050607050304090c0c0311010b0108150a0902 81
    0x4c1c40800030030b0900d455000303c0200c46443d07219940101035800100807000b84402506601940340c1408c226a031541c00003110040c449070002508111400035090210070902da40d0129600c00f60700b119101da948000e0b40c0b106005410036041c84a0062104a002840c030a00640c15039035645031071400d00341d4a48510307c51000645d80c420241c3c000030303100c0c003d001d03245d088401c4802c95420801000c92550703a000b00100707802045840d07205480240480c0c80381c420000c6898040001c031344502c01c140d4030075484080d481d48030840d519030301c5a403c00140c0b50802d82c041e2030481e84a100a142c459449850710b0300138000043c4100c0c0c0c10b01030140403144584d2640b0642801d155061070000007403801c08005011610b0140c00400b072950300048100c800e645800b03010301501c00980b04182c507503143e894414510b01894004480701070401c020402d0859029000350081402036032105081c01e20801d80300e007202c2104880034002000b03a00013608112512500311200c00e000342c24401c0d10f07aa650303600c5080f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 730016115 1250 730014865 730014893
    0x2508150301021908060409080901030e011d0d080924180105160809010905060a09060603140c0108070905030d0302091f050417010605130e07030c0909061b09030305030a09 75
    0x104102d44140f0916642c4104810303032140c000c0c0c9040050490984604072240950100c0c10b0415480b800d0481c0e91601c203420100b0f146005288480c03e0b01951040c1d00d850f104889029000104010000b48103100001a0a81444916040304003a0821103e04c0920160b00a00d11003c040c615605890780410900c15148106407014000b484603840003401441c0c0b400c0503003540516811328403160040351001c1191900700c519410002140040b901d003960240c8170350380c000340c03200c121500040c11292000c90b4800540a0991710744205a41d071003020f48208944d40111500366200c0e54070030320ac1d14000d078010607289000404483d103210060400601030005003401ca00054000729042102000b42000b4840040d21034000f84520382c01c0c140418140000b4045515041d0f07181d0040404241c010300a0b08040d58000030707035002003601c1d036602c1406030005401c00c484042c90b002c0c1c150112108000410300b00d010b16aa034000003440d40e1011920b940000c1e003c403d002e9559001c0d0000501c514503100c2c9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 730017365 1250 730016115 730016137
    0x31005070c06060b0414031b011b321c0f0e04050405010e2a100915090906060f05070f1a010602160608090c0123070606030203010b1912050304180e06250815030102 72
    0x159000c910108020bd40702120484c1e203065100c01300552035a054071140c91213100303031403429180c0141c0c466000c850780c080b0700c030034aa0080d00d001c043c0001c2c42410f4110282201c0c1c0c0400725100d02d9102c010303500b0440c0c48850000e4448015034070f000030030702d40200542184191450807240d815111107011825450540440c070115481ca00c0070400d0142c180a800000e22803410080c404c07160442c00504079108828005044074a18a58513017008240c1650295090f400300326080c140d82c444401035960008027a03000c50140303100c20f0004045103c2c00c05244a901503e014022410f5148010f40701c0e00e8582030342c08049107134054507511600480c03000d05980c5020f00000b007034841c81c600605007180c5031703443d480d0f02550780c4200102d041e0b02c001941f0800c90b1160300040111840905002e1b0460040b0f80000c0c1e02d000018521203208403183c1c00c0241e140000400f40d0305039458500300b0750046510f00c01550b240c2d8040f80c12282505005484943c0d0014100075404a00180500041d08980c00042c00325 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 730018615 1250 730017365 730017413
    0xc1204080a02180114011209061e2004030b060406170307031709070b160b1003050c0405090c060a03110403140d03020306031005070c06060b0414031b011b 68
    0x60300b5854908020403078070391103003841207840d41411036154104e801c644181d41030242965114801d032680d40e02c44541385402c08410030013011041e040b2055003c6400308104024104041c1100d020b036101070200341d0030810241c4a00e024616541c10360301c03e2000703242030723402552601c00103100f10301400014448a00c140285035140340c0381c82d01400710180401404207042d24030003081a002000515032054500c41515541c450700c560b4400071100c0312881000b4004c441440504c51022250302c00001034912480594651178019404e00048643c2190b90800c141e001800c004002e0614900400c4401070618001c58001c1c00943c2001c0f80c4d50280d8000c554482010b140c05030309000c10b00c404110050903140a40c5942800f0002035900c40c026039441310840c1d5101c01050402e03005000b800309807039020304140065561898070250035041845090212160181202007a04d004210302d031035540104601074501d1480303401100c0701c00c403045080440a500180c08000300d9000365807886400c40351600300c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 730019865 1250 730018615 730018633
    0xc060403020d1106060918031b0106050f03013e041805180a02150c0609070e060406030b0c030406060b0d090c060c120806060d020f04080d080c040b0c120408 69
    0x2030600703c50701c0b907510307054204c00144031142c0d035010f10842d004007002c0344980c04005410201d030700314030402d0345811902e100c50044814034101074000101f211011600728151601500c03e0509a07001ca0010188600c21440d2000d510709003041000701c0d413030851803901220000000041079560140d002115540740c02c1906a40c01552401a158000c01421003c0035001036130000d140e5070b00782404002d1243d80c0102d031081c60700c111507040d03c0d54054080c048407880e003001e60803a610362640b8000c2c01d04440d03000b4000303005410103002c1c401c11654003d840f007809e0307644d40c0450606504003900495400d61601c0e800030380ca00410015080501300c07504005a2603043c1e02d41988003091a910100a2100487e1184003082c00e070180040701c06c1050030301c41e04070303921040051024400d905480ca1100e00c0843e044009603080c0018000307807148502142c00019643d1015501a4401c440c040146239042009002c829968005046600c1c003000480305402c0e2460402400c58200742c0002115502c0f480c1e00c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 730021115 1250 730019865 730019867
    0x4110d052205151b0f0a0e1008041406090d0311091005030a05090a1a070e060318010b041b121e05061f052209020a08180106060c170c060403020d 64
    0x102d80010082c1102030001209031088661401041d415174820340002c0340c9000b650b1701440c45021550401000040c98070409040a09150010b58099031356003c4d44803c000c0f08140001c19a0040c000c41c4010044d8940c024011000b0340035106041c1c228540900900d4415102c1800700e00d040f003415120152203240652000007103800080140c0420344c0110301110108003101d112200c1c18102890000c420f03543c0200949031030130409065074206400200700708420075001402d95241030b102000713002c1000f11104000960b01400c0070348490340e481d10324500005010b034240200e5080a00c41c086094808001840810003041003031301e0049440d0710401079580b400380708008000c400b04007040714201c01444020600d0048201c410004003410080344c083c00c12108116000345a9481e05560b55021b0710790081003e1015200c45129441145c241d4140c01c10600840d8162200d665130641c08410135203490025030000d09041000c0c5d1410000c40c10000d1081c030100b48180d000350010441d1074202c080c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 730022365 1250 730021115 730021153
    0x321070f0e010c0f0503130602010f0f1e0903090905090c01030c03090b0f07120509030d05010b031b09040605040213050a0f080705100e030a0309050a0504110d052205 73
    0x21010100160514080c440343e80202410300700d250005580c1c40c0c48681c42c60850b00d10b00c5107004840101440c80000100550705400c241e00807100000180187c1707a032000484240c2c1c0d00c0400039018400d01c1c0c0d800003a503500390707030024100700d000e031402d0341d451a07454030510b003121410768120015411050400886d5605801085080483c602d410401c5d40226210720100c0c181c054002031812101001181009203c0c40c43d1400408600300100543d00b4409415903aa5000b03240030f060706810000000354032501042921302c200780404010201c000e003008841070a078030901140e0f610694400d408540340d00e03a40b01602d80c01c803561000d800b0a50420742002108250360f4890310450f0300500c0c00784062400854031108507038054071100100946042c09032103401d890702d0281c0c0c041c07088103200f1060607480043c4004079017094902a500301c1c3c1761000d02064404141d500131103034204220402510006a004581c07000801e440700c00013402c91044031844280d200800d54940d404254078100c0c80e55506 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 730023615 1250 730022365 730022387
    0xb1f060906140a050d0e071a0301170601030209040311011b260106050d1e0e030706050f070f18050405240307060903020919050406060305010b1207050f03032107 71
    0x1000b824140541010010168403c2100200720541c032004192104801000164080c0c080415001c0340b02d070040c0d80d000f145400905c00c05803003a09855a0b14038081010490030306a94000e0407401c1580c0c0e40352000d44040340d5034000140c040d940ea00104070345807c114145140c20344180c1c0d4407c0c0140c911071140b0100142c0f05d13a01c0000707002d110300420045030000100c5540e40004000071801c0d511131000c0c141e10640c039003001e005086c1820058601081d0200c01081c60502c1000100701d40d0b04d510604802c84601140c4441c0442d083c5104020000d004040305810030712420010f01955071200041000d4801c25100651801c7c0b10141c58542c5900c500445080f0540c246c3c018615607107050300003000c2940764800a8090b000580c041294903400941800f6103000c61030b02845682060b1070034800621852200350340a51800c0240511450180003401c1c2201490000300601c5040908014a04d0f03800b40042c0e505200170000d00080850402400842d9440344d8144800d03840c0008010740018082 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 730024865 1250 730023615 730023647
    0xd050c0a080a1e1112040c05090c0304110d06092a1205150709080a05030a1d0d03030c0c0203061305070509010b0d0906110c0a1103010902030a0b1f060906 68
    0xe203010280a650440c0400301441d070401c04103140c4800c03205030740c2d1803080c540d80b0007400b40b0150802091060687d20401116401c0e6841809551070b620710048074007041d03c00a00d80441c0100010319454418421000d20780921000210b0750100e949200c6140344100300a240d0b480103218441c84c501309034041800602c18002e0b0078184503241d030703201a100c8074000400356000000d08046501c89200740100001741114008440100200d400c1182d602c0d00b10910706000910901003518005e001402056210f00000d400302220a106940c10707000307031411190780410030a200c0d07200809a138042094500403c040c014880410849082c030604200300c0e0f0300076900440360b51004012030240041202d00700320f05400d000070080001c3ca0290040c00c0e045101c1006102e010600c0030329450045000125180301d4107003a450b0b5243c0c131042c58243d07942014003075030613081503007180081161030148070761010000303405901203400780c3c1d00900003140c6038101000154081809105150700100150b0189082c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 730026115 1250 730024865 730024871
    0x180a05090c03010b0102030927070c1b05010f0309030210110408060a020702031504020a050a0801020a030507091202010e04060302031212061801031b09020f070314040312140d050c0a080a 82
    0x204c680013039501e1007100040350040244111440e0308001e08041a6200d420f201850340460400042c018501102c61500b960317044408000405000c0c1ca41030990304456041e100c14402d074444242c01e60003040901010760640c091000321100c1c03ca4030b807055403120a10300002607210344c1080001c918001008000064980c410030004003d6540010482c0307249401c03c2c880c011554451010032020140c680c010341d0042c00744c240c0411000819005080c0718102a1780800c0680e50301c2404075045003c03449600c049810f2391103650301651050300802a00c4101802c0860195925408a40380103581900610005004202d5800e02c04005000a410800c02ca44018001d100f510040034800d00611004240c41c0485021008032038031421a080100b03008542151035811310003c060265100c800100d0002d0490200c0c2c0102129141c149c03401c1d81e40160502080311f001039410f54032112807154500c0c9801c0c1c113120440f40000c0d14010349115080040405031950480b500103800d00c0b001801021417141 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 730027365 1250 730026115 730026131
    0x3141c2301030f06060308161b05012007050a09060305060f1509040f060c08010819170f13120b0a0c08040305090a2103020f030415050702180a05090c0301 68
    0x200c44104103054a030401e03541204001d040c42c2000c000c0801c0c2c2c0c0002c00c050400f0980e900c1180034828114030703440c010003d0b105240a00e44000c0c001710880c0c0502400308081c0325290034021100841000000c0d0081300300e030b040395103407000203000e04100e5200c20300403074440c0381c01d00401c0f1043c09042c1c0c00c920300004403400e030306010303030989901c4498100b600d020b070303120358009428003814000004109030030080c01c200c401107080005080c003900340540741d100c1c424942d94500010303043c8440e0745041d0300441c14088003507604010642c19400703035500c05130750712040c0700c080a40b14069610b11700034100000031200100d624604042c60300401030803d155249005819060f146d0854030140d4080d505141c02c40c1e44c3c80741d0800280380380f40b03140c001ea030044140302400c64055216240700c050b110b0198085800d01f610b180112a924400c6019801407813150b0b5204500080c0540050618184014010980031001c0211042c41890865107218100d4884040c00303104941880704cc05030040a400a1107a00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 730028615 1250 730027365 730027421
    0x1815050a200d1109060c0f010c050f0d0e210a14180d02061306032306011d182802090307030f02040b04050903130f1a030403141c 57
    0x80a441c200b0892103460b420300008a828000031143e001e04000c203601d03201c0b21030011003030b550009107152480c9903190a0300d07045000d00a1054a800c0c1c403110142c02d01e003048002e2960f014020361520941a0f02c1000300030700d451581240c5a24100703140c1040c00b92164000c400061030f000c000300b184060030004000511881561000700e4030014016a01401d420003284003059241c461141008103c8009540103d0000d5250708040301d002d42c410341079165404070100f104040712050320706901140740415460303140415514040500c0400900074200006c00f0031040750f40700022200c5020820404403607011541d240c44c894280c5121a45086003032045c1c0d2008a5541c0c0b5160002230060007280540000f10350700c03908003149024000e4403c1c07140c0d003841d101e450381d650040d860b0010702020220000c0385071960fa09021003102c00c0c10000c060764032801142c0480f603500182c820b4040050b00081828030203103240007041741c09081d001d201c806212100400045a81c1003030201c06c00c80c050045040e40f5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 730029865 1250 730028615 730028617
    0x1009030203073e0a0f060207030c0b0405090f0901150e07080906090c12030d06090b09251b0204090b060a0e010806150a121b06211815050a20 62
    0x21114030140034002c540380500082000c000c680c0501c0c00e00c03a4040c00490021f50100301c0c202140d11860072011110b8468011f80303000d02882c004d241e08042003800080d4194585000c0a4202c0000000020303501e550100721604c1c2140f6070081c41100c1900d4007071005090340402e81c0c41e440f2110310041c1c021401e0480c03003943c54a4a0800c220312031306044240c100c42d1101481150490891014100030b8107a03100300850180c140000041d1040071070b6400078141103080740c0780b035620141120015a02c1c107110201a5241c08541c00c03170a102c196403103002c0c80140c95901c56400864021000f50703030286002000c0102001e915045206980700b6000104820040060120b070040d00007844a65122809408a000308400b80d0001403c0040d405d4050706025140309000d0703075141c040710791480700c42d00c1d8141540c000d11808400920000003001c444240e10380b5a11001d03100501d090b80c81021a603d84410281c01101c071902d41c0b40e19a62400d02a500c1c40314410400c5203444089105403040800b0034010719 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 730031115 1250 730029865 730029953
    0x91507210b0a0b03010e0a0b0d080304031b0519060b03030903070e06061201150e0901030317150a1d01080c0a0b0307140f0904060e220203100903020307 67
    0x1450349030704030040e1a41e500100038000d042e54000454a82da55010819641003041c2c030755400c468078001d10310030a801c080340028642a080303580f003071560312241e4041761848050504e41000a1440701440000360080c488a59201510b00c040468403641342403560480326421000361088d0b202300052140d50300c01080135800c45511003070210303180d074400000c603000c0e1103480b80311000c6941c2100040741c201c03000c5002c4040c880251f41e4403d4944958014460300210a020240108200410070780000e4407009610b50321510107007100c00c2c00c0d546000481c03201d070a141c011380094041e118000c505900c0301510b00f0300400e5200014001c01221070b0100d240a0200d0069000e40040000000c0440d8014200d002c1504a0342440e42c3d950109907103008190741007600c1e5584500e05002e00040c00c080605c105c14018400340d401c5e441040004054210441110751007207070503004942c03280440405501c5828a182d0013034010390f5507501e20381381c924045030302c00d050401e43c4041102d040300302e0260100c40f081 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 730032365 1250 730031115 730031177
    0xf051b0408070b09061908070210050403080105040507031413170313080d0204030203070b071208060f10030902040203010902210c0702090403030b0907051305060c1908040e091507 79
    0x60356030181c0012440c1c520515801350100352084e10810782c3c0f981e004035031f54464540f40c0e00f99094401c202c007081041d910160780250009000c0c10050005103016800540c03c0841810001640c10600603000350f050030840c0c200c2c0c0c00d04d02402161042c815070a02060340c1109424404d45540341c6410803c003a0480540090466840801d203481c5441c1a135044030302440d001412940201e40e644144c507440d6001c0c450880d441c82504080012040c0100451030061030001c015690300c1c90700109020005510001c07000406840e030304140301607240c610045010340403040000d079617807041c2207040c102c901a6103c0e00c8845d1003030800300200c01e04448140ea0317042e507040780c0324082c0703844a003821409001c2c425040c50340104c0b1403050004264121700140a540c2400f482488815a103a00304400fa0149501c000c4082d0001100c2d87d41f05400c2c138409051692251440c00c0c242a00c2d9004100043e6003242c5000c03050b8400460380460700e160301103040d40a1018034001c11180484240c0380d52800464901c56 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 730033615 1250 730032365 730032367
    0x4031509080706090809040c0c0201020601060503060a0b031306110c25031203140a060b070f14070b0d11070816060f090803060a080d090b0d06090f051b0408070b 71
    0x380401401000710341d00c040c2c0202c0c0030b21440d8a035040005d080d6004106032881580391a80146245000d82d22050485130140c01034180c41c0e181a206650603800140b00c26403080c2c1121000c00e141c441400610f008642070348080d030716880d0501c0d0441c211041c6e001c01800c4078000b130040045945000515126001c12020350320b0184050702c0f181104140e1340d0b0001401403800b03c54140700d080c0e02d54004140ba0402400d02500780e20b40e0000e81c01150030f9402071540a84040040c00080359003403090340119407041e119040244440e1403d1402c000842d0040380b01c44034001251000580d15000b030000030400c01088601d00004c80e640e0300150700c225800503e4400c851a0100180021940414142918a00b003072140502d1850420201d40c0102d035564410480d82201040820b0001191943c980c2141c80782084241005480c800a8019800c1504099181c0d000411000b031540a6181103003c46000424903080c07480c544072100c03000009054204005101c10000000001146802c4843c913910039 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 730034865 1250 730033615 730033631
    0xc0602040504111c0e0709020f041d091b010f030c020a05060a020d1b02030a0815030a080a0f08061e0d17030106021504120f0507060603050705030d05040315 69
    0x40064000e070790016074401c1c90442c0380c000c42c441d584000e110211003513a5100c0041c0703c00110004a444441101101c0d92002c01c0a001a000503030084c904c3c404500c04250400b540d449038618241d50318188245547c0749503081c05044d5408100d4900000e102ca07410f0b250f0500c0f1007000a190170342c004030100c00c250703ca0080d2a00c89000703000c95901240c0010582d40b140c9800c40116019611111030b00c02080e01d000c1c6440d030413000c01c150b0044015070300e070f0140d0b01d005c0b5400c41c03c462040c0094603e9142c0c0313000340b0903041e035617178200100c40101d441400240d407141c0c8502c0b070146c0100c2040c8070318028000c21400300801030755081c00c805505a018036090b4a901401004100201007400c002001d000c0e8560340030100d002000061030407600c0541c219801c0c040d052040d42d90900c03060318000c01c00001c11000340950390041000d203442184a141c203a00700811900e0304010390340d15900a80d100d400c01601880641000c0c81100c4110701c003401c105280602c4c59032503600903640d540b600341016584000b1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 730035971 1106 730034865 730034873
    0x31a03031309200a020c0a060f09090507030e030301080304051c15020f2107030501120506011e260705220b03102a0207030b070c 57
    0x510318020b480c010b02c101c0603200700414100300502990214010500c0d803400360070484480d6006080094019061002c070103e160007003002c0200401c1d802e00e12a412036142012224907880001d0180c0d100704044009220380351000509000000c0001502280000548181c9100b16840c1d80e925086042c1c0949181504a005001c0458041c80c445004172039800303000d4031107108440501d0800080c42842c24110404801d04011003088103104003154940b01d00750241c0f1450324190218a85030719450340c0c44805200e02603a00105000001044c46002c907070307000401c200211007548884000300940c84840a0f00c3e0b00300300340f00340540000ca42c64150380511509850005100110100e12100c10107060f240c50840d40501c2443c032541c641c4001031255587c01c00300160201185054243c8800b4541d102c46110011544001030500c01700e0900c040c0c2c6038001c41103081c0458900f207075181c = true := by decide +kernel

theorem cover : BRFrame.Cov 729856115 730035971 := by
  have h0 := BRFrame.cov_init 729856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 729856115 ≤ n) (h2 : n < 730035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
