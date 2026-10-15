-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4067
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:28:41.167134+00:00
-- url     : https://prove2.me/submissions/aa26945a-3bff-4a80-a4af-34dd46ed7be6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 731294964 ≤ n < 731474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 731296214 1250 731294964 731295011
    0x80a0b280603020c031602240706060e01050f04020309100903051b0105070507080c0a021314090c2d060a0c050c090106091203230307020f03091008060f13 68
    0x608515003074601c4c0c910340d200c0c0141c480450920420b280c15505544800c84e41001202d0348190340d200303540c401e400810789078111080035180385141460200705480400a000c1c161b030002005c205000415000b004065440100351152a000f4a030036801000424010521918440c2c0c949a44400080511400407603020010003447e0b030500701403041c070581040132580501e8206d084035a90b50085400c01c0d00d46104540001c0d004010b003a141c0041c598664003400c003404a48000320303440c0d12600c406a0380c5018080b40b003a80b000d03c001000315290450301032441c40301304140c4800741406070000001c010745c01c481c1c501d0000c81e070701150181c2081001d001c0003020100807524031042d0b50500070028016040b900441c4a4101d242e80d1110905d030045a09000c554010401c089101c0c00b042d81e444419001500d09002602c01c1030140700c00b8030008403d48180c440054183c3c0c04080590300103c44c048009040305410101d2080008002d450b0f03a030410860796004003002c1079080c0d1000d5130380380204802 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 731297464 1250 731296214 731296217
    0x20d0b1806070e01050c0a1406240907080402190b1803160302060a09080609010c090602060f0f04060603080d0603021c0b04170c1c08100b0703080a0b2806 68
    0x507000c02007641c1e04154045080711080c6000313a00d940601080c1803504070f404202802002c010041003000103030005800340f00d200782c1e024541145440208501d08103c1001945502940340030008800f90f00c6038003016440f40c0000c240c49810001713445000782c070540c03d410100003201e002501d000d82c0c5010144071046198150018500c618207060000d21450b090300009110350000200c8514881c81111104050000c6000799805400d00340c0c6050b0007040e403c039014001c0390042400003145170001c14124071840156000c0d00c402e90324140486030054004000b00c030b810340c0d100401300100d480900904840d48203164000342c03160541c010490410501d0310040d158801c0d6103804400945520601c54010f03a00c42d0800c0341c2080111a12281405460355400300d520400c002c1c00e48559070f1112a140d5850f070394075491883d0b1038130b200301c043c802c28038015440620310030803640d00004d11039502681c3c01603140000207054200c8000040d003402a07191003d107a070219040d00340283c10203545890082c00907 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 731298714 1250 731297464 731297473
    0xb0a05130b04080309011404080f030c010c05090d081303200307150e0103020c01090f03051209070501050a0e0a0e090705090606181002030c030406080708090c091b07020d0b18 77
    0x1040300f51656886010300a9040108080200c5203105400c820fa41c09000c955003600c106400c00d6901e59600c3d04192040c018941c20074160f0490700340030b202280c07110304002d00044207032207680c1c481e4000c95000301042d002800c5540000000708604c0d41e44e103512262000340080c082504c01c000c02d03140c180140c001c3c141d0001c2d00750f016041d00e42c0064000d0344020b020b003009a1201000100c1c680106074044c0041d2600004006d6001010f911200918019040c1c1c240d0404a440314548195101038900485000c5901005141e80490044090808028004291550003a03d40d210740b030b107041060b03d0126040d401901d050200d0b00d013a00d10b2a83c054400e0703403298113081c0032600030056560301107592801200c60300e00ca441e80910a10807152000d4040c0b04aa903185da440000030000c200c115040380015a08002003114008042200208000c0c020714042003074442034107154180c03100e418010a0742ca0200450401030f168034581c0d0f44040d0140c4244174075803500b00d01404422001c401c0321101c070b402 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 731299964 1250 731298714 731298719
    0x2010c030e030a0c1104050f04050610030b06150d0905033a020c030f0a020d03111e030c0d0e0604230a080a05091903030e040e060112020103060b0a05130b04 69
    0x10010030b8528074903451412486054203030601786421071103094019080790600040111040c5a00b8015000710303c13860803509555561403100c000305419010040c07c0b200040c010461910b03051a03151409450750003c0380c039098070400f0040441da81c100c03040f200e6810200d050a4596488444c00d5400510040e000b4160014078491b0080303c80b6604c00d0707200c0c065012035040c841c001c00b001500d041c2c00e4910031941e43c074038100c0c4c4007947c1d8083d26640540000d040003002c221608041c8103540414001000e1030b0503501601846902a0b0002407000c0002c003400e001d54900034469000d010b070b2191803040a4030450400d402d00084590351000360b0b510102c0b14900c0c0c0c0700302d290001152a140c540000405884d0504598221001e10540e00e1040d480700580800a40c54280108800c0449200c2e07128210342c403803000144001e4a00b4150700750100d400400041001030181c0c6282a04030307105140024103907480e06d400c101c1d56007104007080002400818403240304950180c2034130182407841101c606292 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 731301214 1250 731299964 731299991
    0x90b01050301050607031b03050c12182e0c0b0f090307060203060f060f0903100e101d0105040b010e01050f0a060302070609021203180604240909060e0702010c03 71
    0x700600c1407030f00903040043d061081c14860780030040c14500481500b00e401c0034504009026410400c0005005d0148810340172420302c00794110340450344c421180d01c04a40c0c1010800000301d046845040414510384249441c0c5605554400d802e040c154442441d0301059003440c0d43c00000007070403503010340e01d0503040c4040500f0000c10380313610030350204002da80c0369168401b0440d4170301e0074004240c100300302041c0b1010b124a880301800c48076005404841e080502c110784002522003c02c0392401c549c1001e0030400c0c003290203400100e4960800c0d200784180300c1941100f02d0848404440c181c500d07000f03280c0140184000820340300c0c01403104441580c194450440020642016881070005150340001c0315420004590081070b00160002c000202400c1c16400c2c00e5101d0780407810050b00b107076840d0703450091450090b0907901982d690701d0007403040710b003025641c0110318020704006003444a00c51000840980d58040c4070050000103005141c0c605107208082d00792854140010141420410300035000d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 731302464 1250 731301214 731301217
    0x618090c1704050c13060501170f010510050f1b0d050408030d1a0a061805180402040b0114070c0509010e090d0e01030204090207050a1e03090b031e150a090b0105 71
    0x503805800088041d1510f141007458040e03401885600901c003080c4503c0800f01c070354080c404a4100b0780fa510822036140240d40d41d503400465500da100000c400c014011400c050b1000094220607050462910100a0b801041c0e42c001541c070600d0a240740030b140303040d44828010f00c03040d2001802c140e401c19040461840e200d00030000420380c51a9a80c1c28101102d4882090220394840075107050300c260388441c00141003060042c1d24400d00707a803400303001441d401c0c6150280c04194440e5080302c0c01c0d0721180d0070000070384918414641003014020000385941c8540303000707010031031107280109100c52409045c13140d0700c3d80590181c02c039140c1c58000c1041034480401d5132580840c0b940340c0030f00b42c0300d00c0000503402030040e0f030016a044e43c0302040003c20004001000c012450042808000003241225141d40d5103004800007030000c1c8000100f0095060344102450f0003507070743c012000761000792212044000c802241c0e020700c0741544d10002c1c035050a00840c0364000d402400801d03c0503070222000a0103e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 731303714 1250 731302464 731302487
    0x40507060507081602010c0b040318060c050a02091506030f060102060f060904230304291c1a090411012a021201060e0c0310050108161101090501060618090c 69
    0x1a0300c0499130500441e8410001070000c10b5100344401203900f0b007801c00030424011005d09004089000001182c0c03980545079464115034420300800011106a0a1202041020303080501c00c0e100000c801c0c81503580c241c06580700340c1018000001030719003032000a2403d2800703005245000b2001c014010f41d078a80d141d03042d61098000d000c5894282d4034088a1001c0303011a04401c0150101241c0490203414114003001c456503084e208080002a51051150754031862400800c0c003100079501c602c0b07904582e0001045d60068005c0900341500c1840400d9450344116002c4481440202c01403000c2d607009070720003030046042c00312071180640c21942c2110b40109c5900c007030b204079045801e119003240f0941101015000003041032400d070400300e24801203500309450500307c544c405040450036512034003d1a224202010f41e126a1501140303007a520341c150300c108200d0035521001c692012910900414009042981c0c0d0141c070000c0d00e40e100c0503107040726008401811b09004040e10700c1c41d8402e54a43c3d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 731304964 1250 731303714 731303737
    0xa0f05010513020913030c12020304030c21150609020703030b0103290d08091314130b070311070210080109060b0408030d0506030304082b0221090105070b0a0504050706050708 77
    0xc1145c024107056405010071800185145640100c01d0715140d4040090001c51b1b1042d805542e100780c4a4040f803c4640035491003c40c9007071074110700f0002c15090001c0c6400303030041c1755000540580b110440b00aa0340080001d401107510307030014840b1940d162050000c50003a070303018101108041c4103103448400c09010014806c0d14410034030f80070f22500c070701101d10ba800020065402c203a045010fa0b0040d140c4c12004075003c84d003020000e0188010404011b0340e40d58020f55070042507403102415802001c800710801d4104009100c18030040c1c03903a4230003500310102c3e6201d0040781d40c5840f20030420748110750403800c0034210601080010500000903508150342c0d000780851a40d0307c02c0080303403460195520a4030315100d61000100c44d010368440d803c90740b0055070510341c10258440e1059a40c2c0c48119000617550b55070341c044800300f2540c140a020203020502d402403818803039450341e6030404029200c1802d034980d42d500348030820400b0007250001745910b0402508204060312000114014400d1140 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 731306214 1250 731304964 731304991
    0xa02100b0423010305070e07170c041707090509030f031303141b010b040b5d0a0503040b0304150203150f0a0f0501031505030a0f050105130209 63
    0xc10300c0c0d80340d40040b80c40d001c1410b00400b0303910a402254060001c00c0c031007900d484c01280030200e1040704010100d8490240740c1c07203442c2403d812004141c845100100000c035030311801d1102080742e801d0080407044024140e002019002e04100c0d40728101e500280565405510400c04888082030503020390303500c910451585080c42401e420151090000134841c0300e070000d80040d4000c4d94810702c50031986550244002001010425070074003003200d65001c1d0701e0b0741c0040c200149803102c0d02d80515514100e500005951007070030490030741c0910a402224015541401d9080e041c60f80c40304454603100f4042d01c1c800030b020180b00b54541070b8583c030850140035400c038000000581807000c691942d00744000b94000841d581d10300300d4413003440b04003100c820911504900d8064034151030b00c44401000c1d5502c1800f51180d29150100540080444040311025100c034480d0019076590300f0300400582ca0b01a004005170401e9502e0080d0845000078408103035020480c1d031a4000d070300c40510140d40540703a0716060 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 731307464 1250 731306214 731306231
    0x50c0109060914130213030506060d020a0315150f1a070c0e07030e07032f0913020406080d0908070b0a02030a110312010303050405040f0905030d020306210303100603020a0210 77
    0x131305024200c041d000b210340c0002034030080050014510011280604140c40341e680b2640204801407100d940702a40c0969031100c144040b90494200ea000c0140c0c007580002d8810303c000c0a003103030082e103900464180a107501c007004040d18002c40c600c3c8968040e130f06c407890305c031f892340d40d285090b01c0e1805104500c0804900040c1840d003c0d80c40010806031510845403111b43c0d03480d00240c5a802d000d25903454000c3e40c69020300b14001790305030240c80000142100d03941c0c0d0301e00c01008000e075148103081c0d07401030f1181d1000400140c01e0240100440090381c403010914180205145403d400760300c05521804200608003130180d0110a80381c0c082c0322803030135220441c030202d22145107011314504922100503910000040581042c018021501d0548040c4600d545600003841120400907024049030401c10000c0d2244089500a542c000c000400c5c99a560301c030003102c80080058008000c14a0b0b00001c00d000001d031445c178850000f40f1031841c0c25072070020020002510b851410030114481034444900 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 731308714 1250 731307464 731307469
    0x3030c07030806371e14011704080703081e070c141c0f02070b0702060903161701050a05070e0111070512070311010f0c1202010609090f050c0109060914 67
    0x20320091000958842c0001c01c00107112501c1c13004048a000c08001144c00000f04003007925401404485403000001442d464107142c001d00411342c1c907a01c0c4c10050605c0d850420f019002007280d001d5030040c825251a0840d92501610f1240003a10041c0e01513582c50516188816500c0a540d02c400c02c0d01e4189581c031424641525a66240f03c1c1605c0c031030240f445040c40340b2840681f540340c00c0000b83e8a60703400c82024a810b9032103010354001c05c0c0c03400c1e00c204960000b608003040180301001c1c014040380c1102500c2256003150701600d4000401e648450001114445024011903400161828013080300b42002a0040c0c0725040700884e881c10b0203641e000c05480300006000c0200103080150000c0c516000c003800e55030725509140801c8901199040d0040320f5540b066008c1c0b058031995841d0f600098130341e0b48402c116805042d4607241159200d81012a0146581c0500c114181c49810020394402c45031070700c5810240c12455580c100007140004004282e80400704100721110700c0c9100c0c0c862480c8001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 731309964 1250 731308714 731308729
    0x30a050c030906160213020a02210405060c0d0306050301050618040c0509130506101a07050718320a0f1416090801050c07030f120501030606050102070803030c07030806 74
    0x80c01d41e8441400705100312135071000300c05508010320841e10000031144c154a04000c138000c0c50048001a0b2182940b860142103541c040500311030303d0180e407820241ea0320001501da0f03004000c0211a900441142c410598040c00b41c00064a8110024030a41c07601c00042404030a50b100312070035840c3c030180401d05000f526042d4002402000c0c1400d00d9a00d031245191500468255045609101c0c01001540418142e01060165002d0500c842c04000703d55410365040e420442c0309640b603015040000074004070422b11045c02d40000d06000c92110794040d0b181d2001c40c068910390300071029901e6400303880850700c441198002e415160000b5a44c0148940e040240340c00d07003420485819040c00d12410007440300f080040e243c1c6650b1401e00c0c1c1601c1d070481d03034243c440c10f40f00240352510038058000000e0141845040c00962441e0202117602450868810307100281c1c0241c03480755803900c041c0a2541e0600206003d01443c000462450520303880444151041442c050100241c04c0040341c102c1d40d40e81d4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 731311214 1250 731309964 731309977
    0x606060307051e0315191415040e06040b0103051501030e0a0203011e0c11070b030a0e011a0f0a050d0609140a06150f151d0303040e0a050106050309030a050c03 70
    0x2014202904030f40f0f120546240c1c03007500d4801d98144228400345040c41d08080c60120450305603100554a0310300050310340c18140e03614039264080d842000c0c0d4043c40c0e4a400c00b4000400400e81400c006e400e049003400112011080580e0415041c07404100700380d4080766505c215901c0a290004d0164400e240c0617007880f2120000075815402d041868030001c40c1d81d08420036060f0705000c03c001c80200700c41d041d07401806045200c1d049070880c0c00c0404c041a260310141d640b0100114000c66040b4020035010308484014158030344400504058001a00300704c5400500b200c0c007916648203070350800c400185404080c0b14021309013511101d07100208018012504492015a02101e02514180c500300c009010320b80901d824415410000003041403100c0e80050898803482ca05400f415540c06084a012130072038510f54030807144000c03420947d2004c0009000074400804040003505044588400743c8006138171000c1001014020b01c44d050001000300c3d41d440740c1c1d90030940e5691010a0007a4110300030300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 731312464 1250 731311214 731311237
    0x8031305190303050a0b040c0c0308070314090a060e0705030705130209100504180b0f060a2304090f090305092209060207060f0e030919050a06021518060606030705 72
    0x100716204168041d00800d000c0c04908205100040c0d44000740000c90380d18005550001e00400c5811020a006500c9a1780200c1c0600d80030401c10099a600314806030281d418030381984c880b60f05c060038814180301d00384002d00008040c0c410b081c070302400250344800034014544aa162031220303a0010317416904413046120043c080c4001140130380409401500284201040c0801c1c031088003801c00024410711145140c01413500703040080c0f10051103d150800c02c002c1052201c00c40c0c010609213200000180c02e48000380041c3d541d5420903282070b0075240d24042d2100c105060113507940009400c20241c9034412429500c01e882d841008001000070125032155650032458950b01c24103100e40c0b074001b021311900915061108081e01c0718900201d6410a0510344950818804c0305410f1511341c8102010054421a070840c160b2145c00080e00c40c0c00300d9010381d0140c0d010140c030114102900e041594003106084543d900318820800190325504003c29141c400c100000c00a5061409141503940d1080c40 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 731313714 1250 731312464 731312503
    0xa0201140c160b0712231615051e060907211812020a02090109050a060512010b0103050601020601180b0111010213030c09061d18030a0306150c08031305 67
    0xf20005a8115400f1960644444d166412180303140ca00910b034002402e42285a041440d04104003500c01c079800040c0d031441c400b100c0d4282c2e81c000ca100500c103a10084c00002c0005100d04104500128440e0046400c1283c17101250030400309070384845102d40c0c8050203051074414505036100c00d030250180030032000c0c84036280c05918148541d40aa04010f5148216115403003030000441c00e1741e9521105000960000500c1c00511604bc0543c02268200c0070850000c10010744910003d01c0c40d070903940000c20142e648172450f580e103680c1170141756002407003030010f8800d83d4105456a061039502e100c1c610711041d20389448da1410307485801665901c681c1440215256000f00c240f2440140d1103200a0715107800b000b4000c582e00700240309410440c1c248001c0c540817400440000800c0042c010300b800358600501c060007510140a00080080b904541c0c0c0000d41203007482600c80002c015100e5007010044142e40280001d23012404890b04103241201c8a170041300c3e14a8001d1402065580f540602081c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 731314964 1250 731313714 731313719
    0x304110a0f0312091703222c01050d0209070e1c2405071d031603080406021216110a2309061c290103080a020f0a0201140c16 55
    0x3241c045150988460390f848021042e42c5d40045030100034080c1810441c0c2d00104030300340c844021108048100340303440f40e8515649603103900001461541d845a82c01400200c0f80ca1720450780710094440c007404045030711940c01d002e641c000c1056200010001c3c01404090b100a1540380e90700d0341340d51080e43d1107400c0321641c010540340501080d07540c90b00c5e800e0340802c0c005100142c031169010f030900c81e02c0030340d49038041a070f5030b03040e0203011403c14009281c140c0203015010842e0101c0012078005503000c1d0828a96441ca0964000d1801c504680c0b82100e00c6006d00c0341020112541c0081d41c40d07a500030030400b401003000c10004070030010030390283d0300c00251503800526008c1080d800c4c050385041150003a185544603803e000501148002015088165000c2e0b00700281100300d102c145816407160805409030440104030700c0034400e07001a1800c541c041424940d141c0c3c1003100c0062400e2442c0078003c00406940042c00d45415207200382c1d421000414807420361038041004940b1400303c4103485013011b5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 731316214 1250 731314964 731314973
    0xa0503010605030a0e03071212140c0f0d0c111005071407030215040b06150c0d08180304031109150a0b0f0c01061d1605090105160213140612030304110a0f03 69
    0x200c03807480360040f5a040200f042c12707810510a0690080803261782c4802940d030454040155441802090210881030003c001000000e200e000380c1e0510945420500154411100b80341c505001200c08629080038200681603601840c00700310717207603107601c055118100c1c0d2800707030305100c0c0705412144054080c01c208400c0c088048941ca00803071050b24403181c6041c0d8820400a01d02c56150804681d41c000200c03040420b2041c03a0046d0310640e280e1a9122960000d401d15045034043c0e4425150f0314802440740b00e6030b181401c221a08000140c09000003044e203800402d180708035a100e404090b08000c5a03111500c8201c6044520612580e4002c00503246c88040100380c0c07100301381e406452010082c0003c1c840c01e2820301c00100c101450b441d01810554000c00445890f0b001c1110202c4010410f85034600586452102084200c14160b0129131b41c51101c40c1c1d6040c103203006103071620440c1d4079444040307a0800402202e0f00207070424010390052403084c001c1540b56070168800e030754580c0304480000610 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 731317464 1250 731316214 731316233
    0x14070615060c031b0f020a030c0f06052d0d0f0504140c091b04050a230402040f03060506061207050d1a0907320a090b0a0503010605030a0e0307 63
    0x5180c28005001481e21540d04840c0c4070500703000140420f0010328010101c840440082c00614400e51100180c01c4090740840d162a400d40d1003220b0580b0941f00600000c00a078019001a0555280040c14a40a8114901c0c1c20f03195410702001300380d101c040c1d241d116280208544920095850074801c0ea070500285a00415044409544c007505880c690030b10048041080303103220a0042c04000e854a680d1117103500d41407d08500300d84c14508100c0007803240c4075001503500030844402c06000c4c0f01c000c80d101312141d00e10200110b110b20b104210600182c2e80f05407652080da40c104400040307a80d00c03903010500b507108024104000542c884200b2200e2030b8410000c0064050003d01403049641008072000c0b048001c554056116607101e000030081841140d00c02c2140000b00320032200b0701d002c03820700e1401c2c80c1441b02c40c03500000000780b2051000d4000f0b214000400d40081b190389092603c0e10014500d00041c09440c08018000020521900140d0004911300c0315600a50344e95072820301c1c004001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 731318714 1250 731317464 731317481
    0xf1b0306060a0302010c140a1a04020f22022a010501050a061b0308040302010b21070b210421080106092102010e0102010f051e0c130302040c140706 65
    0x40d00c554030028a4505114558108036030341a1284104c1a40580d18003007000c41c0341503481a1842034504010100d0007101c580d4060100144149901d410b2900600a070310280e901c1c0b19000d05140d619110f82e5405e80700300d210a4040031080180c5540020700c9080307501c0c016100b01049a10102c840d0481090198800d504aa0003119100c2c0d2142da6004103440907d04140c8484140918001132008280148402640a4424800001c444804400140592107d048011011030804400641d580c104204070406000c550a4a50400002611850040100044e040b8507103078030070042010040b8100210301010f40d0701c29440c0ea60650158010500c43d001d114010028400fa100080c882c5240100b880c04c540c84100b400f10001c0311900191141150390413540c0c110340d80c842c00418008002e105007030013110108a41800c00b003039245a5082e105005c1c0c440088140c0070007008598042c019280400c580c0e060710701040c82c10701408203444d0748025201001081800041010800c11640d009106 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 731319964 1250 731318714 731318719
    0x31602270a02210c120703020708130906050d050309121212060f010504050d0605070e10030605030f030a09061209060c0302030928023003070c150807050a020f1b 71
    0x248107061944a400c3c9410340710080c06a1013040f40c0d10102a00400103507000000c0d0601603d84227140d550140550311180d007054290303a02c000180030307401c010301410005003c12901000306070760f551109512403040003902c910940000071070b0040907509010301c500c2c43d60340030074641c5c40e0b0f8425445504000310807180d0744c0c49000369803045c0040d0741c040c00c00d690075500058040c0703140310301da0340d52407004041c0905480280000280e0102c240c0d40d4120548401e024281c0d004181c1c5480c11062500c2c0808050608616400501080340300c2c80d4049920f2003168480e140111a29130480306c00d400030144c0f050050300c0c4030b090050684080790950000d41c00388813880f00f2200a0501c031030011a0b03c4d10010075121031880e00400b0b180140c0341c900000011500b50001c100700590b40b003000d940343c200f00040c6902e00758002144050038030140607503d10042011a140c1141c50b40d2966005010a4000305500c0502102298021a01e88200854000600c0b408210303814085601107480340341c03061243e940c1c0b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 731321214 1250 731319964 731319997
    0xe06090c1008240a0b0702010215040803061c120e10080408030c0c01020c030d06050108010801060501080112060f0606090f1703040302120307120e090108031602270a02 74
    0x58641040340754100c04211540e9900c41d80c0e15201e01a403a1880c1a0803140c2c0c19200c41a24010a0f03903070078005034000c19030211003d1760781103a480007a04202c450311400d055512807200300004100d001c01103a5020004852505100c0e1440724980b85c0b200200c800a00395200260716051903981080000c0c20b00d800407110b17400d104030420400c0b0f07603040b07086900401d002c50a002260480c1519406000d48040d98070001d070510208a0810b451900140000c862075a2200410085940c002c0d000a014044040081c08a6418500003030b01c45003040c89010034100c801d1001d8400d000c031940c4100400200c3c0f4805112407580c480c030043c00400d181c000d031302c40e501d039102e400594108129070100040b810240a5030416107542c0070400d201c0349200300c0202d1400200070b03103400605110100c0b0110f030b07056240d001d001c0c0724440c14444100340c140c204415551003000a180946091680c2c009407603412039801c014014481c1c0c540b102c01c0c1e143d8100b01e150746111b5091060000340c80c1c02800303011541d1107500 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 731322464 1250 731321214 731321233
    0x16121103190f0b06030a03120e030405030f0303011502070317070c0509180c10090b0903030f0c030a17010509041b0b070b04020f1c12031b030212010f050a050f030f010e0609 76
    0x191a81b41424008012130810245c8541c5408583c0018403807011401c1501d0078248c3c1c540100f03080c050800e03404600781d000000144821195240e00d010090351602c0202101d900756650150120030340340380f020b89100c02050500407c200124400f025041c050302100c090f0900c01d108656002e02d0b04a4180d40e80078004c1d546480341406e031510710101210799100a80146010050111544400c0040c0e400d800100311414001c44808004c0c1100314103c001182d680324500d00c01858000003401eaa1810252400104060b688000c0d0035a0001d0b044031000c69070103e5070000d52182c001a0303101c5042808003054400500c0700f0804850300c02c038000d40705481c150400070300704001503c0301b201c0040e8140c911a415800302b516545010342e414080e00b40000d411040302004442d5500c40168000081e07000141d07210391840c0d00490310f0040040a6400c00424244000907401400501074203028001a04243e00a65010007581c100e0b101110020018510109803064403002c049500606601c83c958a0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 731323714 1250 731322464 731322469
    0x510021806030603010e03040342150f0909020427170d060329071d010302040b0a0806032e020721030c0216121103190f0b06 55
    0x8554128803980403140356005803504201441d00301600c0b03030382c1540d03a0715208400140204010300240d40550f500f16804260601e03080c0280c100020540c14110fa002000d41020380c0740300c0426080c508a400c049616804004110350444040d8030421400344561300014511046901c4000003e000355000d000c80c1c0f81411080c00306200040041d60310300c0c1004421000b0803220200301d03402400e022071140c90031003105080400e980c11500261780001c0000c038041281c0411040081360800f80010011040c5072051707000c0c0c10200b00c6000959000003080b0702c960182e100b617040b10007030310154500340e031544051400203005070b100b29080780c02849403002c01d43d0381c0308003840341d0590322407008a10044201d10012200194108201c200c0c3c0e410702d03140c0f50080304121207500d0441c2d10388a5030005500603640070024540407000807000503400582009000050143c840814603a42107115a088071410b8000b20b0701c0c1c403501003050448003004240c10350402490862480c5118081c220f00841c0e615440c0c00c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 731324964 1250 731323714 731323717
    0x204060e19060b04030803100e010b031801090c051302071401090c120507060c060209090f071e1413050604030804050406050411161502130f080a050d031505040e0604051002 76
    0x601c80380f401c42408100001102e082c0295840900d00e01280380c0c1039514000700e00f81100a80003091811400304c10003098002034554860070310044402030107404c1d407175100c115085a642c0a400d01420301168100b003145101e0b01110349031a4000c005200b101942e0040b240242880714085640c5010300c0c000041548442d0800c41b8034a40010203800e560b0301d040000c1d40c5041e41414116044d03502802021250741e580c0140394410f544108060038913103040b08009100c112880442c29010310201c5001481c0c0303030f001c00700c1210707092950100c030703695159940312250070b0780980e020320340c8040006404400c1090180281c0115001580c051110b10b03110020403069039802805608024402d12a50401d403500302e503414000303805403800314180045a50f42e602a03174810800b04030700d407400420800c0080305d600c81450040c6100380c040c14110b01d079907881985810513141d000040680310114a02201d07000050369006090040c030070080e0158161545888820440b800c1c1c2d80f0740155041e40039034440a00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 731326214 1250 731324964 731324969
    0x103021303140f0703031b1704030308040b06030f030a050f0702030105070c1b06050d0b04060b16020a090b01051917010f170a0201090b0f07020d110306131e0206070204060e1906 78
    0xc441e1444030b981603441000721681c41c80c0c07d444000304000d00032040c823811001000030314000e41d1040154500303810003484d030942c0a041c10b03009900450f18180400310100c180c0741080c01900d0000d03541e0342e01117240225070040c0500130354554642010310045030303040040185003510490006050715a04408030165141c1c920500c0040345040140260f006a00e50101c0d071b01e40401800000c0702c6d600d507030110003180c00c0b241420300c034242c1015819041d407810300864402403d4069061021107030800c0000c0c03141c09040f4007020341c284a121142102d500034440c0703015201603072064500c150b035569500d45020120740714030f031080805144d44040d41c40c00450071007030355501a1196074074079180001110303407903200305092194040140b2440e40169982c4180e0240c6500a1004010b042c2c045410107044c00805007110194000c1c00740c8400006a84108400101c40180410f11051040d800415424807409800035401480d210b030100d480070111010341d0061410500000c034644801a840c0c08852150 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 731327464 1250 731326214 731326217
    0xc120f13030e130f060602120c0c090c12040320060603070e07091205010c0f18090f0608061021170309070803120a0c080402090f060103021303140f070303 68
    0x10200d10100e40075a60b2140308010151a444a0031400b2419104a0f030311448951011a110301d010001198100880d100e032041845403e0301d4101004001d69540c68102c04660244800c103002a510142e44002c1e40c030b6a1140c003080e01c40d40e01e420710700100024400f00030b2004200105c20008240795002903690300c01d80000d40102006820f140d40300c400410018005410010381c0880406c28106c5044200541031040c800451604481540a0a410154400842007150040c0300c0c90351040082030708403c07920190350011751070302140c4810b009440d594002140900c1110306002901c00380c0d41d4044100c84100d001c506036025904000c0400f50503224019181d41c0c1c0c810a0414200b10504c011a080040c5400311120b00ba958441c450568008036440107121036200100446035003180950141d00d10145088000c41c94180c0c0020700e103000180c848000b0020380390005001e0790081d4121450300e4130300144031400b1550780c50151130051614074181e89130702401500d0348901c1c100052036401c0d0382c2d15 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 731328714 1250 731327464 731327491
    0x1f050112030804020424170c0306150d081804050612150a0b180108070e061c11040501080c0109170c1509041109011b0302030306060703030b03060c120f 67
    0x4a4804030381e0110043d0099a2283e17494242194201e54602c5400ca68200c89501000e2513280016428810410043e0b51002c0d41003100503c1883e940450041c0e48950030382d2641c1d072090000d101055030300f42c0414004041c424009038550268440081c203101c2c41008842c240941c0c5e4940051141c2d81d2105401956198000148a1010148040096032003140c00800040100c810390000342030094402c2c4036001100c0c0d101c014403146400b407101201502a48540200f54280b003008602100111a070725031200002d4403088081140e0480d0040d50b10500400034000d9584549166494001c4a50b210b40819108040003070111203d00c5680c1c4000102d40c0a030401e05490400d01025408050352030b0038140342000828002d41e903d125694200070580d0149869605041c0050403041000360405004246070782c043d000030380d0000c00c0f00e50065043d6100c036262119490264058440700c100e0503458025081003007101d24000c0080c0405620075002000f0341d484400a0380d00a290a4035401284c0c01c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 731329964 1250 731328714 731328749
    0x6080d0c0c0909052103090f0d05040b07031e0f020730080d050a06031709030703080f21101d06010e1206070305070e03070f12020a0302060c1f0501 65
    0x96644100900d501030300070b07155903095943c1700c031005d8140e1004046802c1000310501045610402140303182c0303034940008001042001c0c038042e001d03020f28414040c0c80100010024201407281240003283c209460001d03480504070300010302681800220b000052107a8400007400070300300e040246d000541090340b014036401000c440c0240c00900c0c801540c40389400c0084041110702c40c8109842500b250000040c06030451406150700e561183d298120120140445411a42e0205040307088903444100203590342c404d6040f800316801000b0b10301d200c803d0340088425851180f42c052500c5189046110300c55680c464444030707040002400410880b140c02000507400e9400340d000e10143d5403004042e4010031100a40241c0303420002c80e11800081d88610900820540186860f1901c845c1203018002c400c0c181031418900e4420344c4940340840d00c540c000c5d001551030743c41600e0091a0041c2159544109c0d00024559802264039030301100700c003a0001540107212407085505950f42d43e05130310303140341 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 731331214 1250 731329964 731329979
    0xb0d0c27450608070b07050601052d01090b072009190506030c06070f050c010311161a0f150301141302010e0a2706080a0f0302070803040906080d0c0c 66
    0x14807644072101c60356580e02d40440c140c281000102d000b000200280e0740d641000b0b1070490b0600f08107034016405003a135140036901c040050f095071000f041040c0360040e1009510305c012501c0036a42c2d0300044400000003059801d0255410490803040540c00c2a0003a4044480901840190484828ac100c2c0d49071514600300d40c103070790040c030b8110400030200c03020f00e4403203400902158802e01d004c0340c11401d1034100074100801802001030300242420100450242c00884150f04e20552112901c01e101c80c1d4241e00420003181c08524000040645040721840e2080142c4c0c02c00005440501e03180c3c10302400c100d1607140502544520301c01c40d0204000b00d480d44401c4009868a81c41c0407818002540c0c1442080c2c2c8aa1001c0c0000b040051282e052001309040301142e0201c6a1820b0550341c4d080400502c1144400581e007071007641d210454031100b90036070038101c0c01c2c50090740210140e404001070000d0600401e4009500741c40c00031007507401c0b00400650580381e00409440c0104126260f2904000d84c2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 731332464 1250 731331214 731331329
    0x30c02010c050c1e1003050c041502070b0a030b0102060114060f03060121020306042003060d020607151b081608090c03010905030403060509070b0d0c27 67
    0x1e500c580d04940f904010a00001c0d000c01c003194502030b04521684540c200e0b40352883c00c0306041c580c1030400b0801420540c00004a5200b1405040e902c2040552801b170749610070050103008020b1305100c0713522142880350040c06082e0031b0b210745005100c0c0d5000480c2715004000030034155400142402c3c54a0350b6071075103212030b4000070032044c18040f09880038003561140c40f40c500790510901c10010798a01e4130b1005c00046607000800905080c20101e501c424249036039085a4020500701c0710095180c41340d01c0050014812a400140300a02c1301600ea401c50600d82c1281b0544112000385803502d120442c022151752034112080769226040c400342c508018080c03080070f5004013284042c0c0d403403520748202280c01e5600c4614111030541c8005800c20a00c0300900c2040d401c040a107010301074140ca4035001c07506501407122511b1089a440c646852070a00070ba1450030040064210241e00480101d503880420920b403080e08401c0c500991000561101c4c62000b051009420301c0361141c802a400f42c1c412207 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 731333714 1250 731332464 731332487
    0xa030e010e09090106080d020316060b0d2003191a101d100911181309080936040213060b130b0708040509100b0d02070b0112030c0201 59
    0x10320221005008079a1181078001d4428815140045105480c1c00c1030240b4240030704e424501150020302c5210703a40300603a59201c0440750010320110b03a04905c20001040c00440c0d031b00c0200b504a040c0b59400700c51410a000461000d03044098600d10840d103404010380c040c08a00080a4051403261901c400300d0700d0102c2a08801480349040300592508020300401c3c0800c038462155605100405c00f200282e11030180251a62500a01c030100642842811500904150600c0280c0f0015a01c0441d01c44246841070214240750911948545080202d05a808029030302d000e082e081c82c00380d821480c001018641d2204c0341c1001414016240d00892078440003900491b032018a071f040c030401c008054002c03200681350030019142d86204486010b03050055940c0f04101c22841408004040341e80903040d54211a000d448241150b500d003400d42010482f11b82045145440200c6c40c454855001d0f800f030003070984a05403031181c99032601c404001444202c00000c0000e4090580c01c801944100c035a200c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 731334964 1250 731333714 731333717
    0x30702070306050a0b04061a040303050d0908120114010305040203060711150906060102101103011401121104060314131101181814090d11030717091807020a030e01 72
    0x302240c49039940419034200b80c6118480945414008000d46414815039004041d2025488000300a9081c1e2240754011448013800f4440701040043c200e0b41a43c0200302150387c4501c0003541c4504102d05100e00c2030080c082c2050303060214038249241d500911540703005540080007000326540d2400200c0312903280701e514050500402c81c0b560044489074400601581c45072020301000d01e030280009107810386140489024078113281816800345204400c82c0d041d220506109034007907013580b0050b18484403040440401a103040c0040071013004c100090b2055480590b002e018040a00e0312008120300b00b50744031507029000c0b01040000500041b10300d84c8946060403e4501d181c1c40c000865070fa110b079a84408500700b0300c124890b80703d441e2845114030710b240000005d1050300301111201d5580a0004e10b400c01e01c0004218014092410000d4550856214201304140700310f040c00760314103400c40c40610340205d6800c200005189184810343e481520a9402413509040c3c41c0c80032900300c000b02042c00d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 731336214 1250 731334964 731334973
    0x818120c03040b0d02032d0106080c04050909011a01090506030a021303020a15030c2a0302120f0c0d0f02100b131a0f01090501050904050411060403030c060c02031e030702 75
    0x4901000c0c0c0301034041c4a01c65113005803240703000e4a0102d06003080100e100c3d0583c0010034464410f141e0b401015066400d03502c1c000c0e141b5a140003462a8070b00c91600710740d601175450001c1006006054211444100c000000c006400325040700668030052170b030223910740c03009007400003400250442d800307054450710581844003040d0703582e004075030102440c1d01b060707030210462000d140c08190180140b0942d008240b43c0606400c00b141c408441c40c0c4220342a00c14010405c0c11504207140c400c0103603101d40756062041c0c40d51341241d2000301d8691350115545040d82e01411111981c11400f0307400d00c80c400100c1d81c002c0c00310706401d042014001c0c4000c21281e80d00c620900c4484600103003506c2070340b241c42d0a070703a402c4181d20f60704004c12403802c004000b0b01d4100185d050091000e640d201040e0380001d40140d41c00b00e0700b61664a0904550700c5140445508150080f40001c2850380c0042c0f032402d040e0040c40100888007980d1000ca1302d9118403504602510460f824041c140c0c45030740c0056500402920695 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 731337464 1250 731336214 731336219
    0x90c053c0c07090f021e040306111903020913061e050607030807120f111b070609060f020c0301110a090b12060d050c040501030c140913020f1f08070818120c0304 71
    0x40c0903064450021b0b0b400880041006e0041268604c6400c242040785c284060130104032001f1482c1149445c0d900808150700030030b0441880e03c1b481800760146541c1c0805222032132712500340c010381e042d48010420000001a2000907141424801c45601c65055505c200e6503640f1508191442540701c03001d12801c50341d0300c403419500d6843d442683ca10b0704070b0380480d65964510314450055540803076522080c90b008200204022608003001c1000c80700c003070800600740a00c0380c0c804d9080c00012a02c1075059401e0640444408059038010544000240c440c80401e6482d5204140d40f4000c000305440440b9010000c1035242c54851400701000c3d1258045604170b54521000c581a29000e03403040b83c01c0d8000c074100740484446900080c01a01c3e040d030b1503008c20700d003100901c54507003460b0030082e00602007810404042d49a00c000c0300c40c12aa46460305009000b50381c401490140121440307400914001c0c003060f05220352412400807003010000502100b9604034245c41540e004000710b803650f10040000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 731338714 1250 731337464 731337487
    0x91d1f08030a0e010914030a0b060a030f081b0304030302060606070c1805090c060c06010504090203190305120f13140f010c110c04050c04090c053c0c07090f02 70
    0x1852940c1299030343d65041d440403000585460710941158484020b01c181750102c0b43c13000241c40e40d02c0e94202c01c440400b52900c10109002d401a07410140410341d0061000040c080030038000c11507941103911000340034050001058807401103000050040e007085010426601d051006005801d00803400495041d0361100700c03414000901a50201e000c0d150070070009580b20510541c00c1203801075491a1a1404203c405071302c550050080700d11480c0e07100d201c507007952010485450080c40307810040380440200d0601601030341181040b0101364501e00c4c00034039400f51500f28940500005030000c1c00807006503591071175500c0d9604c10804213104811601580403400d024100c91405030303841d29601c88518424003810984040d0042e0f0149040ca03003404070328030540d0101e5045564603d40090081240d035000c8905129005a220070040203628401100c091403000695101890a42c5062a00d00c000801d54500400c115040c094008910402c01c040c0c154122040308280c1800040c82d04982560 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 731339964 1250 731338714 731338717
    0x703030509150c160611120c0a0602040308070c120b070f1101060f09050f010b0a050f0d020a1e09051020060702010207030207080604020a05060703030b0405010305030a091d1f0803 79
    0x300c101213912003841c11102c2103000a2103005005140751100c4405c81c0907551541d2404200103803507a07600b0009050100d28411f100903407138a5407107070003950f40e00d68a0a0442070380c1c0100d103042d500070b41c1505001803151044d03007041d644541d2101c810000c075071b80ca9100395500b00d011070a031401e10004410b030702d41491007031141501804030f580395200d2080c00e00b141c2c8011118002c00040c06000b0240040c02010a80802d4606008640c6465940d55a01c14606000c6004a10441e03141c0350002c500d25030600d4018442a65400801da0b41402c25041400c5c1125444411702c551a0040e960301c0f840b400b401c1c481d03024290310009150030700075800801451a45412422254000107035400701d80d00040690511041d070090410800400b9035041980001d00409040e12030b851042c07070001034507002c041c084e07005410038030b02c0100104507640e03490500c4c90302e0303506c000c0c10000011001d5101007111860028041c0e0380e145094103543e041d9559160220202c2004441c03010380103030f0740740b0010701c0500400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 731341214 1250 731339964 731339977
    0x130605012a02180108100b0312031906060804030e0d0f080d020405031c0f0c170715090c03060e0a080904050c27090f0c03160509030709020306100908070303050915 72
    0x3c410540315850a02c076103040030103403980903085c82e05040c0612129500014080105042c2c000e640c1c2e5281c03100e02006031800e2059108440c0c803801e158000642c15086030300030f84202d00923110b286e0a1031207101002480894441c000b07150b00c013450113680109031084050301c440c1004440040c130341521040001c0c07400c204064400b034402c511100c008a220b80c002c4000c041c8845504081031400c000c3d03591114068107090065a00c840007081c100144003d900181d180c034400d60108100349411814940c02d0301c100e501050303907001c1c00c01064003204240066800e424940140c1030f45c1c10301090710300b00005000003900c04400188203021016a04002c1081e04581e00300d51610b50040404170001e000c00203000904d845910588807082101051390403041300c1e800403032580003288110120400ba5054018024020f0b010b12610750b012a0b0b401f420350041d402810200d80340c5a40300803601c0b0846100c10507004020340e0380c1013003c2c1000042d004502a00d2103040080050007105036002a00c040c680200 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 731342464 1250 731341214 731341249
    0x50108250f08160909151104030606140306070503060d0f081e0d0b04140c070f0b09030406090b090f010c08040504050f06010806011812031101060602030405130605012a02 75
    0xb500b1007141c2264004010013460a200240304424140d120800d084031003414411095403929404203c08015004603005140c0c4400108405500c0c0c0c8a54111044400130642c001e126100100d01030700d00a0050700c4c480c280090160f8440e02c000c0d0745200307504084000c21030fa200003d200c23105210380940800c00320fa60401c2c0090303403908080c81c20305080d14440101d460003607150214040f105070b4080f9805500c021000000341e624501c034a4034088807504610003520b0241144144000341001200600c2120310f142d465400301d9458246840e542d115011045500031718000409101d540104181e28001d4000d00a542c18a59540c000c1816030300111044440035034107100b00039482d03800405076500501c00f8030303008400c00080307a18014200118003520411040c0c180005040500c2224000352000900c0028000349030764140c040d503a9005401401d110301c54070150790403110317514810340c030841d181603541c100d0301d442450a011080c20f40c140750b145240d525090403405a02e5075403000002c01d158 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 731343714 1250 731342464 731342473
    0x1513050106030c140703050301050105090d0605040b09011a1f12180b130f060b0a0302030a15050105060a02210c0109030809010c051602060307020c0d0f0201080a050108250f08 77
    0x80c0801444100342011130103a660050040300e010aa0282c2940e054520a003441c0c0c0da200c45000000740210b100c210014441d6040c41c0130801040b0b2140d4041e4041e91149001740040300101752088180f980c070883c8541c011440d809070201041102d180d4540592560926219980b1102c071110180c60340000b03000ca5501114007041b08115280f002190711081c0e42d000c050f8101095501c0360180c54050401900e415101d2005a0450766000302c4580110741c0142110880f865030303d0284840720140140c0901c0519180002a6608150013141ca40803e80e43c0584402031903010500c10004c1007102c1070414000c28002007803d61424465091624007988402c02e03a0f01e00f9880190035603040b05404010030105112014440d01089040400150b0407038050743c5a80d202d44049181c01c00005805900c403c500f0211000c0c0405801c508018500030b036542c2ca10381d5101202442511400e1040c0c01d0700381c3c401c500c0c0307800c0502c0f03222651601842c100c0d00e070726180c2e0755040043c004081d00d41000300c00b50030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 731344964 1250 731343714 731343731
    0xb0d020334050108130501020405031b0f01020604080a051813020c06060f0609040f0b2d18040b1e1009150e0610050403120f03150806151305010603 65
    0x26203040540000d40040340c01c2403909050000f0420a03001e4034040b601d40b80c08007001c04120742034040d20301401025040320803081c0801c05002280b001c1c04003480c001e200f101c281c0c81c6a5440400c0d02d600c00c5421044203445c29007080411a601d902c03410301a0000c90200095003170540d510f078100150030324240305c0540ca030580c4d1250744c0e040c43c07006040644244001d000000e2075803a00800d03202c414004540014810104640b170001400b5a40e003850b91086041d10302040300d0920601d03600b150300300304001c43e00b0082082c09100c0b40395a0082c00840f40c080d8800020001031001d004a9403000d01560170f40810346040042b100f06503001c0d18481c500c256441d4061100903170307a10401e03400040d01e4610301c0c03500c0d01d4078104c4501d051014100501600c407249030404020b0061045070f00859200e0f041140341007070180c0043c016200d2681400000f800d042000021049460410003030b1109007001c0c1408e03464055126012442d407400c03ea40103050400c0c19517220784140308841c020b009548002c0f41402 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 731346214 1250 731344964 731345023
    0xb01140c0c27130201020c04020d1410030c0b041a031504090803010611031204060b03120f0a12050411041a0316080f06070e04050613180c1d06040b0d0203 68
    0x14180c9401180d03440c420f00250303900181504050380306580050341c42200c040c21070060040980c10301d240700c1000701480100d005403020201180d007d00307200e10020303031120f41c2010180b00381d00c0b6040c47d80c0103100d1154519402d4400960300002ca0003180c42ca40405000410140d61820100303940d1800040010031085800c00c2d800c17520302c1c20000145140407041c0c00070310170f031810140000c1c01042d40c9142d400542e032001c11182071040540e44501c0c1c0c440700100c0013581c4aa110b0360782d030000120f200b442c00c9001d01a6010340c500903a80407440043c020352003014840201050f075141c0c0c5c001c0e07240e0740000d0407a440900002070b010480c0d4140f003200604001c0058500684e04400c40c0060303103c00d041013426a80050b40003410f100454003c1202d485000c0098180f141a03840802503500d0042a810309040250882d0718640c4070b40c03a2511016a00c0355070201110740200115001c1110720000b480c240703442ea01415a981c0c004180746494109900860b1504000712113006221240604411045 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 731347464 1250 731346214 731346289
    0x70c1b030f0b0a05010b0f07060b0d02130f1401031a0a020d090c140d0c2c09030306010e010306080304060e0a150804060f060311060703030906020c0d09090b01140c0c 73
    0x400c03406250314a03151a401a141c03052080700c401520744c2b9503c40100380159180c3e6008101d641c2c00030301403081803031401104001440c50302d03c01c02c4089d141c08501020b4100303260245040366086540640144c0d202c8181e0f4220a030000d10809413540e01f00000548075403d4881c061095000d13000142642d801c1060628410401c0d54111f4072074103405005030000303080401824280e80b000012080d400100f0340d000e50028910045d0f922500114030100440c6540000146100769003d0342c40c280c2e191900001501110841d008a089076001004180109401000c445841c81005444c512510342d5400303a828802101130b81e18400100c85800340401c1c030026005802028034902c01c20000c0358610755605805c1c6483e40c450f540144ac000c112001850301a50050b82c1d03071034101c4025961011119281d50706d030314080207402d002c20031082d00407401e00c1c442c2c85800780f4190181c450740c400c01c3d95202c01e00e04135003106000903903030710800d40048020748941410350010380034960006140003498400c640b42 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 731348714 1250 731347464 731347469
    0x709170111130e010b1602061c091109070e03031b12070c1802090310050c12070807180b0901030914010608030918090a02100c020a0e041a070c1b030f0b0a0501 70
    0x8910040c000c41c40500281b00740220706560460703416591311070900501c05445a0809019015031614000714288284100900900c440403140d00481d0365801074150360389045403c8140d0141d00034881c002503480005080703110340400c0400c0344c450f00092a0346500c01c0c0c0c407800f401c5511400414003040002c202d481c803080c10383c8035041c040d4280404400880d0380c4000d848421290700362103e002c10680c42c4000101c86051540c0a0f0070301141c034118030050040d030026150040050000722007000c14224011006007520044481c0500d080001001103000e07242000054034403034a0b210720b801485d1000d205180c01840c0040145031500344400c200314907500901c00d1002480721a00030001460800b00707606030561380c122400a5000c0d00e000301203502ca082400000d4001040030030101c0c40c600650051841540308620090103400c1c1c0003100d0b00100c43c140c0d009004110100d1000000a5030a0000c00030100d112a2500c0b1301543d035125449801150001070301c03203a900100340984240c8a0042901 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 731349964 1250 731348714 731348729
    0xb01090315060e0c1e1602130e0f12090d141f1802030309090705040f080309040510050d081e04150306050105090109060e0604090c0f030b010201050709170111130e01 73
    0x410b10642d124452004240c001d000d00c0c01030018840100d0f1b58080e000c160780a4000d0415071850820184580003031100780c0100700d56106090a0340c0040c000000c1f40c07154076034044601c90a190b541c006012003c20300c03000072101c0410070f4409030f402c10000c001402a1a100c00c0c0c079007800540d000307580d008075101c024500c0780000440c100c040150700c000045600210b01640c0044150313440c500115454081c07501700880014450701e0001c0c407514004094000010200c03020005500c4112038441e90002c5845115082000301954034041280d410282240003544899140307038560400342c0c00320a0b03000b41c01c1041805091525400c003c4c0e41845580040d0400b801c18510380001280041c00007000e42c400d001c00c0018001d048002074039454141c0d0020406441c090012000f8846d0260070019910f071844000385c5041c1d031580441d0320501500b0f01400403911230b003604034108204241e20700170340f00560700950b4891007140d0606584100a000390b80c0400c10020f00b89041500c4425042c206074007050 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 731351214 1250 731349964 731349967
    0x114010311100f05090a1703121e070c0302030c010609061502150c0c01240513060b0d020a02011d0309280b0c0a060c0e0406090c02060a0b01090315060e0c 68
    0xc1c2240d03003014010fa110f1609040203600c4c4c5101c9000038032240c9103500b202d00140700800ca005907001c0000040c1c98058251500700c0340540da68441640040d40d80b0005908560240c0082281c07140110444690b00f4000d205a9107421042e241450070340381c0c80d50000d513104c0e40d6500d0400010300c42428014050b007103407020b030003440d82c43c04276621003c01c05400028551800030340300060100950000c3d00c2ca43c0080c10000358450b82c5442a031201656200301805500b00307038144d00f1181004d100e601c00b03a5400f5031a090414210b12040c0f0f0003500031181c804250341d620b28040325649000307a00c00c803061102c2e10096a48480c4542803103d20460510b18001401e20082840d10341c2000750000402e45810046058903003040c64003007440d11b01007101c060b05940ca015015141030b81d00014440003510203803403d201090381d5540e541e040b9000c030600e00c40140c000c40c000c10b07008000340d081000ca1030303014580020450384940301c0400a8915961040845680c1c41c0e00704141a1500d442503408000312070500d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 731352464 1250 731351214 731351239
    0xf09050108060f0601030c0e030115060324060c060908183a050102070b090a030f0c0f11041514040e0601031e1a011e150c02041a030114010311 63
    0x200643c08002e0405418543c580041840f00340c4201842c44903403400400900c0100d2041c42000a115000c0c010320001070f0800302090700307442250060300140710000300b21117040391505a003261a22111030088039103a80310721051300400c11490141c1048000566030540c070380c08600400003112036403800e26107401200c24480101045061040e03180040541d0380301da2104481c54003e0082c072030378a00411100740c0c04140711141100266000c88030b4400e803181221b00c81a0302080e81c50054002000300300381602caa04400061240e10981c0c0424000382010a02c0318106100480c20015604840206100c600d00b080a51070039005030500c0304140c002030301584d4113584a00c1d15007924a101d50a46407100841201007011003180b64581c000c41400a100350b50b162043d203050426185003180a03220250404603a442d0b511040301640038181e11603c040030410743c2030001410042591b080c0791940403084005c03a0310203000d0000d404a010358105225815031078078182e004c07081c1d40d01e14020f40001460 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 731353714 1250 731352464 731352481
    0x6090a060b0d021c020c0d0801060201150b1810020a020913020d0b180a0804090e0706080612010207121707030212060112090f060510060e030c04091502040f0905010806 74
    0x2200c8a40b40340380d00160399070840b40ca110070007481400700c520009100260300b03030521a0110f03501807030324110369500c1466681c6500032400d8840d24000400854903040e0100800c80b58503004010300003170b4400c1c200e21545254006100490300700740c600090381001c4422802c502e00041b000307501c4840000c0c0c1102d501c0903900428141001c1c1e440092182d84101d012456020500d4001403c1040440440304841d60f42d03d001841030b049886423502d1942091240c494140c03001c101082510000d07030f5040910390310394040100b0b28a5565501c203855500b00070500201d1f508030705a02d0500541d49680f103040a8207010f800c0042030040c101010035106005203000884000d5442c1d802800034030301400c001c401c049030395005210001000300321044100390202048070f29009144202ca440c0c3d00020855940d501c140c5403a411100c0856058004413080710003841c042e0b00000e840c5002c0c1d444416500c219414400490b8882d420000f01104c0c410010030640042e801014050640700700036010038180b5560 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 731354964 1250 731353714 731353717
    0x50a08060c0901050c01020a120b04230709170606180c0306090c1b0f060a14010302060304061104060203090f0103022b0f02070809120d05070809031c050306090a060b 73
    0x10303061090700002e800d0000e03078468015038540d80c0b0400001c41d80d411100c0c001501548102040141450078980400303000e00d070138843e40400d01d81342e440c43c1d031110048404014404400500e08802e00402013030100f0507210300b98141e01034403006001806075041c840104600c00c421003c603820503420140c01c10440001c0d0509a030307003000085d182c54015840b10b54071131003d07000e80b0030aa550364010f1401c00d1080c180018502246526881c151112529421030003810340f040c0a41c0d6012103403442e0010001030403c4c0006550040c012840011002e00340400106c5a512a51007000142d0010686502d1880d000c60280c840440c2420f0031071078000c0c0b204011258402e008244240715020708034035101d11044be00148a5501a068210f50380c2c085460203500603085640d03a5030141c803008001d90040f0000240540c1c907070445403581030414026564200c544d0780120f2115406004039180b18000c0fa03442d208001300548a601c5007601c1c0d00e403440510041c0710000707041014260a00c041004007903004170 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 731356214 1250 731354964 731354971
    0x41d0a1b18020a0c02060f070b0105060f0a0e030a06050903040e010e190207060912210e03030f100503060106030e0c030d09090209040212040b01051e01050414130e070807050a0806 79
    0x10000b50302d4003405801a20072040458001c1c3d009400005c58103c400d56050050149520070004030ba01640c8460901c0440c0c007c442c05840e0480d42040343c6940c0701d004030f20f4811203041c011304948040045666080030348206503011001c030303030010a082c441c2d070810741da00c47c1c09401d00200303024883c40c111080c040000803c1d200ca52900394000380200074816a500f004030072a4100600100d1000301800061004400da6529000078141100b0354070302680c01e004051500b00441c00031810742c1c66100482c10103002c0030344080208050054001402e4806100301070080000b52800124019500d640500344182110f00b03c1c4a9004500a9000e0300d81140c0d515050f0350710380b200140c40354007100c00b0a00a210f1002717039808607d8800204070410044c0c20005043c0c5000341d803990481100940c09032041030f00d84282c0303804110184030a10801c1c81c896003028100070002c050b00012000701401d00e048482e811000502900840d100b40201d442c1004980000e107826615420103503d004599a00e502015 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 731357464 1250 731356214 731356259
    0x60703050708061c1221020306180c04030c080d030f0b011e031d0d0207080601030f0b060628110a03080f0912131d040b15041d0a1b 58
    0x786a92094100b80249402000c1e8000c40c10400720240000183c007101440241c006c554004900002c050840c90098900071100900940300b10b102d02c014468040d4802010107258840034000040881e10b5100460002d15400001e498003203007200000b8280c400707c80c0305017107140c20124601550799000340d54842e8840c007103d030078071030b0341e00c038913045028103058800b4807646034451960307002d141d0780426200c00018080c4c08542da4950f880f0012038507071400b40309c0030f400c8000c41c07100d20002c42c108201090384000014503513490240000756940380e15200f41c044404804451540c1c0349800d4014100d1003021103c80002c01c1103140760fa50040c807400c8014501e001100132140420129901041001040f2040d125050344950504150070001c0429102d0700c04040a00c041e5050404210740c0060301841d045a6807090031354541141000c0d5a161a5200d1340050b56040500000e003121400e1641240c40030f0003034401989242011a00e050040c5c100c00c0c45010700032020060b14100754440190013004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 731358714 1250 731357464 731357479
    0x2100b0a05040e101406011b1e0807020a090630080a02210304030e040902030a1b170105161d060a090602010515090a0b130c0302070506070305070806 66
    0x160208020305000e40c80103070090f003000c0c030040c508000400c1d5100399880012041180c0c001940c0200b0620409a41081c01f15036800b9600c0000e81f510008801c190703024042c244080102450168900c1c0d072011003d4502d40c0f008102402146080d402403c0103164002003403210b1410000300251401060001080704030401010b400c60f0b00c0d00000144203a50820f1816464001880c80a5100c854092230b22260b0014040080050720344407041c1d90243e40c0603680c050700205044140001840114010307a03251040c0e2441000042e2a0100b100011510141c907036000b0385081042c50700f0a80c0c000703041403aa410a8100703c1e0426081c4030b00721460006182501100030846a29400904c0e100441900300d00700107a950329a6420a02901c01c5603541d900812169407409602440510710410080c0d00c524020b0114184d204030303400a44600c00c004016601010081c250907089400070303c40140405d40108010741401010702800760b0190b41400c044c003a610304804c00900c0000010b22883c0300300301 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 731359964 1250 731358714 731358731
    0x9040503030604021b10091a0403020c060d1506030608101107020d15230606090a261902010e0108090a08030406020f0a02070e0612060109020306040e0d0810090209010210 75
    0x80803948042c568080d1042d207125046c0380110b40050034120b02c040d03805103038961051420b012042c41c400e220340e805a010704213000460301000b030302d6800140490300c52616032680c4000e03040c07100d44038801003c8680700001c0e940e00c0d02c140e042c104038400d103006007103a1401d2003e800780a05041181c88556045030218580c0e845071030041e05404045100a801a00d080032240745e00c034001d6540a01450a82c9010056503111802c00642c0d01c106595240c204080060401429401464654050385400141d19101c01c43c0d0314400d25004042081c580704002018001095580100314011412020b203000c1030320307181c9803001e1551901084002040600004005010300082e0760541b210f600c0c440b03c40c1da07641c041d4410000d54801c2e02e4003c20801016000102c1c029241c0b000145c800503500e10f010303082d1070707203403008180080d0402000e4507000380d210000f0185140c03040c001e0210301c052030744454800c1d08005007202c2c0c8200d22608501e118910401001240343e80008500382c0b903040e90f070b50100d114070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 731361214 1250 731359964 731359987
    0x16050d06020d020f07110a1502030a03090c080a05061b040b0406050d06030f060e060702160302010c1a012403060609090c1707031a06040501092615150904050303060402 74
    0x1098100404003200003080001c200041c505d0707000400b50007100ca00d1f03101501d9039034095420480207540805603004000c141103543c02034000a42e680d0003601d0015085039a60303900342c200120b280c4200c0e1a07401005c01c000c0c0410800c00f0038002c4a00300e407040c500741428488442c1161180e0b000d6441480004a6007030341c08003040c1c1000e8007840e44280c200c00b404411b4603000c0080d16a005040ca480d0040100190310b281c4000358102c0001003000503a01c00303a01e15001950039014201c0d003940c6800f001035900594146400b005030003043c4400048010102040d07000d4040e40800110344101810703c0400c014180d4070075241025600c3d00e080025114000d0001a40d410012003002e40f182c0c50600704126042c1c1d0107501091020081450301b8595601d0310040110301c4c4564018a400f0400003e410b00159100480b03002444000d401840e00203000306d8241403030203405042100a00700d1031001c21103010502d41d00042c4500d0140d417203d01900309279035141c2e160f000c02003105000b42d5002c90780c07000a8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 731362464 1250 731361214 731361217
    0x1c0501232101060605120f04200301110f0307091202100f03020d110405030c06120f09030706060807170d0e28030803060f0909030f07060f0e060916050d06020d02 71
    0x12540800204103065844e10050004d40118002100301c0700340000003030855a6008200d07210fa64414003041581c221591a11001802c07018869015940c07a038101d10025401402812014188171003103449160002c00203000007000d070001202c0d04201c0c211280140c035000000c10700015141851010448141c600724000e000b02006100c00505210308105481d4901c0c00510640d4800da09880362a0362900601c00341e4403030001000304c44103181e4001011100b91900c80c80c2c0180c4403006507441d021441d01d8440545e200c98101482d10b40000c0700400034500c100781d002c024124ac40e40038006a01c010302001d0000030119110784c1c0140700000351813003260603000d0200d18501360508080c40042e1070742480e507a0fa400460300c40d8040d010f16407180c07049180c805440b40c80b0f01c0450300150320309001c0700c1d80b40019422074401100c0154a0ba042034411601b1030003540340f0301c244003004045c140340944010740790005c042c42c2165951840b41092041e900c0e03005500c2c5c160742c0c000502582e101903400b4840003d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 731363714 1250 731362464 731362519
    0x604051b03180d09120f0201030204170114060108061e010e040608071a040803030103060903030f050f09011103060f010e030f0115090c0203040506040e04020a0302061c050123 77
    0x24100000b04003050398490707610007140441c80d0480f00d00c0c0481400559001c1c1c16130081201450121031400c2c0007135122803a00002e14810714002d401c160355581d002451510407940d2901503519001c0c9000741c11001002c141d070004091074088280d0501360302042184035942c250841807a84401032020b00c0c0d002e05601030303c02c10094004c1004942e01ca074850b07203030320700c0d070040110221012030b250000318030402c169001c0c2c0341c200000d50710b9a4a19603800c4020448408100e080c1611904180d102024a104a40c820001d0205024a510b4030a054500b161380e602c0350a5101d9000707206001994440000f00c441c1842c00303080030b03100c510010000924181c0d80311a0005190300f0b000b540907040d081034000340c017261003088080c044c030001c4940c140d0b03ca01035800b80e19006007051004001458254500a401500150040b0110b039166000b10380c103a481120700c0d1102d80008017030840d52070041d1040b44d005143c41c1c01a0311031180d020081034040041c03c2400c0388601e162690060091607140c0c810000d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 731364964 1250 731363714 731363761
    0x501050d05270a030924051c021209150c0d0e10020a031b050301080d08061903030207050118050a12290703111201030221011e2003060405 61
    0x4001d203500720999a0303030000f00f6080f8001144060f00040004042d6140c03070241d40c40702c2800011a031940300444140d0028803043c4500542072028001c0c0703222520003442940c00051f28541c40703207400456945410710700302004205904140c20032809518540c1990685d5240d11800b250a055040081d840c0212031200401140d1000512404640e01a40000e0101c0c1c030511400c07404000c0300c10150351501092103141c00036003000d00101c894074070400d503136a889030004124120324220b0096041d10485650812005a0301108040c005580c1001c0e02c03003100c0e131041a07a170861908000c046841d0b00d81d18821015043c060702020401c01446170507061380d0440d05661814a02101c0c0301603e80500140ca0140200e46000d07502c550090709034040710542507401d00151256445c560912029110302d02040650b50503003444203a0082007030081e82c1c0322034111001c4003035079104c04071590200c4460309000700bc405100242c1c81e82e4084450142c90380141c1c00c0b900004c803540c0300100000d00c2480700c01c0413030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 731366214 1250 731364964 731365021
    0xf052a0d1203150e091e07050d0c0b0703030b01031b0903080304171206040b0f0108060f130f02040311060a0c110a0f17100606122c15100501050d05 65
    0x265034204805405d2241d4011300c200d410300350102034065070320800c42035910120340001600740142e00344031503c40c51a80c8141c0c03209103040c0d41c3d00110940303508204c108400181d00d0780707454001d969141c01010410000a00401c1e554913000ca0040c1a00300c00b480001c1c40c0c000040000b17804d00254076000c841d246545a0803544c0c03000303008101501f8003001c540c600d1043c1c2c500b1118500b503051402da0040d881c80123031070b4010b29440325020000650340c007040541d4000c10380071501c544c0c4d011a00826116150500000d46c441e41585088083c0082590180c1d001da4800e109424509510000b142c00840c0c001c030b4941a155404000709401e213007aa002019081e0001000150351001c00805010508003030050f81c10301d100130584202620005d2289400081140d0800010a11141e000342221000f1144403105c1246800342d407007035940303002541c07000c941028080f40241c14010303e00c10340c0540c07001c020000369800d010010f000b074050b80c41071007005a0b41c0c00025985141010000c50310704248030340e08 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 731367464 1250 731366214 731366219
    0x72a020a0806011a031b0315100c0213020f0a0804030315260a020a060e030a1e03020706030e06070c03030b130506031501030b0c03060d0f052a0d120315 67
    0x4a41d00c0c0b4081c410003c500c1880b03000d140b19020b080303007664081c090b044400500c58810b401340c084103402c05000707a4082c142c520035076085e40e0b9074485154005115512280420003450040003286d4090f418000c281c180100402d60070540180b0407680c4903242b80c103283c078043e240ca041c1100205a460302c004030034000c2da580030681c910703203054506043d80082d0404462602040c070ba0b64940029401c0203420524980d01407028900810380103075030307140c042d044840030006501e4111708614030385940a19249414070410a06a040c81070402510281c2024800b00740e00c026015907418004041c5c20802c81c001000501709482a04050701a030070040040c40340c4446000a20000e11013030794400d10a10a580710240c034030a1580d100e82c1241d0300000301801c2692801e030700f11299800182603551080703802e81c40000042441c500f0344030076030044000b022541e510422001a4079400c0a850250784602c490490641d5910b020820426030301c000c0390a5a101c2c4000141e0140c207000f01804407651601001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 731368714 1250 731367464 731367479
    0x2071110200c0907170c090f130f05061009060e0d060e010b10180308071106030408120604060302210c0a06110132060d020d050a0b0f072a020a 63
    0x10340c101500702c43d51221a10342c54010b880d00c4100c072a01c0c0503141030040c0014140401000648944900540300f9294003941030000f0384038000d0401d1800c041a611003400c402003200c2d00c079070b940c80041070b40c140500b840d10b02c2001e4a02c551901c103082c06c128407000849840d40b1640c050084040c2c0c070800600028860300802070280c140c410809001d810803035080e90210380301c2ca402d00c420901c00c8881c503944a040d902d580140b544012016108072000307041042180d1a0240258400c0d8010080036884260702802c001d002c0f10058140d41c8240d081000600240e691000095034650b104081090b1029005c00c1241c1041c43d07010569030300003800c407400925150005124030040a003d0001c000210481c94144030910fa4207400611041844d030003080c03070300c0c40821020b80088009103c40100c0d51154001003004d8030a540c00c88040e01702030f04050030440f01242054011000c0186100a4a0460001007400c042c0680070040d003c044a411112403980c030010202c0c21350043e11009006032074904 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 731369964 1250 731368714 731368723
    0x30a0c02060c0307140306060705060f0703060b13060c0c08070f030510021326061008160311010302210a0203071e0f080a0f0f0e0d02010207111020 65
    0x4000054011100002e066800801c12240718503102d0300c5d48101104045150000e50b0001044903800203810418400824010007406200e00100c4101c04010700e0088002003da9841d94081c8841010511152012544201c201e07820f0f11103518056000340079038100020208035551040149005e100d1001c10400718000d0040256030180302210600a18200800101d1003014001c039240080d0301001e00c58030a40c04130035120180c00a2076898002d1052804c0790403d00e050396181c01c80b40d003a9a0402000030306111884a0300c520644041c1210304d951a15601d10344001c0c517003410140d002426000b500d03410000b880c804c01107091514400e207080781f40f000095000380c03003881c0400c0c03070030305003120711154041034000300361040c2d071116541c0342100c0f406d0343c0c2d1402c05002100d4242e1645039808030743c03c1070302c03801d032074141140700203d07005152600440c00c00c00212850030443e4010085600490660380c01d42110721003e8559901c1e881038128210f42da09415118010092800300704819410320008 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 731371214 1250 731369964 731369981
    0xa081e0106120c0809060f04080d060605190f12110c03160203010605030d1407150218040b010e0a050d0c08030c071d0601120c111e10021e0307020c06030a 68
    0x70003045803080f0240241c925440456042d5202d6010a0015010f44550700440350030a01c40c0341d0f4035080000018059080da8050f40000c0001000030030040380080c204c00d52a25540da8506016003d482d043d540106450b02610040c0e03401030b1035803201c0390302440900c1111100c880318410303a516442c50b02200384005540f403809074481e60034003502040611340824070b004000d02c0c5d602d9544140b17549061560242c3c0049a090b0f0707a800200010810081c0a4002003403400304206aa0f80c54211314003c000c2107400c441002070401559101d03203029074440e00c82d1304040d10012103012036070300c0f42450004628000e542090202d8003000c6000c1e68522000034881c07060701d0070340c01e00000349441481e020610002c110b030881d00207044c2e1282c0803030310011540312902440d19450058044030403120719038035010100c03007001174420b4a0070003040e03409400e0041c40e00a07011440203510b030605003200300038211110036030450084000408241414001c10440b15a00809082544c1b030b858144001d000034050134 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 731372464 1250 731371214 731371247
    0xb040303030f0e0f0a060b06071202030d0c03060f030314040b071a0703022809080d170f06060a08090102090a17060601030c1b080c010504080c0708120a081e0106 71
    0x841040e059001324002102c0581d0a0040405040da51250b40c080d040c0c2030030440e0020010401040030440000b0701102c040156002559070b5100003d040040351400c4118804141c5494814840505e00c03042e014222070305480d00e10402d02442c00c0c074840d40d21990b480321181c51800540c41c0c0030055a0f250a0200740808014111a503950328029016489219a00c0c60354070060480380d8181c0c80f5551400022131101d180070108581c03a2603589150443d003103125004642e01c0a18649800340040403651310009580700d0f818982040740118440b80a288242d1007802581c00c0003542a050960503500d040c10000c01940c1150b94070b13006002c0030340d00d0070300c0031285003d42000524254000c1c020744800301c1c042d40d95001d1102004c2c03e0208000c0d04400c044039448405c0100346102c1e00c0074040d06003d170780190300c031a654510240009141c0030942e842806213800084010b000759540c142500c0510b08141440e60240d40c5000340c44801e14038410b21007050b44001000801d81aa00486c00d441c021f044 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 731373714 1250 731372464 731372471
    0x19020604020102100204030f230109030e040c030e0604032003031603290f03030909100e07180b03060616050f01051515070614010603090209100b030a0b06040b040303030f 75
    0x504d0b03039560503485079020151200392100100b84c0010030511050403031820b018564801c02207104241d030301f0358a00c6c02c0d0940003d107203840c104001d0b207014450480c4003611406c04201030b055041d4441e480d41c41c0100040c040c000c5c1e0282076003806c1d0031039a10781003443c0c000c01a42d40d0381c5801c0040c00180c00ca85001d90002900d025605140c0b240f80d05002480d04580c8515204c4c40c880f018100152207446100c11a05400705001c1d5089030303240e200159002e10b900b11041c002003810948101d00c540c00043c94038040040b02c5a5040150903074074910f0341500e0010f10550369a548281c040340740c0348134040e00f5008440c000301c0010144600410307002802d24003080203018903125181360503800b182c2415500d42c0b024401c2003680c0005500d1008255480c803d00300071441460f5841c6100b10918240e100304086515200843d0031840d0581c1195444240b101c104030450342080b01041c07a5000040580801c252303115594009561280d00b910002c00301700301042e503104d44a1034000c000e414941d0a01c0f600c00c1c103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 731374964 1250 731373714 731373733
    0x13150f0f0b030f13021207030b0603011b17040c15020a1109093f030703060b070f0f020121060e01050a080a030c030c0c0e0717070912020619020604020102 68
    0xc0240032240203c1000c5406405501c40c5010007446940c40c110481e0f20200c1e001491140705020b0007000f0007580100107446803481c0079420715083d0345036044144080301c503210140702810381140007041840110700b1006115038a81c030b441207000500f074005a4050002c3c1248003802a80042c1d2071000794820042075502d0061071041c041046000e484881d03854202550240d1550f1101040d140b111115540c0c00cd1081141d00c440c3e03000c44540c10001300d40200010400c81c0c81a09801004001c200f14000d40740340115680310704030708000187c0c0080c824016420700801303584c880d44800270000900303440c0280b40b1042c3e1802c0e4006200c24414074420110364400000c1c5071030180c01c0403080301e001c00c000c0c01c2c6500c103564041b201812031031300031020700c902e084d0180040740306820b80c1d02c050629280b001c101c41c20603440180c551441c03d0351099040c140c0e40108416103034094030711412269658240e0352801000d10014820780103190001180419100c07a4682c07403540001c20900a40c002e8017690700d403d2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 731376214 1250 731374964 731374979
    0xc170309090f04110a06080601110316050a050d080f2d0c0c0c010206040812060d1205040f05061318020d090c030b01080607020705090717090a060f0c09030213150f0f 73
    0xd4a01c0750a0205081f140000c1c0d095000c0c0b080e06519400ba107090b43e2400040c0b440742c4a030035920364400d4446503c030708011030401074100051000c1d40c4150524400915085143c1c034013002004080c0800400e80c004450300c54001d40c0060b064019610383c1500f014980901011f4041d00705220284040c03040c000f50400ca07500115105004035004a030803494107000b038012003004903020f4411608040654643d0005c582e40b4036080d00f00b92420b55030142c2d240e103008109103489000e9003200340315032010000c100d895007041220ba002c98840801103881d29000160580003406207140e440d0340d0f01d092550b44410007601003046001d59205503004241d030b0341ca61043c90741d00d903400c4901d0300c05648942c3c41400181791219074268403a0491400140c00c11241e00c620340c4070841582c202d4115031002c0c10030300800160303004601c1d400682e51004c00c0541903a50000b02002e0780c5110190140091516846040d01642c00c20321040400e04c07412001c15582c0c003000802041c1500c0748041d41e900d100710109a80 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 731377464 1250 731376214 731376229
    0x9020a08270615122e0e2e09050304050306090d0518220b2e0309110405010e01140102071a03100f06090302030114040c170309090f0411 60
    0x240c000c80010146640c484281d201d05189000505920020380075100c8440d07501008104004030b520402c600c0905c00001100d00e40e060500c038043c000c2810000030348042c1d44000344a880340b080601d402071300c5000030344055920f41c8064104071310040c2804015401e20000100500464406504031001d46d51042c04044c0c84a06820060002031000c000301c08202d219058003860a010042802d80342082c5242236600c2c095000d00c0300c0110300d403211010380e5035180650190080c2c80208844c01d51132044000b002090f1181c08030f00c401410343d9011040144402464464016400504108082d5860702c60800c070741002481402612032516440c0d0190b944040350380c20407903500146145440d202088801c540343c00c000c0c804074a41542100c0003d9032a850142ca50083c80d8540700c0030840c504500605094880c030300b1b41c48614002c2c0400380f00c0091003c14600301207411b80084030b0150708490036594150312074296215031041d502000d0014000c214400503004600c5486420201154034003070041e00c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 731378714 1250 731377464 731377531
    0x311090105060f1c0f050a0515030706050a18060c0506010f030f0f020f030703230a051207080c01051e0f07021507051b250f0308070303020409020a08 66
    0xd09100f002e004803031480142861a1580340d80000b01c0c000b0140c41d1085607184450b401e4100d468a007884025021840faaa41044c0d141580c4014100d041010980e00c000078851542080780002d15007102c0c03071082092059561030700129419181d5900300051580034001c1b000e81c0c03940140c00c00010741101c000c00d03020469900802c482031503803c0381c90f12100c00e0308001040c1d0700700c040c00100003016035082c030204000c2d41c42607031041003c09132401c18003180b00c00104c56004a51000201c0000f00d04005423820840e00002540c07a03481f20680b4064181d40100c440e99a080d60820b000d0120114405941030002d0141500144207a40c1e080d02b02124485c00755203040168024040c0e001c0c103841c06c8180a584a400d074100310b0710b45030107140101001784030003030949450b030040301c00c4c1040854886d00184034601c00c2d280152007503051652088100a162100602040001455008050090701520300508445108644501540078003502604045038200b40ba131304e018403d40194200350340704401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 731379964 1250 731378714 731378719
    0x3140606370905010303081f03060906230403030e1231030b0a0b0103020a0e090411130b03010b010302040503280803010602060603010c090f0512071517011d06060d1b03060311090105 80
    0x502034910348420000704a40300e026a65245c44dc4442103824000d13a11012400d0301002c0804094074040c1002011140000314914064200b041441c5480401b9003c1e10314002c525031061185000c00402a0f00d003018050280b10303485d40c4c0f010004140204101074032311490b002d5205002c1803a0344c100440481c41550100404900b8240480e0400d041c00716002e82c0c043d1203107000a98500c44035000804031080c4a4590381400c2e142c00b03c0c40034508080c040c03155048020b08065007042c0c10440003036181c0b0038a040700c0d0403140c054501c040307581d507c52404100040c4c01c555a030355071356102e40c00251a80022a0524080d41c20801d04014040c403908401049030340703001e9000c1c50103041604025280403089148080c0f03100300080401c40c0307100381025034200491038540d2a00f08a00c8002000c000c10142e000c900c0c80100342d1160f403049076002000c039520100c101d40381e07035513070300400243c400400340e445812058500741703c9403010403501980050305407402440c4c800e410204090800120404c03d00402c0e4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 731381214 1250 731379964 731380021
    0x50105040b0a0207050a08010204290a08090a06090605041208040b07030f020f03430503090102070506090708011a060429070303060314060637090501030308 69
    0x408019030000c0d000d60b6941d40705903404155903100054034411746402c1110130783d5002074100b0611500d0612a05940381d061030301e149401560150000f14080c9084076424880020009001502d003800303490083c0758807071820400d00d40c0c607080801c020601103400700d82000c025242801c1d1140100209803050ba482003d045413580c500a0840c081e00c607088070200195006c0c007084a138044480e010f14410042011010f40380c05000c0c80c82260803400b1000c402000000090104d40c0c22031b07036a00040d1912840c00c000e40c0d00c1d10b0706100c1c28028442d090000c1c1c0240154424030088060104030481243c11100080c8080051103000c4910f6002c0345440641c4000c04000400403c003620306804070030710709420480c044000490030314440e83e02540c41140000d42c1c1b54014010450880c0d43c00314000b14038030007403180d46000000700c0d01400c056108002d000306c0300e80004001c40348016503802c1180a2482d05001e0342c0c0d86d4444800500340a00040b00414503040000e0010f2050013940da208124000006 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 731382464 1250 731381214 731381219
    0xf12010501031a0411040815100501090812130312032c0604020f270402100c031b1502070b060f03121611062b021e0d060e04050a0c0f05010504 63
    0x900c005d4480c02031440c1d013130200082c81d540034420016080c800c6002080d41e032810200ca10401d990300c4e00010305008041505000c25440003a81c00d1148003964802da0350f0f2200e8100d1307a4038401d0740c1d600c001c20340e030b5054407003400b10382e4180c02056240c0d1500c4141801a440d80364680110940104071800720350160001a0140c9400660300502c000e014141301c4c01325040f030900740340c1211a2801d0a030f1311510340042c0b10441c1031800c070031420300aaa26040c48000c401c0d13030b030003000e04807441c02011500040032480018040040d454441428540500710742d07848036490961419201280c04601c6000f03a000e400307802d800c01080010015400043c420301e040001c2001c0c185940710f030042903d4a48e03640111f03e08a841c2d00d0b00400b00c01810718142240690b025811075442d0003040c219805140c0180480d111241142e005025405956591140c0755081c551403a0010070499100c10b2001241809010a1200205034151200c3c000c80141e4422904e403103000c800c250807441150700159040004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 731383714 1250 731382464 731382469
    0x1602041508100f0b0a0e040317070e060703020c030607030f0509010209180901020c0109210201060807060e01180b0403050d050c0615041b1227080913020f12010501031a 74
    0x50700e1100d198000010130300c0e50003002c40c1038000140c200c0c42940440350180010301d03410040e082509000c0c2e0050040c1c81c0b0b888030005051484a1442c1c600464000c24007408041c000c0c00181d03006200501112002d00e403000300140071f819030140c0c1c4041c0a00e0800400c02100c0180212442940060400c001e1500000035821107550003c08002c025513090000c884030141c03e0003800406406030584282a26286c1d840700303d03c2400c08000b200790b80c5400010000c1c0c0c0c0340402ea100c01ca07000340c280035468002200041e141550811040140005000c101088610600c070281054a00400842e540c0d80000344042c2c40b10b12520240f2040e035401760002038807200c408090003601010181000c9078400c1555010310310b059480d022100460b031507603142000f0300100d1098000025140b5084040a02030441b9582129010400039110440005c1d00c11100e07180d54003103076484d5480160842d56651000b00b03611040d00a0f14810303c90301038076030000502c0c1d803081c0035049280c0030740d607031142da007400700b004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 731384964 1250 731383714 731383721
    0xc0415031a36040312050f04030f090902040b03090d0c0c03020d020f0616050d02010902090612030f072406061b0c1206050a05010608130303020c12160204150810 71
    0x50724802c507156810031560700e0907900d09501d80c1c1218551596007038101481c01402e1040c5910841130740b68902010000140c0791a000703a030300150541004894002c0100088034442e007681c115819490001a000034a070352000000d43c841e030164025030b1440c40400348221010650520094204400d54605101524001e480c40407803a2000f440805109110000b140c4560002016441521a0030307034880240001800300c0446440c1520013003080c010382c2d038009105680050107041c00742c030420300413104200080044803504100404120b4840c01c0360724200d441d500b981e0340180d1198803aa203000361a20810302842c815220691114944010140c1240c0a03010749160300b13442e40741400c000090400042004402041d01408000c507403460079100c4082511010b0303104000b04901c2408000d00d150700c00c6145200d5540c107180240c2c0c2c3d07843c0401d0240c030303080b2038940e40d15820400080e000c1010141400115280d84240c03024030800c41c025140b4036070f00b003952240d80c0b015000714008101400403981b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 731386214 1250 731384964 731384989
    0x1c0e090105061e0a053609090a030305040204020c060f040c0b0a080705070507030b0a0b03010516020607110c10050c010e01090206041a0d02031609090207030219030203070b0c0415031a 81
    0x9081c4d400c207211040b50310302c06c00c004001707620b0b805211580c02010f0030361000e8040d5210000d4130082941c0c2454403980e40c1c2c81402517805400c0590f82c0740805d046541d0780d0101c0e80080c8064049034101c0c2018201048418000d0320102c50702000c213030000503000244010383c1e00b0101c16445640e0709a4a20000b5546640444811645400342a40c0840011210b0201354000c2c2c08544d400500752032420141401c440010340780c00042c0e0401480721300010360002e00540d000700d407803078108038200c1e808084502c1c240520103c03036400200c55018891259000000e80b40014100c0700a20615039900100341c2241d0721070701d01030340103541007009205040000745036090794801d01c4075040c60b14101a903114100e0700243c0d045065003084d007071b25a94095201d00d2703441c05021070300030461a002566902a42e507540c041e68104440e101108504107150007402a1254a40c00000409a51070014001701d003a0b03102e401400e070300701c00c030540d8411014800e1058401c20f02d094140101c96003005000c1190821048 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 731387464 1250 731386214 731386217
    0x2c03061806040312020c06150a080316060e0712060f050f090601060503090f07080a06060807060512040312090f1205040f0b030907180504030f08090604030309051c0e090105061e0a 79
    0xc114161000c40e00b0010207208503000c0c02d0007c040c0448c2070411480c40c2040e80300e0074041d0b00c20320a40401d4070035a4a400b5225600030400910401903000203824030109610250f0388118441030300084c065541c0080640f00c3d1400d03420801c640d101403281a00e4003090b0364100645d4082c400600810f8050b40045400c00c0c1900202c030b0024010040722442d100560b00a500d440e00001d4890081180e24064000900b406c14080c006c41c03824900010024050301a00316419030620012409040c003403c8001440364055100b8885000303a4105081c0c000c50b0904102c42014800d0303540740815128200b900c0c241d400c03401a0400c8070740f074210109007940000c1d02d280004e004545000410707802806050803884c1010101140926041c1070151000c5c094050207810702c0040c108201c580500407a40d59441645820006048040ca0034030324941200722003100200444141100c1015800501c0b960410000700ca0141c0c5503a26401444428000c01c582d1072200425040076880c46140c8102401104405 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 731388714 1250 731387464 731387467
    0x109110915090414250b1e090409060f14060103050105010f200d0f110a02060a181a0d0e0a0218091f0b1e10050a2c0306180604031202 59
    0x40d5184c030b9092080b0a40b18a6140420074180010756040e080100c00501035101d8403400c2030105010f001c0c40c0c103110340e01d0642001002030101125520303980301c01511900144100090400b0305a800018104030b0400d02e800c1c6540000101c1642c03181c01b40c80e050712070617510a00c800c10b0350502a9841d5817000c55140b0b40000c1646400c96080c4100004d40416016135661420428a48400781c0f81d91208400ca440c5904040d00701400750301e1301801c886451555107005010481c0c03107021141511f46903000450414102115488281a03000c060704920f64070b10b5040040201c031081c001e43e43c0103c040300a4100c078803c5002c4042000c0140030540c0108000191039107107007850342c0407079140c00320701a80380801c2c1e40708107031541c5040910306441d440404100181c0006114000130300f81c0c0000c005060208100041c0000345540b15414407a45000d003511401d40b645000c1305014504490104c03910b000c0d00c6100001801244526180882000100d0141c0740c15102d40e20211807002c0003a100c002080d40 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 731389964 1250 731388714 731388743
    0x10606091a190302030718030503040e1e090102130504050118090201110a0309030c320d060213530a0605060a0815010b0d0b030f01091109150904 64
    0x80350b0303404101800710b039940181e40f4036184501800500e11442c1031b511787c0180513000d10000b00000704403170a6a089a40b0000b841d40c0322545480303c60307040013903118181c1c5400188101150150060711004181c1000143c00300d480b003007444211102445081c0c90030000b907405942c101d1541c0e01c402c04550061405040c09001a20307181e00d8079041c1e420842c00200d0400042061020814100e0041c1401c0140b80c905685442c10000483c1210380301001015400c80c40d92025075541e00202a0099000034255100d40c045140108044482d12031085107400301441380f11107041e8580d07000d00039160050701994000c4800307080310412042d82400c0001c9201d4507002001100c003000b04d5488244550004200d0b031814105009044000f6030291000354030401c250700310700034054802410344940c01c40082d00c81c40061000d42c082c2000b118465018000e58880c00510641034010319207680c012011040000b04500030702000e4070003101d288442d0080007a05480038506111482d8100f40a504c007981d03c0e00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 731391214 1250 731389964 731389987
    0x30908010c030209030a14070b070b010e06010507020d150b150c070f0b0703030c140712110d021009020d1410050c0a050315010903120e030f1b090414070e01050111010606091a 77
    0x142b100006640c2a0066401004080e4007422202d80c050b00a280803800d001e1580c0c04220f0000c0503510081461034803481d0310591115507441f01209010050102541c2e80d40810f101010758044010a045405148004122851108000c0d4221781100311010703d0308a654038120010f00520401008009880041d5a07211040001408a8034091201811190981c510181409512030060b0394142c0000c92100c0505801280110000e610402c01060f0800580700042410000c5940200040000c10f00c2110110002400e4450002044810002c036200d020448000703000d5001d2040024108000246904000401003104610181041080592aa81c90070700d1004c41e0355400340014000e01ca04801d5160400c42c84421800000181c581020707501e08001c4022070000c00180580388100110701001200600c02c108190074405980506445005960340840203115050009800842c240c55503d41071180c8021a002a1203800c920743c40e1071080d5060f40d00e036208d0302e050164203000c00440b02 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 731392464 1250 731391214 731391217
    0x10e042711030706030e2a2b0503031b0306220b0a181404080d0b010210020a080f0108062a0403060e0c190803030112060216030908010c030209030a14070b 68
    0xc0c500d81c1c45c042014401c00c0e00141c80c00300880300345d00d00a0194150b00300c007840010242559010103440005a807065840310240102207441c0d1503040c1207034104008107004010010394090100b100d20a880e416144069041c2e80c007007130b1400e42d40304480b11031501030000e035889807030449000641c2c0820042001000a2462100c42e031150244900307040c090341d00c1c0022480f415082041c0e10031284a40c2c20151030740c4019018190718100e50a9a94038913030451381c001c00c260040b03220354680035561180c60340760083c11608262141d80d06003c0c2c400002c51b07600c1021540303d2203410000f4641041c3c1514030105a581c084503101ca0300991010040070000c80c0c014010040b0b03038003041c4010408881e2010601c94007190500034004504c0b040081800701030408811603045032004510400c0302d1900b0300700b640003403080141c9084000f400511b040e08042d0003104030402c8070500c4000300820804900250164404c455890742d264114044400000c2c00c40e0401950b01408001120791068641e040079409 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 731393714 1250 731392464 731392469
    0x70b1c09030c140f01110c101a0607050106051f02060f07051e0310090b01050a12060b0301031a0601050901091a37050403030f080910020301090902010e0427110307 72
    0x198000c2429403904c060240254a252401d06128034588001419590340300e000200c1d0500c4d0294135041c0000c0b041140004150744541c00030711030ba41d9aa07503840d1160090513107200306405404440c00c005031500103500d0b0007a890032150060211503884001510f02d03844000c0c0200c080c09414004643c1038800300c90f21f55048591031038059501d0804002502c10390609070b229070451410a441d4200c41c0c2d078000103075076007031825007031040c9100c45031040c00025054580100920b4000030000006106c03800d42c0d001070b4241e15170303907a05403134440400454061050340b29942c0480c060b030808000202c8001d440c0c00b000100342a000c0d09118189112040fa170b840400510003200358131080851195150704400814009418030602d0140340d03948c05401104c07040c508905100faa00e0008005540900c2003c5680c00b070b44004545c3d9603180e410308401803a0003d0181c1c0014041d80d903c4185003007500c1462611342900d9240b0019004180b03410081c1e5403902e8040790710540740c3c0030080c49500c041000c10301 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 731394964 1250 731393714 731393753
    0x33030109060f0207050610081c091508070e0420210a0912051c020918070f0e030a0b040209090a05010c120e011811030307150905070b1c09030c 63
    0x90381e4104d400c14a28014020300200030242400c0701c100002d110002c0c40c035010704074000c402070340510b41c0d200c203443c451a036074001e0040c01d4803680341c1701240b507000c600715219146a454500c5460090303814401101c06022030000140c2070300c80e82548018440002d0a20ba07151209052219500b458142c40300c80380c03d41c1d10210050310340c0b00300000c02007084608030603903103a441c00c64100900c042c1c0d040705001026100e158480d500182c0004a9110340c0b08482c50b100c50000da250b4241002c010092200f1802e6081000081d000801280b091902050301d6400e00d0700090202071a486603020880808009071180d5014451180f40f1400a10300b03001d1074441045c0741e114911000801c40f405021740340b180c007140a090349080e400d0340d5072582041035080c40d41d4202050501d146809000700c6c2c50351240b483c02915600050808855848040c0c20000403140b20b1002c3c1c442850ba5007080210703c0c0100d0a01c8019410001100300b1000300540c001d030a060b00a18140c10700070040d88541503400c44007a5040c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 731396214 1250 731394964 731394967
    0x220f020c010c030608030a050403062003040b070f020703021807030b0a0609090506120a1b0b1204060b0108040506011403011d060a06051203090103360b33030109060f02 74
    0x3002070f5014810f0400402100e4091490080d400300018850301c104d00004050541c5d03220040702c01030402e00c03c1540c8400640e0140d6403030605040480202030102c0300c100c0011038400c4c3c02d42ca900d00c041303898000c03070750b0142030a24182d030380c00000c11045000801c1030040640d12049171410f0303550300c50600002c001c0c80e03c078078030410b09101d1684151840201940d01455691001500d1108009554200d0a03000040070302c0c40314034510106484681a40284540760b804224482010b07410303880c082c002c0e0b10803c0200b2210034900019252200b0883e030140168028100410414481c20b03a0130032140c000400000f0303056640100482528800c0d5240481584000c0400c40032240c640700d000090841100c2800c04a02c442001d80d40e00d102c0d01c60000e0404d03480e45200503700c1d008841005900c0c02c86800c5841c1e2040d10300381c102013540581001d445010340b280c04644000e0406500303a00120040102441e402c0d001c2c843c4400d00040300c62566055942c0c1c0f8000f8011490b00c1c461045150030039140075 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 731397464 1250 731396214 731396231
    0x60f0e040e2b14030705030601120c26010e0f1b07080a08090705030606060d0f060e07020d0e0d11030a1a01050f01260414060403050d0608010902220f020c01 69
    0x2da90228541500806103c3e038800820464403400d07003960342c80b2069142403a40c82c0c0d648001220215180c90020084605080c1840d42c1d07140c1150415140b141305400d040100f2036071203200c50110350280316072850300e1182070101e901060740b030701c01a1303200c844441400c4092940f04402003941c0d10a50040d01c1103140801c1c00c010b1194031810707040d0412500c80040140c1c0b42083c00003034882d0703009815644510000503c00c003c20080f5040015031003507000042000070390300e10010740074a0003150b07098014011590400c200740c0c02a43d18169401c4080c04141408043c0c0d0398245903800c5071000b03180d240c4140540480082e400140c60100c0420700000440705524000902c00441c11080382c1300d051041d81c174001100c441c084504550b60911030103840c9150340342c5080544d035200d6084810592405807404110034103810800a08000c28000750400c5200c5d601e230200d500321035004000030760112a18081e000c10420000b80842044c14010000a00000070b0b8040c00c01c07680a0603107d44142d440d00c0c001e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 731398714 1250 731397464 731397523
    0xc15050a0e0102030c06070503130b04050d020d0816080c04082d0c030619111209070906180903030204091a0306070801120b0c1b011a0a060f0e040e 65
    0x26040d55201c00e00045040215002200380c03a00f00c028103003810400b021001804042c16030b41704040741600302ea0024035038145410070b203403a05450a9010003500c6440180b0483c4d51003040b0300e038401c907040180c071000c0a418860403198220301510310034042c0c0d018003010031160b0041c803891042d9203083c4940405041103128800722103510702c000c0b05a13508285125581038030040768039980111605440408000c0d0718140d100246030501d5504607201d008110341007816101d0050f2809001c440c800c0307135802940c03a003114042d10321902070315035245001035021000305441d03000419034074401d080240c245522104203c0071034aa04040c04a41c0d11344c44034400c50f604051000a401c4256881c02c00a1581007448008080d881c40500800d1010f14600169444458000b624540e07000b8a800320045c81c50070b1100c0d0b01030103580b45002c41e131005402005c0f045262407000103045034200c0d1a50502c1d9141d030f007801e4440441105000350095140c40d030100940b402444400caa64200400404c0c542240d400c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 731399964 1250 731398714 731398727
    0x108060406230f100915050607021504080307140109020616020112150911030714070303090611030402031b132007060501170318310e0c1e0d0c15050a 66
    0x5e04106454404d0074000190361400040542e8820344242d65a007015101081c040e098a903043c1031411400703c0d0108125001100400202d40104c4c4c00b080d5085e1455005800c07501e0481000750320100070081c42468600f00702c074101082e03005050000d0ad0000b841803070401c1d1080016081880c6d069040b062041403c01c1c85121100300a000b1036506500c2d0001006d000a40c60314412640481e0100d1b1100070140709030042c4561550002e0240a01b20814251100710340054a00320b129001e003a2203000c0e1168007000001e040d80c0c000700f148040d424003021a034000c115100c130102210703881d9082036140d0304035800200215445143c00060a40c0340059105e050710220b22004400e07041000000c0031f00880030500c3d250901c04594000580e4003212420100300040d001305400c0c292180c00f0b00b00c0d10a00e541c0308405241d1658296a51350070390b64108070a4580e540441c01e40a50030400c150443e043c84080da03803400b8400e43e010b1403c02d031100800075140c2883c100c2403000034000500905c003d40d0060f03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 731401214 1250 731399964 731399969
    0x108041407062312070c0503040f0b0d0e0d021518070803030726070503220309060e010c0b2a030405030712170f060f060d05010317030108060406230f10 67
    0x2001d804c00d4075030038902e411004c1c0a050482080b10410240050003c14021035004090ba01c480109699440c604890f03150080c0c01010201458410344015099001c1041440c40d20191302a060058400403003405407103000d000003000f00942c4021501f168001c2016101800c01c440c021900c074603240d00300602a4181041000c5801c0300b040006240c10305c0c04070031582203100e80c20000e8495680800c0d9500940075075071078111900c48081e515041c15003000220050707500d82d036140043c10b400d044c015100314440703a00081440010310002540400000070030400d54001d2180b41405060004102c042178000351804c1e100d41e0400240002045031302221543c83c14100d05209003c000f50200d030407854440104030b10f10548202d40082d58682e940c841784018217070014111038a44112141c1c11004000034002104c10210b01c44004c07040348540003d07241207c820400420701542c07507941e444041e11465600b00d806c122502c0c00c03031400c4c41c0c248e03d5080c861604925100102e1810301c2e01c06000d03a2059 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 731402464 1250 731401214 731401277
    0x150118020c07030b040201052709100f050d14030a051207020c1c03020a0c06090305060901090f1217011523040909020f0409030302040806180c010804140706 69
    0x401000c0c0440c41e0202d010030440703410025456071541d503400140c502d813241003048801c510819000d00507010380d081c64104503d0081c0e540c60056a03440481c3d954906040c0240d40150398420810441032400104c001c034031510810681c0640903421040350310350307045044045c01143c408203440d6842050810441d6010304039200a2041d04080f8010600c00c4400f0141d140121200c0ca10386018503000704819078006912400c035294183e986c3c5801008030b001c50104403150f0040801259406005001d4541d005c0c1e0001188a0550415600c48810b0425030b19404c2c14800100e171402180d881c4004894000d00719910182506120b65000410b42c00e005400980078070b03990300d0005101081942039a0943d20014400180100180001440b041c00e1070200d65100e0706210b0341208060f03250300684101c6203030b07908a0701140c888514800c40c65440b07059100c03043d400900304000c1513100300380c5250041d016001300d00b07846c1012494503082880d41d41109021500641490f0009982040d04800d1803117407 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 731403714 1250 731402464 731402467
    0x20c010621081602030307020a03030201150905010305070e09070b0c0c0f03010911150d02070c090b0109030503030c1c09120e0d051c02030c160f0506030f0a1d15011802 74
    0x250340d1080030b036000e12598441c2102030712a085086450400c101c0709582d030000c2620101c0c1e903491400a010742030070480d408a2500700c07100011641d00b1406014140c0e94007101409140c0e0800704403107000c0500070b000c00d0403489514030020310b4122946c01405107540e003c0c003a1130b59042c1441030040400e0f58294480c060307032411600c02c006c211142c0c003101400320120350f41450b2200e00741c262074007400340f0344207050b28a00c006103020403c420486e500781101c41404042c88080009401501e0000c03051101078040d800801c00a560b00c0c48020043c41d07544004c24021000c0000348820030112822074400f11602c288182004070015081511200007081c212089008040b8569409456030740c141481c0034800380403548550b000307000340107a401c0544043d0031603010754203895100b08105200c1c800c691030030b0031400d400b08440c00c01000300c80c4191800c1c207001c002d50725010780a000510103840d00c0c4401e6003050780c0c00240f8100070700004c00650a9642c2c891419410414940c00b41e4640880e0042424030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 731404964 1250 731403714 731403779
    0xc150f020c0d02030c0301060b09090912191b2a18020921030d0507020a0c03030c151e0b040209010c23030304060507020d081510030f020c0106 63
    0x500140007184000251035484200102d0700c04a071801d980d00071381c59455405c0c04001314041020030701038294143c00b21101c0503a901e507054a6521203081259400b1040c908008148511a41040f111151041460316111407106021900e4030700c42c0c04c1400b26419400c070408001c04603da041c241c030918030319041210000c2d1600ba49060340c12080040064020b401044244550b904d0042021a40b422203800c80481c00c0245aa0340c0c8076446170b0046900320f07241402080e00c1743e100254265030590720649628405055840544103410741441c00c40303104108191041e00250b03140245000012049164450600074040ca00191141803031083c1c0074038410300c0001010303070340695001400f94120400200c04201343c3c3c0480c11501040901c03004601c400070074001045803580c01648106d00c3da40c2501d10311025100d04071256a015501200c01300342d84440706a440c5410b003181d003a1000d03142800184501d2965014050760099110114686d5503180c040242c0001c00c0e0015800042d4091181000384 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 731406214 1250 731404964 731404967
    0x40213060e1807050301021b0615010815120a0c06020d0c050703110303042c011e09020d020903070806041208040308190f050f0403110a0503180301060e040c150f 71
    0x10740041900c0d140200d10242003075200c00074002d900107090054000d6581d134003489968161206156004a41d51082d1000948039803195001d107801108140e40741281c50b2030b000e0301103401c002c3c100c3d0b59580c0840040440082ca80c401c0100b000ca40e44900c002400c1d05c0d00d000e130080e0821044030a05418040220a0240000d4012405109513903019107164000807001d404240740d0700440d0820081c00300703044004030104030b0071540300800310083d56a880f402c0e078840104c0e001d5030200080302c20b0003001c030400a005964164010f024400074445005080c824801c00007464203100e036006498640080b810300c81400040b01c4000482c0300d00f4140301c2c0c180d04050f0f400502581008240000048001d1802c1c400761805030043c180805030f10360140a503080c005400351505005680450100c1d50030ba1181c43c0c800000700d0604040d40d0008065420700c001e1030050742c1e4280354804995459540e4640200740c3c08c00f100342686c05a8054040020b1203800c0c090802d0010030111444018000c88800c02c12420f03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 731407464 1250 731406214 731406239
    0x21c0e061317030403030b120106080601091a10050d2c3f1c0614030a110406050301090c140301050f0601110a050f030a02120301030201230d060e04021306 68
    0x2100b0480d14594035079403814114010000f1007409903104c8403100503103200280c1500010b060718504015a80f440e40c0e0341540e01d013202c1e43c2c0343d03441200321504104180c1c245401004c1c10360400c0036091031450146462914030882d0000e0b1074020200710340a0003980901c2412580392202c500400080030785914210741d100340c804030f882e16050201d000000181074841603035a1680610303041c2c5c0d007940c2c96107a0040d11801c1584034010044049240460000b00300d0054003c100203180b0240203440b4a4803e612400003007004c0354607445d0003d45072040021251000d00c9403030301e014002c100095140f8100000300782d803598000901071007a0704140600a10840302d20040341c1106003400e1040450181c130300d9081c1050460307400a0081e0060b4042003402c100701000605181d0055401d0328500c0c140b03140c2c41280d90000b07020180c0090203c9610764003018200d401d068042e0440680541008881e680c42c1003034444a80045400812140c1480218104203400902d0000201300a0118504082800745d8a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 731408714 1250 731407464 731407493
    0x210c03021b010e060c1504030509090f0709140303070c0305010606140f09120f1b0114040b04090c021509030901031d0604030315051c020a0602070b1c021c0e0613 71
    0x130780c0c0000301140c0501042142040300d030811030003055103280509000e4195040450043d01034010840003c003203503240354100d403080c1e5854071070f1886541441500800d0b60460300e03103543c0511040000d0f40c08500c41d50412002903101d40d001295030340c2400c1c0018201880c9048003078070781405010002d10310395030100b40e0f0052201560350350103207200102268030f8014214044022401202038202c401d046100c01005200d000f030702d9220f6070071f01010140c0c00d188203501c00c0c401c00380700500c4240b000d0082600b0101c0d24000c0342c41201e480d043c07400301000b981170b8143e40001450b0300008036118156014010074000104070f44052480f02c003c2c0b9121a15040000c00090416958448641c00b22003000c60040240202400c40d000e555841708602d4001c032078000059125000b1182c3c001402440000d0201c2030b261040301c0181014010141d05110300d07425901a40c1c22078013401800ea40a1070000310344925030340c030310000c100ea0044485590030180080c0c003062a0b070b0002d01c111400320b0f129005c094203 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 731409964 1250 731408714 731408719
    0x803130e0403140d0204120b04030906020d02032d1b100b061608040909030e0f0402160b19020d022101060c0b04020a050904050f060915060904210c03021b010e 70
    0x5944840131900c00c001e1140e6084129001c80300d0190100303000280020078030852190310381c2111261119800d0743d84151030740305040142e2042000343c60400710107507240a003502120b6013400b0a80703800c51041c0c150f0801d10900e5100742c8200c08062090108100c070940800c4411420042002010b010540912640d05c48095a900007c01071040160b03078801c88009111201e8200207007142440c00402d00b03052038807550300c541d81d180202245803801c0d10841d03030000a501c41001e41c1286d5030b039420501540051450748013450325071180411800d180000c0844910034940141d03034030400d400004a49480da80c000522001c040014461180c0180e891064250080c03400406a92584001440d03642c00d500300c242c00103003000501041000000c0c0000c00c423210b09095a00a690f080b507815903900c054240185066a19008104d003814602c0000e50450b02416403841e51400d504149000041020300c24000549142d660ba001d066050280c40141d02d86d004003070112000c000300080c01c2c8950000c0039132 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 731411214 1250 731409964 731409967
    0x705040303120507020f010c020c0f040509030a080403030f14040b1b180d0606060e011205060a1203020a0203011e06090b0a033c0204060b07051f06030c0803130e040314 74
    0x5901368000c000000180c22040004d011590700500c0082d00d4081c01c0f034895000c3d42c07000c1141004d603c0c160242e03500c00c2d000c0c9001582000100e4100300c54014000c0e00c00c1d01030580d10b4421080c0016180a010140c400710102d038034050400345403401c05000c00401c581c603200010351025441c8031030b2100301d0f0713001c0b88804800910b100e010400601c0020001303400620943c0307405070000703c442c0c01915400315004240c80d1240e0fa05207401c0840103903181141e1042d44400ca0742000d205040101c000c10a005010388102c40c081103641d408a030031141000140c102d104441030703017260940f5583c05000058050315000b488070004400100e0031441d2640001082d44032031b90136500e003e000c1310048000561203c24094010a17062060540c0006d918200380e00860403c0e10224182e0558002c03a034520740d100e401080003055807807081e44450b8000c1080c1088544540c4004007140990f8105005400300c1c0d000b5595440710301404a04443c516400b15042104403030820002c030340c00680c158014560003a207613 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 731412464 1250 731411214 731411221
    0x828020d140f0303160906140a03051801050f01211703040503120a05010602100207080702010818151614070b280902040c0206100311033307050403031205 68
    0x6428040c0300400316000f0320000c0100300340100704c01c000180942c01501c0384c108068a031202150003070821040d101348810f0401c00441031034400d5000650121814018001e48082403954900f9540156900006032100c2001803100071586508910103d04d039900c94000d01c3c2c0d50384d40340c256510345540d104079220804000201809000d00807601540c0d68007604182070324000f203000b0300401080c0103400040c842c5900b041c104028510840d000310f60030075a07450410300340c3d0303004503149200104a48207008203180020000d8008000307000d05400f01c8900b900d014174000309000c0345036003100c025600b00401c1c640c02ea40001180000c0f6204140c021a010410355540079150403500310541d4443c10f0658502c1850f0306000d5507502c0f141d08248201c0d0284444030f000041241c0e520001c0c2c400c04024080c0b0201000000c114002d42d0084100c098240c60140c9000c130b0314000408075a1081c00b400f40c0c0c00c500044408032035040500e5001c0042e003441410030b800c54500800c9112010780c00000b881e03980c00031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 731413714 1250 731412464 731412503
    0x40f06050c0309060703020f190b06060a0e09010807050117060607030f0504050a0f080f16060e012304050a0b0408060c030a1803030c0f0201051b130f0828020d 70
    0x1100c0d07003d140a400950388004916000356917003106c96129000340203001c880001d40108500812900350400640e0449413500070800c0348a41c050034498052000c41462103030729850b844c0e5464020f0220030090110146420009003000b4048100f0400300d5462070104070082e40c07010142c03194260146040b540c440d1030713040e096500c3c1c415604403a0b84840d418a0000720b0501003102c200603234560a0584502501d55102296501c1440800e0034090090501c103014180c4a0a080500074005141000306d009906500030401045008404e42900001506000301d04240c54102c0c000c003980c0c000240341c51301c0d002c1404c0d01c83d480035110307003030300c1e040040400d00c440019040381c000c1600702c0c072828200d00d619190180051040c2070464004c284c181e0b400c02c8070280188540c0348614000b17001d410300c160090340d42810550114001c900c02c110301100200f0482103a445140c046c022000c0140f62012400b400701001040c403201d0110707030a45116440006880c2c888107103803002d600c4a00c0301081500082c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 731414964 1250 731413714 731413717
    0x9160b0414270103030e19051203120109060302010207230d02040f0f05060a0611070506280e010210090305070b1b0a0302090405060117011e03080406081b040f06050c03 74
    0x208914204102e180c0c04000c240d400480c14101c91082d1200c0f12002504014010f0601410f5800300441c0c20208040009007486840c10825041c118280c0c0c1c50100010380d0408280001e030085664907949071401e10465030100140d5015044604260800218564900700c000c642800b1960140c01c3c43e146050441d181e64000400c204030100c801d01005489848203402050115452441411802400a2038500454402c1c400181c44000390280a082100740304860f448031040d91010030340e200c90301e0311103456010520b080030702c59070783c0900742c5600c400020325100c3d424070003080749132800554100090308101225809588807048181a0f6204604c6000c2d0510003204410640d41c00140182c42075410350083c900240100d404103c0c5460f44801102c0c052140340307410400f21000c0c0014002c40320303400c1c94808080303009400040c080362203540f5414190001da02c45004500d800b020b1114010044a0031350600341c51062441c01c040c98008500700d0300e00e0911622080c0900000e0011603000c0500 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 731416214 1250 731414964 731414989
    0x7030615051912031814210309120a02100504060f0302030c09120705060301090f140601020a0b091c05120a20070302010b0607050601052e14090409030809160b0414 72
    0xd404404a5480302c1b090042c4107605100ca01c98141c030400c81c0200c02c100c09401d1229003c42000314102004c102c21700c161214400c20200c6240301d8940c403a03005236505400780c1004c01007644d40070703122494075001400440340c00350110181070040c0100700d04203034071905883d03543c042100e10410204140043c00e0406805421540d00940000004211000380360090210303402034030801c004003110b981014805810035502c2c140181c0000000d80b005c5002021160703003283c41282515022101030600a1080b1081c2d0844000f2950104200f68010782e120302c80750744600d0b5408140190040100310501910500d84080000d180100d2400280b51003544000301c038010142213140d482c212030034021781e920b100f40b0507d4480e842c1d42c000c0000c42c44101504100285510041d11214411805e0503240b0040000c105440001c0070310040503241e950b802180c60b03450007078035040028140300c81c0080c140800030b2410300b640024104104100c002400440b4115880715080000c0c43c06084005400c548084 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 731417464 1250 731416214 731416247
    0xd062c07050108161e0f02070b0309070515040e0702150106020a1a1b041d0105010207030b01050f01030b030105070c050105070e30120a0f0801230f030703061505191203 74
    0x4000e01443c1c51b048800300e90780c5000f5800b21499140c0e40e851112051108403000c01c00764201500402450400c25a009040803407040d1940c10103880f980340740394800b411107032600140d00422224101030112039120b070140c44184003a103084265515801500c10320f14a8482c18040150001442800c41c101450b07a005403043c05c2e06e40d00da50340d40490078079510201c5449214281c1c440009250343c00010501c0480f81d01100c3c0d103059070b103032400700b010380201280c1403814540c543c5850070007075800b8810b451040004c2c0e1105109071629080250868a00801842c01d100844240241990301c403904900044544e40740d0b2590071801807900c50001d402d103901c0260601c10030fa070059407012240042c04080c4030550712807001c0a4425400c86114600b84508100e840054130100c0040303010840d4544000c00c0a0804050100d40c4000300c1c0c58030a003a4001d8501c40d60b80e40c1210500021007800c1d0008140855205090780d0f030f803448155484000e071050051200308011a54101030241240440c00c0104 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 731418714 1250 731417464 731417507
    0x30a0f02030c0d09081e060406180204090f11060a020a15090b01080601081501050607080a0201060315020405091311011805090f06120a0309140d062c0705010816 71
    0x10710005000240c1300d01a0458a00031010308003c4c440740c13103c00c542c00c0082c03070004041d55202c0e034032100b0080c503002c1c4034000101c120056007000340c0c032140a10031003544240c212102035205820000d4204414400040c410581041403010095002440303d01081d009032074040110510002503000309584840204501c800000000b0720940c08517000e03049030840d07019030b010420600c1211074510307001d028081d07000109101c980041141d03500a400c0e5146c0c03034000041c20a44a481c0e04e4011003d4a01c02c6c0d0620340c000500b8000c0c0c1c03c1c040b4400b0303000800d05c45942481205d51b91811410200300600c0c0381002001d02d00840c209006c81a04401482c001d047d020b042d0504a43d20410284111940350107102c0341b011811403000c0000c0d80b00400d035007656034515018180480d0030f1640082480d042d43c030400012500000c43d00724801d03070582852190900307010403059016079800130b0036082d00c040356410440302080300da60451402a4400382201420441300e45140302035400244091060029401c2c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 731419964 1250 731418714 731418733
    0x906060d09150c1101230430030f0b06160215070308040b090607020d050901121a0312040f150c051b0f2209030903050d0906091502030a0f02030c 64
    0x10682d010103c041c0c40d9035254040200d48040e00c80c00d80300d03c5088007504240341c500350b048560700d400006030402d1094440c0409501c860900b0300105441e02050405d19201551705d8039000e40512403280c482036600e005110311125040003403034034003c81042d00b01c1d880707040840318115919508403e0200c030040c8805604e506080c140103200d600c08860441d501c106170304c08910f803007000290340d40c0301e41d800d98010418448640801ca5490b0040100c00d03051040c04501015409084c0c054034402400c0d190481c100001100201460710021804928960500b00800c1c46440c4448e9000d6080d00c4030300d105410000d241d04030440f01c47e807210708050424018140040c9411002d6904034005120031240c1582c03c0c110402003007080a070101d00700f4030703155160507001c0701320030a43c108100090103400d101110a035251503080c00d0284490810001030405081400307403d4001080c00302400d2002c1b1090124400e99101139901c0c810082040188a0a03400940426100b04112845070200d24103039603400a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 731421214 1250 731419964 731420003
    0x130b09010e04170c0303150406080a06020d0612021c0c05090c03041110120902062218060e04060228020102120f070e010f1e090501030b010306050906060d09 69
    0x141c0c19107040310088200e00f03c4500386041c1d6010749a51411080203540b45480302c645000c3c820700b540680131340258aa80000440040c24001c441d01e040c040c180242e81c03000480030550842d500c94114081d1032a05404d42c101507100c844420141000c3ca0342850b52203000c50410210030000e41d0711071507101c2e03504810410a508018041c60142c3d100d0b00e01000c000911408100b00a10300800550000d0205440c10403000d0700c5421051200780050800352808455541c4215020060310042e400c1d000401010056188400c074500740c0302c83e009404001c52800c0c08481d1651040107400605030b1600031907050300803c600b07141105501200e291a402036601c80d02c029001c0e42000d100f00c001a81c00d000012103000e21280c030107209111a42c1c0d41d03240305c210b00006541d00d541051000b0108030480000c01d41d01c0086408a11241456845e60310750a45408001000c1d40c142c3c803c1f00c2e0405003060000c0109481d100c4210750098003c0b03451644400001c50510000d000a41001c0c04102c500e8980b8840f40 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 731422464 1250 731421214 731421239
    0x60e010c03030f0f0b0f0d0314211e0f06090f0604020910081501091202010f17010e01030b060d0c2319140a080706051b0609100606020f060402130b0901 67
    0x54080e204200c0f1400c2c2141005907981500c0e2025004c02e9600c1807154050f40b14a0060802c814000400a2b0b03043c01c04002c0d602844048031200e0142107030300300c0900351381d5134109505c0c1d1004049020104070714005011a034546806040e540030701c61840045100742d0764540580709022000f0380402001d540e4540020154441550310140c40f007402c032550030b5a540300319000030a841c0c55038807201d480a2164011144502c08000b41000c01080b1002e00458400c050980307402012441c4203184194194108166402d001070a080d101e440f00310014000030b611100a2011503041d07480181c1105050340305000d9120915529a9208d4010059900c102030b0100c203590698209101c07120320031f00c1000c2440344c150480d002d0000c140d884051304102651140c0028006404c1c41a0151090601c22824520304007003a24420b03c40d0f0000e0a01491301b0906120f1040284030341d100404421310002c180c15190280940064003608960301441511616900040f9003a071010346960410342c2d490483c1c8511 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 731423714 1250 731422464 731422481
    0xf050f060708061e100e06040b04261c050f070605180a080706020d1401060e040e070510080402030102120711071509090e2b021501060e010c03030f0f 66
    0x8102d440000c64400d0400d035051020003210701c8030803042407a00300d00b04210002498106400c01c592031040a405880300b1010304000c00600302c8403603c5034100000c0580c400c180b060300c0c403c4080c4101b034145050900140011a0000c1407040c07050010102c1d804031174600c0350104080c0702c84400a0003100b00100350340680e11400002104040401c44643c9898864850f6440540090805c1c0944000300304264020082c0d50a44d00d80002c7c50002c0380380c00e041e82d82c426401140483d24542610310503081a00900f420420301e01c000c0c1c00705a05100c0060340d02c1c08848141400c110400f00002c007152401d48c1102d0200d00003103210080391038030301c0f4001d02034082c0d1034401000d406080e00c00190300f0001000c500c111000d98640d03040641c00c1c2031021006001011025600d4400c84025541c419050805000d01c807801500043c1c0354042c07804041e190020300c034000c3d0410780880c1e00420886034131401034a00d540003460b04003d0f000060400300d002c1e054103141d003180103107000d62503004001c156009209 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 731424964 1250 731423714 731423717
    0xa15050c250606172109030303180718022d0f07110405010f03031b03050a1b020a03050c0f0616030c03270911030f04020441100b0706090f050f0607 65
    0x7565407105617a602030700481700c00c0c40e00340e8400e1001c80c6080154032800c4588032030304400c07034003100d507a1448003070344641c0c0494081041da80018603050307188184800440d81041c046207a03401c6000c419102000e841403031900207903600042050000c0042c20310710f98900d07a0006000303114658440703c01c1518100507120031800720b4114035042d1451400606002052905511524242801810241d44040c1c503614001100b2041080da1030050b5200c40031180514040d03002440700b8900102881240500800800c1c4510320074001558289550b4805541c0c0e0f80e85458a0384010f141c510f41030310911f40c0e02016844a030001001000a561444012403c42d41100d0b000d214125000030800c030300b4401a101100c13145050800100541481c3d0000303d003d4000040380005001c070001d40703044520705480d8030024000e01285002a180c4582443c5400041e4149095843c520385020040544103141002f861552520050300a02c0410402184002d401c903080d69a80e4900340102a200c201c121201da0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 731426214 1250 731424964 731425003
    0xb0f0a060e2505090d110424031b1206020a020c04020a0f080907150203040807050f010f030e010f02070f03020715020c010804140a15050c25060617 65
    0x156014076800850048107004908403140c064401d1240652000c44042c034248035040001c10450307140c00d40c08041d101d0155601c014000300c1c80c0c0801041d643d1440080c0c450543d009111000321448070758840490b60300c0a85105c50042d441003102d40c9803020340c00001e00d540c0540b02e5105101c3c1c0d640007800d071105968203982c040880b40041203b24040c075a00980050585140030b00c46a000703103411500240c9400480d04c0c25542c41203079281c4c500b82e210f5000c00607040840c04008404080101101400c011204110f961802a0000b0030480c82440b071801050f0702c40d540210030301800c0d802105120001e03501556140c500341071205031071030043c00450040c07041550000c1c80d0f81c252001c02014144c1e59002d0148400c510340111104000500700342d035203404110148803030840400900c200d551080e081c0c40e441c0040780600b8000c4030001481200b02c114204860b004006c01c600549416489144504042e200340b0b060100c000c1984e0b0300312813045000c0341b01a000200000401c401d90100c07181404 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 731427464 1250 731426214 731426219
    0x2116020a0b03091504080307080901090203030a031508031801080c0c1b0906100824030604030f090803030f180a05010501090203150301180b04031116031e031e0c0b0f0a06 75
    0xc104d50300200d07000340050b0303020f0021429080c03180d043c023600000d20f00004103080c2a540c0000741941d10520580010903940c0c000034a09090950300d900041041a01039400c207000a1405920135081d04110f41c10020080001151018070301d06944441d050358081b80c1d0000c8840c1c85000c4d442800d0b44a80c0d214401d000001000f0741340176003100340c8510990352018800c5e0ac415039142c0c000c40300c280c0105a06140f401c0d503614242c41c200807441c030480c025610101740c0807400742d01500c180016003012186802c00c03c00c00188113446004280c1013120350090019443d0600c0079103041030082d820081082d400c0078000104e0030860f801442c052451000f09500c4000004101404ca94400c501d811818001e0306071000804d032510000c95015000742050700d00210a05402801e100e104000c1d403a81d05034154080c411710145400c4200f590384004040181040c5c6924081c15500303800a20310403c01d042d44422a0162040751600c940f81d031b00032000401d608000c200d08041c0f10007150301450b5a403400900 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 731428714 1250 731427464 731427493
    0x1050103081201090b1503060103140405010605120613230d1206050f031504020402070b090d090909050c09070311280c02061c02071709040b032116020a0b0309 70
    0x483d941c0c130000030062030540d4400004846d140d0070007030805050542d6070380b40c5500d4400b50b40c00b5920491203400005005d40c20701c0200302d240100e01041d442151704c04000c1011006010301c0c81c0c0d500070741043c00560024041042c0032030140c5080500a043c0c007a030303c605000d254206607044840d811110040c01240d03181c10031f00241c07945030360416078150300c01c1144043c10b05801034200e4200d400a40b015140000c10780380d2071150326054031049100d903c003911280090394003040580c060407124205102c8202e1a480e256036500740e0381c40007481842c200700800c02d001d00980c0100d030702514205156440d01038101020441c1e40f80c25418001c404446008280113520800c15030805940c002e11450600700150b480005c0c1d41c21820107410038030f90800250010901c140c100700c00304040400000c0e5902c50100501054440251005000c1d84c80b102e040e04405130b20790950696180322042003074542003a591000d148218610b8060740203c07900704d010a01480f0040114801e141034011901340c80d924545 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 731429964 1250 731428714 731428721
    0x30b0109080619021b1204061206050108010b090a210204141b0703090f170c150f070f1502031b0403020604030209070c061d1b03030909090307050105010308120109 72
    0x9048950081883e00032401d00c9041d8080d003c0402e09000041107240f024110380c0c40c007040340c0300c20004410082030410140d50b119213108101880e994060282c0d0f07140400103004014180210b1003401070225220849440c1c452910b00102070b14110f9110044540186888401034444240e0140d0b09114040044900c035140c0c0d14054684400c4a04080d00300c4078480724560000541281004040140084c0810702060708001810818680b004124040c4694529200c00142d83d903005080c182603c038509102413043e039411440e10001590754141c20b2a00d10b10129070102d0090a08614401c003028503540303030380039502c504c2d41c0c821450501e9401c002e000c11140030380d1000030b5101004103c10f00060505800481e005011418a01081000d580d03462040e20003c18000050070541c00300300220b09020080f03500a8100c8990a240801c0c1d0100425120b1041006140c026000c01011410b003450400c00c480320180c2180c001c000958580c60f00c000164842c50040201c14a03420001c02c06840718807 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 731431214 1250 731429964 731429971
    0x1080402180f0a14090715020708030a031a0d020d020f0406170114011d04081c0e1606090b07120c1406090c01050f07030807030204090212010f0e01030213020d0b0a0303030b01090806 80
    0x4008119207440e152007c02d00c106003044d820214001c0c00c2d400110f8540803c0504107100150b01d02003818822001c00341c0d0199005903800f441009004d44a00c00b5071280482450510380681d980080d0750b460501040c06450aa802034450f1030503104440040232065111040000c8203110545490f42e840812040901080140c2c40c03075068100e005c02c0011799148001c148034601640e0800d41007c0b02061103003100c1ca01100f510954110b002c2c0d09031205841b15801c80900301905000348032030305100d943c40087c099184001d0154600c5030326990703a1409a860005a0760303009100982c03482c0c0c0e0549070340e195201620071545510842c40d02e40450742c001d9003910350280d0300786d0000c3d0901c1860384003229207403c050010410b050342008042104000c0340014240500c0705c609032041d40d40740400c4514003003000c0c0d00c00d200703088401d0f00500040e6116410b02c007522150060250301c5a8200512800a00f0090300040e4009907034440042016010f0f00a041244002d032210f40002e136496511549448044 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 731432464 1250 731431214 731431231
    0x20c090703111804060b0a021b190603050901090b010b090a060f050a1d03070b041a09010c26030903122a0307030f05100311040e060a0e2505090a0903020a0201080402180f0a14 77
    0x11081884a170340300380cdc000c6522407044c400200358140f294a500d066400b00b0713088003070113410019000d01c50b42072840985005007101d01d0301882008181c0001003881c000c01c91140c080060701c102c41e0000d00b4030322000d03e0104100a0503580078076541c50303910385140d00038812030910488290240f1030020303014007500e41381368040e111213001d4559607982c1c814468103503524503905054008140500101503010310b00c10f070080c1005552b1502280305080c1440401841c1c0618404c000b400842c3c80c400b4003042e8810040390468044d100c1e00c6228003507018181e041c2110172221300c1c00040040e21000501c044040704e0007414440c0b50100808240810f80c2c001c13194514895121070302194500d59113620038514580f01109481e901c1c11442034078190f111101a00484050101c01c05000741c0c40c11400c017a41054419408100c5d4003030980d0065114405014082d042c480301c00005800d45d21303421060040410f96110f40401752801040000706460301781c811070b20007850840010202d224103501e00e4054550b1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 731433714 1250 731432464 731432509
    0xf07020a12020d080304050f072621280c0c050301140c0a05070618030908070e150a180606020c120c06030606070b07020c090703111804060b0a021b 65
    0x1207031074441311540080c01c115400c2c414002c0340584040140034103030190051a01c0000240200350504a142351008600d160a4020b190b060f2220f48440302a60390481c200c0c121281c480b02134100108000610900d00d2049815050300b101c1c3d515130015503040c0340c512903174040c0030141d00c81c0c003403508848031015440c02c0100c0394000b003031786000850090300c4144034514040789005072659540040d0b0718902100d40c0310400c00c0c40e603401019004001c80014003001401015154039006200084440140c8000c1080407500c1c9400c010f900c6000c24003004e850100116458210b9000826008100c544913560050040142006042c5469916140c406041600420b0091050820441c00398405001d459001c0020003803500043c14891685200b003d00c0e03009885205030201c00c2c4400d04a000b80500304040c07400c8182401038094600b500d10103650604500110300310000460001e1810350082410300c400802c0c5e6045c00c0e580040c40101131034001c104026007540200c21721141c15642c01451260070781 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 731434964 1250 731433714 731433739
    0x1050708090c0d02030c04110712140304030309020d0c060503070306080d05120603070302040e030d061a12040f05030f04090b030d080f0a02070c060327050c0607170f07020a1202 78
    0x521400c0d000070240000c5c15120795180c2000001c00300d405541000c11211804901001444005c1e0209854100c1d03506010200c030b0b40c40d1404060701c0c40001d00040c1455951500c06080d911f8601000307189517440f40900400a0322585e0180c242d810450322400040e04050001c50090800328520b0406c02040d100c55090200d8404045003000000b00b013503401d44592100000035170390390700490b120580314101969a800d4080401e0090351215000140304000e80c4504001e8134462a0071078000030b400518480e0103445610b041c2c4045e500348400034009103c085848500c05080d01c005204a82440d04108040c04818041c5511416010151340100304280001101c084071500c101c0c2d4008407900c001071900d0095500c00710907201c035403c1040007d64826400280140d000008000308003c0f81042d440c4110035591666120b8001903114000d000c00b180c01010015209200181a10201c102c81e0f00c3d821100480b41e030365009280b06900c0784000700310000309880c0380140000c0003900500120320515 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 731436214 1250 731434964 731434969
    0x70212012d0f0504080702130501050108010509042111071703030406020309100e0105070f1106060f04090b0405010e0d050304030519050702040e060604060b0a120c0513080c0301050708090c 83
    0x340588503070201c8035200c24903540094001e1040d2485544100917603a100c00d0180140602c560089064040032072500b40144001da130041d5040c0c0c1104c1048940b4482d550740e614150205458612000103d40742c0e10356120030341d6800c0741807601e120700e1020454403034981d40c00c06600107651640c0e00840c507400404c0801c0106100d90000d40c1d014a181c4e080b101603461010480080710321000d4000d516940d642d041c0f2521a17801650000d40066510b071502c1c00400f40788045484d908003408582c455002032036a032146480d0740c1c0001460b41e8000f403505c0c04620385403c1c554060940380007103903043d010f81c045202030ba030f00070000d0724000c41c0c060b5100c42c20300e443d8608100312030240880a03c1800005d10441e001a95207026440d108904240940031908145080c0000d07600d1941102980c040103120060b88554005050300e00300040440c00f29203640c1c1d08906594601c2400c84002400e05165004540024009528131a4000a40003003045640301c0408413011942034035000d110b034100742041000c51 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 731437464 1250 731436214 731436281
    0x20603310308060423040b0403080604090201020d0305060a0f3c0303030b130e031309060b0d15030507031406070504120b0915010f0501121a01140706020301090207021201 75
    0x168541c41030341c511700d060300c0305030207081d20101c40132210804240304010406501c0041d8079042001503034180b0141125500103900c443e00140f100c81019074881c001415561068045c2c401803400d105400000c58a40b01d095802e000151000711140003107184014204211040900301c0100481c00c1e00310303660079980c1c21000b0f84804c11a842c2d0000100c6900031a110b2184181400d9000100040d640c946a09520318021030659003e0101240f61120401c6000ba80b20200c44400041450020b0100d07410000d9014050542e0000f84c40c0c0c0c41640340100802c038030200d41a04d4410316608a0b0030307230754407014105c0301c46c8994000d9070368400201c0425070001d0320250803581c1110103102610804008060702c0804190264840c24104107840c0d403c00c06541c010a64441500000f0400c1c8081500c03880324440c42d076190040141008201d0b012104402c0c900d4003030310f42d01980008255580d59440501202a4109520a82c07143c2c1101c1000c42501405100d1241409051f0003102108041030050400c107 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 731438714 1250 731437464 731437481
    0x7051b0117101e0303020d0f140a02010e1002030106200a060e1e07060e090103260c0109050106050f060c0601060e030c0316152307030c0206033103080604 68
    0x8220b0a00d000700d4607400c040040c00c0020062004040001c0c5503007002803511017144003001c24440700705208012140d01c58a00a5803401a50001d40c0c0da88031060128018950300034500c2e214041c0202c0a1030b01c02d1140c005504a4641d03a40d00456205410b9405889061414030076045500019600001600caa0000155401c042c1c00f40c5060f40790b1a18242c1c095a5841c08012140e000081c080c03041c1ca4201802c503481c2e60003958501c043e981540c3d51042698018401418113840c0b002146c0c030700d24503003000c441d215016080240021551480c019020b81050b0140e540b0a61000041481c5d9040a1090364840c040fa00003e2440740d190860584206a01500032034050180550305411502d0030807c840714860300c000c0503180c11b450b1101420b0111440895a41080040e600c00c0c052240b00b0705887c001034102d004800c7c0e45030303203d14042c0c1d2446850f080003500004040100107540e110910101800f04070351040146001d0440080d04001102c22401404039079141c01043c1c0070b091581c050b024 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 731439964 1250 731438714 731438731
    0xd240b030f032508030a05010303030612081b030712030509060a0b100c06021317100903080c1c060803030a0e060106052205030a200d0b04060f0f0c0507051b0117 71
    0x65443d689810b111030340101c441c5201ca54941004000305607240c41144002d103002d0340300303090900b05996112040e02c91108581911011444500300c100e0303041c000c0b202d07083d40c0b081e415501071248400c058050941141e030520b440c041c01002440310007543c0a003203ca800010011603152034405010b0340c05200380d000594035282c0c00e102c040d10070015000d000004d4409503003004070200d0380814085c03411010108000c9503a0030041c0c07003000a40c00000160300f0403260110f0031741300c000c01140703000b106200f507080d03032011410b1202c005150a004401103024918a04040c03000c000d025503143e41d00c65081c0308441c00a6010040c80c3c000e1401c80c564030400301c40c0341d00681c50941d507410000f481d240307140d002038400301071540800420600c80c5c203125200e01c005640c01404800540c4504519401c01840544010b40381c4900404048080e800000c0388200c460003000780c1c04c10844020304a03080203404860500ca01e204404500c241890034a5103210160f40d440d2404044503a08804501c020b0440071 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 731441214 1250 731439964 731440027
    0x1180b07020309010f0f0e12102f0a020f01150e070c050c041104050301050f0f091906020a05070b10051306050d080c031e0715020309060a0b0d240b030f03 68
    0x71b120390703195248c647e0f44c403c01c0001400c0c080700d100050403c40710505d2880440e0b03818824000d004400754030f01140754080c1e103911652207001c480d200b40d0078450484800281c5500c0c1c00b002104550b1018041c02c15104111802140c035903a0320002e9640b007442c06405452940041c8a8446074a040c0d001402d0b505007019116080030b0ba540c000c6130955409480124048000c082000940c4e10715045031a80542001c00401c0711a520507010b582228404601800d04d40e00054801c0b9014000c0040381c0d001540002000c007a880c00d0214004184564085c05118074030303440c5ea160994015003c0d440075540700402801c407200c401e5844d410164041007215580d4041442000144c1211080c550500059540110341c0c1e0101031812260100c607200000c1402841402800300c3e400002400d1079001d01c40400c0080c85100c6500018030340103400000502c4d05425503140c0e07001018181d082c0117800007400d010700006445104140c1c8445074040402d400b588180414256030011003030100d501c001580840 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 731442464 1250 731441214 731441237
    0x141903121214040b1005181f0f0504050709080f0a050607030c021b21060a0b010305040f2604170f060601020a03180b070302010902030c220b040e01180b07020309010f0f 74
    0x11f0041042c04031403080031001c2508215000f803003904119075814501008540c0c031030404900c044408424000c02d402241c1d10340c00030781e65038000c041113009058400d0454409004200d41c069481d00e1105045032203004900103e103106000b8082c0d04c0b80c1000701c0d0050304040085003001d040c85035003000c81c2503104080b0000f8280b003001c1c0c0340480c404030000102401c00c0c3d00c3c042840d9402c0c0c1e403592003c681003528102c00c01001c61178405601c2e0144e64000c000000d0100780c10b04410039459080743c0346000349000140001c0714609002d1141f141e00000e015a440c0c90301000c500c54580c00b040318100c1c0076800504d0303c030b00000c3c89030040d001540210500c048003291101c1e101c0145420025085003d41e64a501c2c0200358501001030120300da00403034a2090020354941700300244407085121219a40d1940401e04e2540e6454008a40c50034100008000c2c8110301140c648807002d00c030311b0903a04658442d0101c2c2c03807140702008507a80c5200c107855103070b80392440c080101c4000365283c510700104449807519 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 731443714 1250 731442464 731442469
    0x3020d1a0702070e0f0415051003060204080d0801090c080f07050c070617090c130b030c090f010302090c0a05090f010c02092509050a141903121214040b1005 69
    0xc0364020070040d0300525405013401c01941c109070014010b5990303001ca1404000006d150700b01d200701182d84510021545440d41030904401d4000c0d900700030503650002c24045251600000c0c08500c281c55583c590005981e038401510072280b149410f0b0340050401c1d800503c0f0003607500b00c5903400c107005140141ca0041c002a4050030714445402940004103080d42c000002006078101e2074000f00400c025044040c00302001513016071045400803500b0b42c03201c4542d9243e81c0c05000150304420003600f15121131800c124180d8019009001c100e2050801a002c901190924000e44104428079240c0600d85107208003004110681521a107040000600365070b0010f0b2141c465160081c1703400b6120b8006941024142160522500891401c204a104040002c0e42d110366042086446c410100d54170f079034407a808203549810030700401940c9584018000204251107010f1003058000c0c2ea55001e142481c2c0025000f83c43d8180a08a0a00b80d00804140880d2030b5184281d00075000d04141c84a803980e9001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 731444964 1250 731443714 731443763
    0x216050f0307030e10022508070e041703150d081c1a01260a02120403170f060d020f040e0a0606030c0806070807110109140102090102210403020d 64
    0x816000307400108105003015004070b020018041c044a2041003d0301080000390f564200c06680d2045445c03041d042280c601d003540c2290050402a004e0b14145915a480020410300c1918104c800c1c02409016080002c80003060304d0107480356a080e4100d55081d54100701070007080410942d1710500422540b841000719950000000520440110341001080e0440030f00c01c0c1c522030558140580c0c8502c1080200800001103161424847c40c0440e545405151300028041c00d644940e156000005004c2410307008054050f02100e03c25a0415039582e81159480114060720b10380d80115103180d9100051400403640c42e507498010340000b0304000c00c41c02c03030341c031704449110180d650b2a03441c48103006006a085090000e80452401040d550400721001421201c00a0a040400c0221800460150801e4000300312150b080050004840c0d004070381c1a000b0b500c1610b9040c09407080c1002e9840440c09040f144080b07441038040c02d401e151643e0203210520000c1d081c21a0144d442c03072101e0000c14916407 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 731446214 1250 731444964 731444983
    0xd030306080d0305070906080709122f0d0206220305030d1a0f040c0201110f0706060803030108120c0a0b1e13080f0c010609230f0c0d09030e0411031f0e0604021605 72
    0x11611903081420100201c4106080004600004005d0107429215101e10203503400d826030589130551f46071180d055403035625090d0010144071039100c0c0e10020501c580040900f240c41229142000010203900d140d003070040c100001d80d0b4000c0b8282d5100c104910302a800151040301c94000840e90440d20307071600c44654010300d542400b242c008100764003481980d01c82d540c0940f07152801113145504000f41580d444840c051105500d81002503030000400b8140b040c0030383c880e40300005107240c1c1051001c0710340e01c10246008040e0380e07100710f002660410b0524a2802003030307040101d40f450040c0100003a49540d2111051441c9592200d02c0000c3d03080c454424403910710964121482d404403400001080c1c490007401c0305212001e2402807048041000045801c4103240c40800141001a0324003070b030f482d50034003440c1c0354007034608400c410102162000a40c49082051b040202400700c000c80b410000b4510301490264a01a400160302420142e000308a981d590010121600d503255407094540a002c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 731447464 1250 731446214 731446223
    0x60907051921151a07050d030f0b010e0a0501180f080709150e0a0b040f020309060708091504080a03060b0d240b0313030e0d030306080d030507090608070912 69
    0x1554800b12500501524a45100e62100c06001c0a0507012507030305140c207540252030100200e03064441d90102c0c10310813140402e83c003505540e1980d0610901400610400308604807c40c2040d1400a4640c801d03001c118600c000181000b826a0901c401101c121445a4018030b030140600e03000300712140384600c0c0100400d845030041145c03505108010040d6400c803a01b5003008501070f50140055070320510116441042420000f81c03940380c110003e00070304072059020949038400028400128070104d803c80c400d0449880346500740c4c41d042c2000ea5568a5030f0360942682c0940c01c04100000c0341a401000105031a16001c03032415216112049154014076030141d40c83d82c0c1d540c5c801c041c1030740e101c040c64804240c411003e034003d140c00112101071100170700d680000c103240d1001c00c1c2090300032411b41c400d0003009410841042c4507850050001e06140c02a01440d110b085c8081036070520a0003880d00c1803006584178110140f901000703440440d0050070090520101040c0403034030b140401c4603181c1542c0513 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 731448714 1250 731447464 731447477
    0x603230321090d02070e040602160204050a020c0609030c030a03150b13060801060c0f121413030c05030a11010c0c05060a030b0405090714130e030309010608060f07080609070519 78
    0x452010b1400f2603449403001035410070f000411044005101603944103421a0300581e66142d89460034132038014400d00258003034504070a010108809901a2141542c80c008580081c3c581c001100d541c0c1c0540501502e06602c100002c2c002240301e9040800181c05005c02d44228a44501103070106030007011401031400041d10040100c0d40d480804140140361504007c5407210940d00ca00161800040c0094002c004030640e00b40898807507030030034010701a40103415403a0100104200d54109152205541c20b0280c05c901050703519000c10758030032561b4022440b10055800c80015209039114050903101100d4101001840d0303115000281b00300d021036617002034074007034038000c110444101502c00c1d46070f548122014029101024042e024003181122010750440b646c0c10b00740098400000c18400d240130110511482003015004803064426007000e8400b15038580744440b24108048900c600042c0c0f00e4000319150381808604182c108240b8a04035141160320b4100504580941b00340000040a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 731449964 1250 731448714 731448721
    0x30303130c090608150a0c0f112a010e03010b1e120109030210060e0702070603020c01150b0c06010e0903091c0813150302070506180106080f0d030f0603230321 70
    0x9803554007584901b01d82400c105800240c3ca0042c0003020703d4100c41d0901001c100d881074100345c10000184420030307076200c1e0840c230900442d404c1580c80c0407400d01d50124884642180d45440c0c18080c0c00d0281001400100d040da43e1803082e418501101c8003031a411085c00d0000080c0c03107000380510ba1106010350014892042c401420004a4070164041c20000c00c5800511610707550209812003114110709d0f002d40c507491812070b01d42c01062901c040d40740200c10791100040d02840403000e420031026100603111180c0ea82c440c2c2d18034102044a41007002d070000c211519491070207048282d21a80c2441c00e0300ca4184081c0d494191546c098008a0803d0a00800400110305e000e020420290090b10301542440c01d1070307036100d9403802e01074540a00d906100c03a0360303210000254054802006d000085910003074401c00300a40f5a5050042032000a04010b10001409090b0082804130b9500406516482039508201c940401d0511004000d0740000c100550b0a04c0c1080d00c80140c1c0304105402d60b001e0704 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 731451214 1250 731449964 731449993
    0x6023717040e0618040822080a050a05010507230f120109050906091f091e1b140d0b10030b0702031c200708040b0f220302030303130c090608 62
    0x120410741c0d11520114130030000002d03c2c9a05891150604c0c4400082c0303040d5141005800250355080907819204401c42002070000010350500c00390f0244008104a880e00c031022035001c0c0d6800590001c20030345951404012003140300a041c3c44e040c3d0f5100500700400c0120030520001e00780c0c0160080b42e122018451910000d024640d0007046103030003850382c1600d04202c9281983c00310f800404040d500c00f0303400140005d503400d08080049110748050017089900d0b0600342d0848404516520744074114000c211288242c0b0400c1103c0360090104002800f181c2e140004424010b02c6041455050200080021030400c3e09500800444e005152650354092444020903507900c0d003800c0c0030381041007507484002003041443d00408004c52182d070780c03070743c40c11314002c0d40c0700c3c59211094100c00001e6140c101d4100402030300e035408005070220716888105610804140440c000030358150801c01c013003003c9600741c9a0300509648a030150503012503488044000711003560f030012903180c200c66005490031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 731452464 1250 731451214 731451229
    0xd0203100602100b0913020a09020c07030b1b1e0d060f060e0612010303080916120309060305150f010c083c071704120c06023717040e06 60
    0x3083c265904025250000c00000d0139010081c00c26096281c0c1e0100440c1551900403101c0042c000e5988159a9200014911941c9545c288001d40701d0543c040081407000c41080c00ba1003040501080260901d140c5000108180c0c100c0d05201d1000748040201c0d000104242c0140001021600d040800c60b91424501809800606500c507108031420080e02c1a0041c152603442d041d00e4051a2209065807164806890030f03005410315558403c034101c00092000c108401c02e50001e01c00c2d036510001030355a10095050722802d0321703004030382d40d0030b080d102030b5500b00144001210101403510000c003510f69141d02080741d2000c031440400e0209860f2440e510150a40100b6010406000000c95002e0411821070a130291100c000c1c01200c4180c80602d0303404225085d070b40507107940030a644802026151225080041d03104e0900940510070464103400302500c2c4002800c9074840c0d40320402400144d081c030300714070300c00710443d00029280b41c882a00c405001c0500043c001505c20900740c0c0c105101000b130007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 731453714 1250 731452464 731452483
    0x706080f0411043306050406050f031e0906091506060306010f14210105010203210a06030614091002131802040e0108030d15031a27030904060e040c0512030d0203100602 74
    0x5006d0204401c101c07180d400011a282000d103202d015450f07455941c490b8401030401e0140706d204586074010721a901c07001041075030107503501d007084409403003985001511404048039225807081e02800010415406210031241b070101d0b52a0480150b869405001016080b00e1b24241110003407004920a80800046a5002d080240020341c1041079a0200098001c1c030386100c28451001500402c1c4807040326041175018540c0f004090058483c40c006000c15010203d0300180c143c49503001c1100381301030520880ea03495403e4214124100e00700100c450305d603004401e10391902a8200800221488800d140300e0181c04c041c00590356a0310100b982006a401500d41c00d06031003c810720070000900042c096203802c1c40f142c12600190b07501c00104107002c0a1003403480e001200100c8007102e102c80044010310010b142201c04112094580020741f540703c10445008104c001ea1000178805460b0010041d46030140b128116032606002450620607a041982e28a208814048040c4551a011311402e0791 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 731454964 1250 731453714 731453717
    0x40e030702030601231f081312050a0e0d1412030f0a0b0f0d050106230303030105010c0c15090512010b150c0109051203090706080f0411043306 63
    0x2084441e8000a0300c41206124819112080000b01c4d2102d9850040254440e280140f468224403815140398003044000c0c1030a100050000c40003801d0000242e000764601c582100b05102031204c6840260380315444815a20107102100c409a05aa5108941181d91a1207500d6000448045102e080e190541c2e20542c81d0204000744100854051003410080d48094404404500b400c4810701040f210340c2440080c03500016944060811b201054000d401180e041b50980d460701c0d0101c02504410780108044694150002c000401131980b190070312201d202c4c00342000c1580c03039a40d002c00c00b01c04880e00d0910404607100034410807040c50b11680070100340031000000d005d5503081030000b4607082d00d2505c001c40035040209282080410941c44104001ea00c4011111151500c02030104682c20407a40880c0b00d12964030041607141c450310ba0385008011824070a40661125600c00060b8285c003500341d40c005549010400032848503019542d00a8417003204141c00c0b00c0c0101010701d04000302e0700a0390 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 731456214 1250 731454964 731454967
    0x1a010e120c0d030c060c091a070c0302130204080609070303030f2c03041e030c05040c050f090d080301180e0f070512011104030311060a05190509010f020c0705040e03 73
    0x180c12103010070915010031049030303001850b050500d426660404841c6010380040c0ca040d020b108015001004030b07059910781d80081c6603140700100c2d80503080c800c440e4000c1034081d1644041006044c0103001003000da10710b4030058202526841050f140c66002c179400d00040d84144010024580c151182d98a0b0b28100e050038800a21801000e94030041f01c24040048200707443c014032800c000034402c0e00e02a00b07a19403180744d001600c0b031440c0101c0010340400d41d007103280840c0000f403a02d07280c455108078081580b55070341081e05000c2100b039690022011a03070070402e00840d0300002041c0d8002180681040700e0010310745c202c18000142101c940c0c500e04029035004904402504000203041022a60110746102040d05440c61842c058484582c20812031040890b0101c01c041e0411000700c52252074604079402d075524000503a050b00e00c10b4030600b400c03080399089002003d02d00d400459102a48500205207082e4540300c900c22a849003e155546401440d003c0c001f904d424000c001e007103800c190046 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 731457464 1250 731456214 731456239
    0xb0a05040b150f0603070c0218040c0b0a1704060617060c1602030709181704210204090506010603020d0e060f07080417070c030c0b2b0b041a010e 64
    0x1000c03a520081d26030350359514040020b09840d50781140c151105000035207490307120f00740082c02902d480e9030310400320302ca044190042417400400151085c822904841050055454003140b5146603226031010700c1000700d4050507886858001d0ba200780a248031b5040042d00900e0880401040e10b001c0684c12103a030811010b024040106038281c600b28070101a11020001e07451000902c0c0410341c0d481070050b2824031410708003e4500420f150b00403801044048207c42601e2070341141071040b4044c07140d4518287c1c45061030604822009401070748003402c00104c107609500c61900e0140c099210900007600081c3d0200c4660f0703076020b0310b241020a00010062410f0507094841000c000500210070401d0200014050001c4140c0504a2118003c07440e5a00e0009041c4070f042401540020349070b0a01075000060021030110032140006120300400c120106104c040700c402c03240c4050481107051f01d07a031120038240d680e80b0803080b5035a02c0c4440c80c0704d1609100005801e069074212442e10803104003059 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 731458714 1250 731457464 731457473
    0x1110a08030709080c0d110a08100207020f0619051e030a090309091811031903021b0a0b0d112712010507081f0e070e0406081c030203060d140303040b0a0504 69
    0x106c12016841780c1e41e021000d8201010605111311540411400d100386180c100c4000210342c01007403a02d000750303581c0184d5040141402807511500d004c0803a10151007140030201d0f0b01c03030805064a401c1b44000c41c640d00100c9152013110f0b42094031901c006036942d107260410181c0185c10100240f941400c00d104100321204c80c11282540320300c001d050070390891041101941c09108446030600107000e030b040f140c8900e0400039039034180006003060034400d41c004101036150003800c200840390603140742c5203000003008444000c0c000b01e42c44512090780502c204011321180910100441004000012250004400701f101c26690440b2821850349080107100c4e41c10b5009540c41e0348201d2000035000014032842188a0f0300070503078422800d410080060029455101c0c0001c90212403ca13001d20102e40c440d0280c6031500c6540c6001e02588111f42e011104650194024640c8414020000d05000f00309441c0c2040082d402e40301010603420000030401044804192290040d5071240208020302d4a80d90303 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 731459964 1250 731458714 731458729
    0x20c090412170115120b0901080313050405040c060e0103060801060803070b0f071e020a0609030903060c03052401110a03020a0c06080108031215131d01090b070e01110a08030709080c 80
    0x500c08000c81d402d03004034145c01c681c01c411001c00e00a0001c981960f50386100513180e41043c1400a008284100f002400d03180602030f590003150403190070001d00c4c0c030304401039a00300d84030103c150505449030f10004038a4000e1180d0f400034001007011396650000e0386440c0600c240e000f0100c42c0340d0346645082c40303c2c4541c03020000c0c8070b00052a00034000040084410303032400e00001c000900c1103003844840310030541e004503070701c080b01d01c01d4106100030034001c502541175800888d0907018080c01160801d4004001000c0745030100e1040c101041000ea040f43c0f010304101d19208298056408020610304110003064040010015840c0c620030650500b0800d6403a441043c14001141c0403110106980719460603000403ca04020641400305020300240c80c094683c0d050302c03038100c0101e40440c0f10240e5040c01480105580718142020030341d2010000d690a0b0122403000341000b120680c21140e50508000103c5920300618440da120b00c0c140b04000c041c070105402440464008a45000705038440300c5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 731461214 1250 731459964 731459999
    0xc0311120402012304090219030513020f060d050a0207020306071805010c0827090c0405090112060b0d0308090705060c0a0b0a02091e19180507020c0904121701 70
    0x2900d4106a490510100c0001200c440d9131100c5010004000852841c107500402e5000e00031100140102d40c401d000b80d0458004407001d240001d0240202c400502e071661840c10340d540002d1019051074a0304004000321a07007159241112540007403100e0540c0740400c0040c0e4440003620701480c1988648420420030310241c404c2c14140f0044404040410440310181e41483d203591140025802407407480360030300b80200704840c1c003030004200482ca800003180111400e0311310107400c004071a403900e04800f0f80c0400d04101603501ea40c1c0c42143c401c0d11b660380c1208440c01e5009507101d0045091110701241080f0442d40000d100310010000102450b90105040901036080440c140d00f582d586d591400191140c080401d9021305d44103401c0e44414085074880161400c1a110600d10000464000910700c41034010143c02c1e00c0180c00300640c0c12480c3e007107268026400d1043d660b810b003002011804c20a0180c8003204c0d80d006142c1e8090140e03510880c40b0054525196058815500d040c0d034107001c100510 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 731462464 1250 731461214 731461217
    0xc0313051f051c0605090403080703060905060a0b0d020c0109030c110303090f040e0a0c150806030607210209150403020102150c180a030b100810020403020906060d0b090a0c031112040201 82
    0x4403d101d0b203542c1d5078400001410040c0c102da0f000d14241c034008124640403070382e04002c41d05c0c181e004145014284500d512404010303106000080c140515400c491b0041c03d8801c0c0056020002c007184001c082c02441c00c150b01c203440d041d100c2d03121454841c030230180141c1d46a00950040c0441c00c2140c0c0c40c1c1405031083c1400f5140001c201021140035814080d00e200083d010503880107002641c03120380341003c11302d0846507980420760380318101010345906d07054500c1c07000146514903881c201203d0310705203a02680c1805c00145044c81a00200c2c41c0c5424080c5242c030012008901001556014401c40310a8400343c15151041c3c500108240d18900400d13003907402c01c89003800d1300540b98a8403940000a59004141902180f4000400c05d1030300d0f0003030244051501a40061420080181c0240c809070ba41c0185240240d6564500b40981034002103400d444a80e00d45881d0101c1e81c80300301d5228002c90503164085002d10681501409075103078802860303030040301001180e1141d180720300070350f4000307509 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 731463714 1250 731462464 731462497
    0xf0102090a09140c0f07060507050a020706030e0d0822080d0612031d030109050f0303090f0601061e14070c06080c0c07090c03110409060609050109060f0809030c0313051f05 76
    0x802400c5e040030b0183d50303c01040b00d45010700b032180d402d8104002c1c0440c21103d42c00c40d02c440751101070840c10354503220820050303a1300c014080e0042d14010b406055200525140b20040f803a8990410071846d0804001a01c00c3c01001490800350146402000043c0c0b1000280c50300c110350703d5174000c00e1200340c1c2c4c0d03036500044a0790800358056034003904552040c0d03821008484820b58520704540d101d42c81500d2100c00740c40f41c10301c980626500401d06904030345e21354179507180d606864415088044140e2484008000402101900107028100a00042030245000460403401e049001e442c40740047e0070f14050800c2403050020b825070010300b00c002c5d5402400c02007400001440103030040e103801c42e008040e1590115004c02c0c04170843d4400c0c021505595102042c3c1641c131001507403c030070a40a03000000701c03c0c0e01488070090181a6803a004214041100c1c9080851206507040d5040f81c055180002e00b050820070091402d0004818414225030303442000c0600341d90041e1081c030030481c2d200da46074070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 731464964 1250 731463714 731463727
    0x2a06050304060f0f090c0e0105040e100203071b050a051b0f040e0102160b0f0105010e0607020d052a190f0509180a06050a053904080f0102090a09140c 66
    0xd2941010707005260744c400500c46142e072898041d1a520042c0692551f0aa02000010303262800b405402602814030000e030064074003065600000c1d600c000c00e03041c00d20140485000280312615613101106006401500803003015162880c00c0802103c8a0140c04504034400801c0c0d0381d404424814089081350700207100c0010841a5000e03000b40302d128034400f100552001d051090801d0084d210310045003c0707008036a2500e005554035003401c94960781016051240710018284104684a0580101c0444400038840c510f040d00e010922001e4000c04116900c52508605160920700140c2c40d410307851244050804002010314441e91055610a52880002c22440380b21243c419200062070781c1a40c1c0e040400382044000f40c00c0035200103604c0c1e0328040000c0c0c80036403140000621101003400f00c000841c51691480c02c00e024003190507000c0001040005183d803020420784080703c90500001da01c4101c100d040040a08490303000e801418140340d50342c41700c100d52400065011006451040c1c03a0301 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 731466214 1250 731464964 731464991
    0xd242f0307110f030a09030528080304051009060605040b011b0809010513090207020a0509060a1a0f0313020a0b04031e0303021605060609061002060109050c0702030a2a0605030406 79
    0x3070030781d4400004e01000030306440c01644690310b80d05881c060801c03200503407103101007451422000911400060340f810504000102c54400071a0001c0c0520100c0d55107440c1d10343e0130411542c41d40c008032011541c49000f0402410a4094481c80e0780090901101c0ca07024410381c0140410700c4040141b210b600028440c0302031303001c1d40640c1c04500e600f2081e40c0c45c0c1c1d0740b501d64280c025401a0426031045008860004d03040c078046030144d00c50b1001914452110745021241c0c0c1410100d05c0c08000a2641030008442c0301403420302552007103416000820100b9078500508c15250910f422001016004020074008180500c1d03d20910758209000d42c0c0c00001242002c034020700a801044000480e490410800c0c040000780450080300c007191307207514903160441041143c0d06d610580a015030811001040408081e51002c0c3d440a00300300300f1413030b06446600103410503002ea10b0803100112000c448000d0102e13401405070b4000310003410400800d04020015003a800000c01c003c0285843e00285584d01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 731467464 1250 731466214 731466223
    0x9010605032e1d06040c090908120405010204122d0206180a0b03090d110712020d020a0503030418050906071707110d0302040302010e0301060b07020d242f030711 71
    0x20040c001014803030070443c0e10070303030f84815060794103580e102e50b0750700040b41c04221485807003404c580c0400d41c6481d200d01e461400c10381901c02441500c40d55800e200005900c1440309400e0748044c440d0542812030081c1184260440010745000c0c1d143c001c1e1202c0c44801602c40308120350315000c4050024201e5107180b800150340b4559500103181d05240401032001e620800150030101c0b240c0703070302c551451881060740c0b01d60b00e5115104002c43c4100d118240400360501480c080d8525002030850500507444402080c6194810741c000c90041c5411122002c02d52201d00c82c1907000740c9080301a0401d0308140f00300508a03039400f00b1003c5502d00501c04100c555001e1803403050700020b2101a07800030081c644c80070f402500141301c10b03800309401d008100c00a00d8117201d00b0042c0c50140340d1080c2485020340030712807044403034402101d8a03185840c004100c0d00d000c80c00d2180002030380c0390201c0c3c2111fa003a00d0058040030030011880da182110a2508080c507204196a03001c2c2640c42c0c040030200c01d644050b0f240 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 731468714 1250 731467464 731467481
    0x9200915090d212c03030405040c080603100b0303040501030b0d060f0e1014161809060513140612070e0103050601050102120f07030e011403070809010605032e 70
    0x36162046941c01c00080c040d152985000e28003016181c0c8400700c0d004d5641c16054140c040e80a214403411518000e01300c1400c01c000c25000e0112418a074990004c1012181c0c005805c2000c15100d43c100600d41c82d08000031031400050800c107010980008021075920302a50003110b05154940c0c200c803032551500741c0105421604850280686e010004081c401024251415005402030148002042ca050300030766400071b91340380101c45250b807400c0341c0d40042661068680300f080140e121078100864012405405403003a020001307517591525040003903200407401001123581c20005080000c5c00ca40c81d941c2d5024000f540d110b0f1105401000c0d181c10700c103140d000f090400900b8030001c4103210000418a06850080c1c080b40d4410340048aa07200c1ca000b4040c4c1052040c504000c010700091007142e5021441106041c034803a20031100714041002d0700308031020760000f0011006c011420509006000007044194040c0411030f0044c8588900f00058100002480b00c14409000c40d80005501c610b61 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 731469964 1250 731468714 731468719
    0x120c09020a052a0601140108040b090a05070906090c0309020105030412050c0a0b040501050c0369100506030c12071724090a0b030102130920091509 65
    0x851110307002551031100d55a4165060520134140045130b41c00031042000d1410304142c46200c1d142d55560340b5144070903802441041c1c5805401c51500000341c08018480280406030740124a5a00b824602070407038090039030300710406041a04503000350f604038007100c0c0c020303820401d0701d0100541600203071203900c5000d068802c60b01c038081c1210300380b003811210940203500c600d0080c4800d440d00d4100c8083c034003059072401c048040c0d61907030f07001e1561050024008006440c80000844498a601511801d811000d030442035400d1034480007a070101c0481c0408c041203020030410141800801000c0300c038998080c00f80501400800b140d000f1480b1015181a000d85110010b85e80c50201401401c20703a022450400d542a1903000c500c15003416000c00020b54080b91035805c07400101002c20030f051380017074004e8041c03a07607560214245850030300060206403000c1c0100c0003c0c524107100c04048031119018131400741c00f00350302c2c020281da44008480d0b000500b1140c1220b2802003002030040c41c03044820071903 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 731471214 1250 731469964 731469997
    0x804081305031f0f0501030c27020d0e0d020708061f120807210c020409060e01062411033a05010e0a1404020108090717070f120c09020a05 61
    0x42d858000c44910700b41140c140f0106020014607120020180c610a01000f043c0d004030307040c184061a440000e22200c2400320900110100c4e07404402402ca81c00042d9990410341ca0309a0b240310312204104155075007200d03200a00190b8902240ea640ba03a4001d0a144007051a801d58428040060401c00000d05940404400c2da0b10700c911b0400f000b0350080c481182c0110310342481051010000d90f00c0e507050302240d11034a100582d55401c10006140400c1d0884407075686403440e0a403080244240d42c003038505400c00c0c0f0000c0504402c3c0030000c4d09007039203907003c0285e170149008413000044180c1d85140c0e604542c01800300d046415005035592104402e003281c440000c40305041b130f8400d07013055040752920740c1131041035100c00c0010011344002c00f0441e245500410003040065121350400e0750f21580d080c041e10050307078958401a00304800c4641d0f1415651001030180024007800f8a1200101078000120f1445410356a030b0300040c1c1024481c0064032640403c09402680c003860483d0b105038500340d00031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 731472464 1250 731471214 731471233
    0x916080115050a060503010303031d010507030c0810081b150f090a0b040b0304022806030510081906020f0d020c010f0f06050d060e0c0907020708060f010303080408130503 75
    0x1500802251010742000800d0600000d03503420080c51500945502da0b513030030314581c03c6403401d0b405460000171903c085010b4408039400690284130392805244a642d001c036900e00d03030950090180e007018105c141c580b031542c1e1040054207000602d00b0150707a08402c940c60f80c90840000141c070780f1620782500c19089030000d00c903000d0040d46802045002000c44110000d5a102d544200142c01a40135212440104002180141c80d242c40380c2e00390b230044400030f8450310a06108120020300a6840440030a4a84050220f01c0766000340900240ca503000040ca243ea840440d4000f820314949000f5141c0c0d40d0002d41a080d925980341210303000650341005543e941c808030b548a00134032515a0f06230034140b40c04a4104180503901544c2d040b00c0340200351102c1e0302590346540f4010260365088040610442050800d140c4486180070b00c42c003203035005807a840e03250890403420098000c1c50740480d10811001407001130380040c2102c0c7c009130881035490b141d010301c40701d0303801a07129600140d17454403486401 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 731473714 1250 731472464 731472479
    0x2040903090305070f0b1218071806050f030d0c0503091804020405070e06180103020706060e040c090603080d05182b0903020315091608030904110909010e0916 70
    0x9a003203c0c40b03038044450081e0742d4404110b1400c0c42c0d01075517202c9081046041a100018100141c00095603409094989078540120b031521001741d1280c00e480e103a0400c003102e1081d0903c2480d000340410703a1090030b15180c61300065103413255030410a05014021824105100d000c105440c01e00c10040d0005040000c000e10410a2210440d01244038504000000d00e6041c841e24080f8244180a01940e0800d18102c52001480602c0c04c1c0301c5040507428041c003400f0412500a03000100f4045800c401181810304201281640c0740d00116006410304000b0000142c0d2107003114480075a01d40006415150103562400141c41c2c443c1078540c034420043d007070040202c5101c11000452110004481c5034840260950320900d003440003a51640045041011300c1d08440304070340d44007150310103031031801c1c1410020720b042820f2504018402d600102d814205410300748544503080e004840c80c80e0800040038006020110140180c444090382d540202da01000c00b0810f907900d40d08985d41542482c0d4a0340e01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 731474820 1106 731473714 731473727
    0x705060a030905032d0301060206010e04080403080307030c0908010c02100e0f03180306070512040212070b0f190c021e061b030d05010b0913090203010902040903 71
    0x248180000e00c240020514507801040d420a200d104c517008403c8603010003a1000244010001404002d8000a01504464040106078015501c03460a050140203551005000b2007020085c850300d80c0e0103421082004c4a2640d98042d195514a4000e007602c1103104040c000d40c1040031702d1a0150301580101444046440c11124000d06041c001450740c2d21106c02003410901903890440350b03140a10006410514618001d401c00c1c48007102d0125504010b00000c0c4a0920b201c0120005001404414007c000191442c0d4682000106024035580280500544070015071401c0010601a08035409210713006000c51212404200e214800c1c1d200c0d4000055100f07070244900c0f1458403007011100032644851000d1030f221219201810162541038001e01d0003c00d0502040c600364644002172120810356500116110401d0300119004080415020750014148581c00f014180c1100303 = true := by decide +kernel

theorem cover : BRFrame.Cov 731294964 731474820 := by
  have h0 := BRFrame.cov_init 731294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 731294964 ≤ n) (h2 : n < 731474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
