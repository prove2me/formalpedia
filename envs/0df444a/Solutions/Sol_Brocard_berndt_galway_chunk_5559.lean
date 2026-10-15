-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5559
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:15:49.582024+00:00
-- url     : https://prove2.me/submissions/a7ad9fb5-4269-4274-b4b0-2490486b84ff

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 999640287 ≤ n < 999820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 999641537 1250 999640287 999640289
    0xe010603060e0a0e0a0602161103010902030303040210020c1528080c070309080d0809071d190b0904060203160908070504020c03040f0b0a0e0108040b061c060614011107 74
    0x30150181c0d007a00c0c0d0f0b840c40300040c4440400d6003024094140020b0002c1d000d8001481c48841040365242c40c04400d0a00480c90042040c00700e200341c0c541307801040180c4010094990150301205c2c0251031044203002a81800c1000000a0b840b170314074000c50310310042820103800e0304003255401018103214036264040c000304806802e404902040001703112491014014400700b4400d11340000c01030380d00d01e91280783c507010040820102c0d92890400c40d40c00ca007001010020700340c120400b4007802c4011414000140007074241c46042101c0081d045100380141c00c401c441c190041c0480c2c84074a86820f00000035002035441c002c1c03111032182440e10840c0301b02102420344003140060401ca034076010400001394040040c1c05514007080c400050701e64420a00b030001085988d0049a40700c0000c1c10040107035030064501070600109001340404149034030760079980982c042c0c481c2c10304409042d4109007150322116006200a080140201d0f0160a080210f12002000e8071039040381d158031540c482e1101b481d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 999642787 1250 999641537 999641549
    0x506240307031209030501140108011401060e09041406040b07020d020d0203040e071b0524043c030c2d0b061c05030a12051003020402071403130e01060306 68
    0x10440301071001ca10100d074a58040030705404c03d58140e50392995400c0c02d50b55102a01032001400b0b4004000d072001c2030042140401c000e5544048560401e44050b0207442c001d4241030240c4000d0b00010100407090015054115400c0121207003413910b880c280481942c11108040140140ca2000301d0340c60001076042c60705912900554103141c10000140c4d4a0040145003200300826207881d40540700c060608003580c00e000e1030280001000040c65180d569a81420f01e20b55000c2050400011903903000461f90300e400c01c2c41d4060364901d101c90f5020405900e6400e0b000b040f1134480b0951040513080142c0d416200d01c207002034541c55640070342d4026803110803207151003200c5610154200080c1004101c80e80b0010090070096030702d5400c0c1800c0807400044004a0717255000141821b240382d00b001c1c600d082c20941c1c180034040c03444d01e10400034031221140f10090142c0c0c0c02240880c100403101c000c010240000c01d003120780301c0b1450701520181c0701c500d1141d0382c0301e20110300c001304015100e40103241c1680c0d1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 999644037 1250 999642787 999642793
    0x1802090a05090429010807140d0605130314040f09091b090603020405060312030402011803150e0c0d110607050a060f050f0109020a020606010e0303070606240c0c030224030405062403 80
    0x403408c4090b00201d04564450340c1e000021820200000340d4a108880c040c400307002980c8024180c0f0719015282250781c10100340d203c0ca00f44810890441660350300d000340c80d81480e0128000c48549042c00d050350f2a03c2a0044d1140e003080041846000b0394000811207000702c0f0180034039282c01c01030684440b41c4c1024090170031000c000080140d40a81642a00d00d0400e0a16800c05642d079240c0301844400044408003086d100c168100b01c055040014046080003151004000310701503036600381e460503040c01301d4010b01020070602c0c14840140040005550042018017820700c02040120007000120b9401000100c1c00380086041c100d00d1080c2c5030180d0145c2c0040949443e01d00054a15540c818050340e03052104111034000103145000b944010411341c00715070301c030340c45040445d912007600c0100d00c8200402d50040d04007282041000070101c82c2c060350a0101c20728190382d0a40a11038540071844010800000c1c4800c00c1000655184103076034129200c00c404102490100040d0600d221850741a8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 999645287 1250 999644037 999644039
    0x1803080901180e0703020706230106030515130902010908031804020702062808070f021218031c02070e041505191805161802090a05090429010807 64
    0x940503020a10782030301d070009140e42d40d0382d441480020b440c1044a004c00001d40124104040108602402c04401c0d0801000c01259403044058858900c05108000030903441e080410390380c240205c200000c162010b003503161540d400315103070070281c150580c00f24000b81c4007900000c0c2150000c42507621100011018442a5001d202000040d4100340c4069030710030402c02c004901d4024071102144114050030a541058007000806001603a00070312040502007801000c05000c0d90118400d4211400c00c10259252140e014a501e5144c00c19400300d0341600c900c1c6004587c03170501c502c01c0035070704056a085440701500c03044480c0001c001940d00400c03040c4203d0651141074501d4000f03550056028082444060544800006888417080d16280c5c28003014200e0051110070b00c1103504400400e034882d00520f1406048152019081c1c5026001c558003080480f00d9584800707482c8002d0800402009d50f074285810b2000000c191189503400030855412041d090354064010310b1304132940034014210413 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 999646537 1250 999645287 999645289
    0xe0f1c2f0306190b0d030c05010f020903030706150b1b1903050406050304052e06140105030f0c0c07030320070305070504090c0317070210030506030615120f0d18030809 74
    0xc450581010303000ea4540c10b111300c1c1900c404400484280c003960310714105003051f0501500312038030043e0359811280100724005183d10004112151198060000210f200d5140d50343c1c02c2a418941180406860001e0700b006078030903151029501400b0344040e58102c48400011050260b50310a0081c04280180300811650380910040c0d980a40140281c900e000080394429203440703106070065070589440c0c1d0050f2000702107849482c01030100c846000c0013030002040003802a0000510070559840400e0004400210f48025140c2c640301078030807104507503102e113000b8001d1300fa110f0409a1035101c208000b18010000078000c01101c0d003050240206505000511016290f00201612961180e0b40700000090300359103880c1d111560b1950036500c40c1520310400030f03d2440c0d001d8000030103040c1014801780390b82c082045504204c44604002c1c8050007a000b050400c002140301080c00e0099141c00303101340401140c28444a00b481da5283d91041d010004855100781901001c0e05081c3e040c003012a003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 999647787 1250 999646537 999646561
    0x108060415052509080c010e1e03210a0e090622200c07120c2615010e18150a0b1009090506100e0f1c2f0306 48
    0x440020700f035110400c500070903008040c6860f601e6000102c1030541040705200510030b40ea18002c0c246402d5041000c1040025601c540855120800303041e18003010410365010441c5404010780205540c1003000c1805034a03501c0d8005410541c08550340138980405403401c2040356202e103200801840c40040c0c40105094081c48000f030403400190307210300340904010b01d892102070082002c80169501c40e02c844947e07081088980c0134003101081800c81c076000524448070601030300c10300425088400d01c0d41030240f000319100607041c2000c0c010724000d00810910700d904541607075103844088501e91620b14030b504100c2ea180c051310402e608110315000000909800143e001f4204000c080360440c0c000000803030740e201a01c191008150f4446081000c8034072409115401041180d04032403c01c1c2d4400302500c00002d501c855032080c03140c000c0c81e41c116614480388914603c1300074800001c07900300b0324118140000b40d45050009921001d2484c1c0c20203010110080040400780140c06180c68004107522 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 999649037 1250 999647787 999647791
    0x231e0d0f0c050d0c1509120f030c061404060c0216350f0f0102090a0303050a03110f0702180601021f09120e10020622050c09070e09010806041505 64
    0x1c0c2055664400215580c4480521110324001c0c05001e580b00d01c0c0c2041d65800d4a2660310304c40038000c044104004422180d00b2081e4003e420581707500c4003010500d002c40300f8000411008140720714000401c2c0e541485202d081e0311a0348070340b20804c4640f40046040e6910b510300c884a07004034002803c144451b50049214024506440586207000311040341e007400c580313a200a0310070391548055949803000904005541c002d844100086143c00302e80e802241c44014240005410b0100004550080b10b100c2d5100a0107525548003140c1c5406600d610031401d80d00070070080c0c2c17254005d0007462001981d80341c1349501801d8140c0040c8110f00203812084801036503140e044414681e50014900458030007002d40000c281555203441841040c40c0030842c43d003041151a80031940034000304080f81001c800c142900881d4116a0101d490340f81c03401ca4502613441040907044281c0f0410300018a40103490740f444200102d4918016a03210341c8140d5860740d00701c401918a0b5226a800d01c0e030340106038800c503 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 999650287 1250 999649037 999649043
    0x2f030c0a020f0d0f02160b030c1c1103091608150711030c070e01090e072d0306090b0609100905040f0605090601030302011a03120a0306231e0d0f 64
    0x300c00c06202c82015041c10a06107044000c160038a00300c400c010380c1400700c00c4900407041d5110060904041821070390703000c001d0120701e6031301e80000c0f414020700e070f00129100d14a4001006000807581c1403d14085600169010301507482120b080d00c03d0700c0b079000c4c40c0000b80e800c00c6004150002140085503c541000f0f00454207001034002e40030b640071018402441421707084801420f00c14601000305007000d405a0000302c0480c50804611030480b80031444504031a80d402d0103482c84031012550131040c00348544080036a0041800000400180743c202e0f1406902400100080e65109000c0c4070300d0400444400c030001900d01d005000c001c10640c46a40c129000d5098081540c0c0c440e5243c03400c41f2820380c0d03854a154003071001042095824080e09121514400078000c00381112000b095450740400c24001e00d005020a0b058180380c400d600010003480e4103020b0010080840b0341c2d0b205103903a1810954000e01d04072200390308041030441c810150700d074060042e80355032401c0c0d181e01000c005404022 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 999651537 1250 999650287 999650293
    0xa020d0b100e16200a0308101502060f010f061403071715040b040204050109032406150e0a0e06091008010c050c01050603070e010b0717030a2f030c0a02 67
    0x1c682e98480e144902d20a11404003940030041240f43c0140440d81e003c100d0300240040001c818084400106080108a41c035042050031600d40f10b142c0f0006507260707040f240c1050503614000e940c6943c000785060083c4d02c0514012074598840f00d81d40c00c6002680100000b0408260b5260440b030380072001581e00c10998540004103881002e0042c240000c241c8401c0710100c01c10300c26260b02c0c40c2130310418848a4089030110b14040c50b040000e810801144400742c45240003a40400034014400c21000407024506000c004260f220514240038004051100c17002400d545c00030344160410151820030f55550780b104030785c6c0f640c4031010041c1302e520040292801100400c00091808000d0240503180142a00e0b45502d070709a80760b0032800c480c00100114030950081004014600c0021451415500d0b2100116610b00303071410807078011002600300c05540540041040102091071740728050030314000403401d03d10b00b02609600020030308160035540c00d120800101c1e04030784405009014404aa00503 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 999652787 1250 999651537 999651539
    0xc0c070801090b0106030b010c020f061b06091e0303071e0e03060c300a11120c09040507030b100e0f0a1409010608011d04030e121c020a020d0b10 64
    0x141401c1d10800b200c11100c51007220014400f00360140501508200c0070320307007601c0c41d00c1141c00140001400c5040380d03004820001d8021001c101c80580342144101c200d040300d506c0d04000c001c43c0d580d1500200300c4c038082c2481c1030711040c004101104480c0144240d80d44d854880703004502d2226040d03280c1107001c0501c00c21201502483c0c0b01440700b1441040603291803030301d8102031070b104517420b5003a402030b00e00c031044100c0001844400c405000d402c1506403500094001241c00340960f00d224007400c0d918a20104c104020711052000b000340361981d01514140080d4440c0c1c081501906d04520344140c0c00114010060703602d03442181214001c0c1ca00514145402c018040829084021500100c042c414445410201400d0411415004100c00d2400c21842e40c9030140000c0d2031111864203030030421074200401c0c00d061141e26a14030560004082060703000d4808105546c84844198440403859800c0360011940c0c0045031002016401422250445174156103190b114103005007003101070810088 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 999654037 1250 999652787 999652799
    0x7170109052509050a050a0b0706021b0714010e10081306060f0b090a06050a0801170a0c090b01110d30061206050105220b130219140906030c0c07 64
    0xc0d02c4000318501c1d803600607506041c002031102020705600014054a00000c04110f0410143c045401140d0818070050b01c03046810342c0d9400b035a0010070701c40c0151141e44e00105140d11981e0b85062074000c240c032003a14810007502403142403251242804080362140c40001c0401c4001c603d21060144102c03000034115444402c2c8420707150040d080401d1a00011a81050300d0070700000f0040070f008141081410008600700042011805004941c0490074003200b24010100c03c004940c0f1059202c84c0d4031140d1a2103182c140000c040118543d40054821070740140783e50008190714880314415941c112941c0b1000340c00c01071001c0e080c052100e40011040fa403908103401c80c415440580100048260441981d080c440b0a40354181c1290b0322840d07040701c02c0c03820104444001e89150038401e07000700324031100900190784490140c0240c129907000040c8050341c4400c022400d54032000036102c0806c50b90120250f000c15003d240400e5400420070004540303407a180e00040c0c0303102c4120000b141c003880c2d1191 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 999655287 1250 999654037 999654091
    0x60118150e0d0c0605070302030715140a0504020f190e1303110303060a090c03021905030a060b16020f0d0807061d06071403060307051c02090717010905 67
    0x9404120160445000300d0540d03980403485056010040301c010104a109840b002501002842501e0a000c00014070b03104040c0280242e407003968200c0c810b00308280c1e003a14540090040c0c1b100510f562410040054207100440c4034843c01203401500741d051406802c0288440b0070420a0024607030015044000f820202821001b0320a07090040e6a80c0c0c1001c240c90060b01c004000803184140f500280100f145645800350028102d070f04a14011402108042c01a0001e11030b5440058524544003680c1c42c1140c0c2000c011030103079040310800c0201c1070381c1e00000790080c0103a280164185210483c42c1c400340c5080f05c200440b413640200b4041400410360346129003544500c108a400740e407070302040d104403500c0030145a01501d00c1c10140c103c9290121004001150305403111800e082c0102c0807617441d45080201201400020301854503240e009803c0c0860400045800c900c900b00080c00180003620070450700d51072004041c0403142c1039007003e00e824050700004242c421109010001854188503030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 999656537 1250 999655287 999655289
    0x4030b040807030215220305040305010c0806010914011202072d0606050d051f0e0f16050103060302010519022802030f03040b040303080a0e0f07060906081e060118 72
    0x45214076500c221902d40603080c00049485c004a04589004000d103400d080c6820a554943c01001482828890702d4155218040c540000c1d01c01d6180032104280b250f000800c01e40207802c00d0303c0c0c0d00100c6503600c801e07460401c4000721036030004045500c82c09c1031840e2500a803011a104800c100000c4100c1e442c01c03031400004482228104804207000000e000d180c0c890a0003400042d511580300a0b01900c0b4a540c0d0b45200482c01401120081d0300c441d001e02c964800c3e00003103528401e481d29401c0e2002110f6564031903803a00304000080c3c1c1d00014840d0301900c038035403c03a50b0686a003420450040d0421011180840514082d4040c0309101c102d11000f00000c1c0000f02810a21030b10314400e00c0c0149031034400c43c01c9014142d54002c11003449091286410b803411298145880b561075a54800751201a0a00303414040e55841000c08004c05210042030305016a981540e1301ca80f44c9030b80314002c0794201801c1c0c8100d5003503041042a0203141c15080d203903691061041c14003911008003a030304ca01c405009 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 999657787 1250 999656537 999656543
    0x602030f0c19080d0f1b05031306110c120424051603030501140a083d1e02031005060f2814090303090d050f061608070c05150a0204030b04 61
    0x359002034444c00c0e104952413039600f55020450340b41d030184c40c6801c0c504d2440c10002807000120014500c14652680072448681c00801071005601011a60a56400031090000c0f50b000380c45401d502c030488501030f1004c44021018000510400e204142c201944400e045c50410204200301c40304028182180c205040c4240ea000580303600d40320890901c40c90000c0318178412600000c0170840d110307002414080d01400c0046000e0300b0300b50180242d04140302c0d09560600b15140100421400260b540508411050354090404221404100c6800c07071000b2030f481d101c0540c003503c05105505194002d0010700f241510080c2c0f5100c031220319100584494450010503100f0030107400090399100042034880100300340d00506001c007000020b5128004d1401860091601440c01818094208018250017407500103441e101c1c14292a01c071001700400f54548041040c507008500a28403a00e01c9a000c90340142c050460013180903a0325120b00000703031401721074540034003000c000b060181c151030f0300a0344 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 999659037 1250 999657787 999657803
    0x20316060207091d0a0602090303090d0b0609071b080f09040216210512100b030f010302011412042301020d0b09010e010302090f07120204030b0402010e0306010602030f0c19 76
    0x110780350856050711301e8601c401c0e18002c09807070b903614070010004c1e842c985a58844409a02c03502c0e4680407a2850240d0000c040d401210f0084240500c0841d034101400342000307440450306543d90b90800e980c800c0128030b81c5c0305000580420301020403d100003400035001001103851428550000003001e90300f061400021180903e03d009040010380803070800d0030440c8000b03081d01c445042e0409040d44c0280d07010000c40080040c0004d202c401c44400c1361010300380c4803109603140e0400d01a804e04150090104038089410301d400d00c0b0115160400b500e0141d14944042082c60741c07650f640e0544100c074000c07118002a541002095840c00a001400c00800c44a6000801c0ca910b0b0003000380d000c5042e404010154500d000500150b2a002d4200b52f0104005d0300040660715401c000700e0303903044400d00300d0b41d9203480802d011041040d902ca0f018050b174000d998026516030000109a1142002e01c1044054ad0040140038007029800000e000703c40c601c81d090b00c00c03610322580c03850750b1010108802c8900300e17 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 999660287 1250 999659037 999659039
    0x703021f0215090f100501060207140402070503030103081c0504110d1a161b020114031308040b0315011404052e02011d1c0c02041803050301061710060507020316060207 74
    0x40d0030045e441070004051800c0c0495403400401030f44030b0314039000306001c5506a020418031502c1e160102c425066111048039a42e40e56400c01101c1600034441340e40003200401a201510301413409054051600400d03401144111034003041a6007a24940c12241c05034091410b443d00380707079010403510600300d201d00d101c551060000c2c0280341110071820003c0c8200c2e980b14840250340d002c12200300450000300c0e10340e03036900c94014100d82c50021030401000d41500140200740807500301c020394094031074441001c00105110780151440185140070300740018040c08104006d00d003508190889852412140c4d02d0034895140500e00800234003042c40c00341c3e445100318240701d00c03101940a54040110040d0440c0c04255040301c11000340c010300b038001c000d0001008000d640c0c0e0f075446520f808100510048001310140b40140050304248100380200c0c1020b03600a1409540007459849003e03018030303c075482c0341800f00035602a009000c003a44c140c8252a41c1c40d100f20484210b030307801b51a0030780040140d5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 999661537 1250 999660287 999660313
    0x72706030e0a2f041b050a0504172a221e0515030307171b031b071a0403020409030302070c030b15040e1b190e06040e0703021f021509 59
    0x40041c10042c140203510700b051503500d0000c05d04000703a07a2a542d140056071100c60950490b91340c0156000721200b89601c44000308a0080041ca54000010704400b80308001c130788452006402c2c822940040d00136000480e07001030b45001d00a9807444004c6040c0000307c19007010b0010002038405c940781e104107681d07038040c8081e1692840442c0e40e510030440085190900655500b00c22012400c1768890007040807035200b0480c40b49070031600031201c101003100c0e15144420b1a880004c002d240c44903825014071440461451021110444c5030001c08404520b02841c55080c4401030030400300540070103500b4002000000c61b800350000c0214054600e80011341045502c113407128842c030344441e2150745030002000c07200b20082040540c080e41d6541c00c451a1000c80c000c07900d1844480146020000b0000d004907250780c80a407003901420060307804000703015041114a584030081e0001940c0034801d524403420003028002070420410f254810b40c0c2818240041d200b015100503603609466802c001403036854 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 999662787 1250 999661537 999661613
    0x18050402120321100b0d0f110310140303041e060f2c0d080a051c020a0203090d03050409020a0e0907020d080117160b03072706030e0a 59
    0x10442151002d0752410050404180b00820103061141c0072402010001d0742d8800c4501840e801070070a07240740c1e551103600100100091040c245c0c0c0644540c50007903016842e9070700106036481200d010545500403410100740088002005181136807500c003c03c0003096404100d440d1403180d00f018082050700e682000f030060b101c0304802e0100d03010410344070350241c08061501000e11a0042d41842d4215a5040d070020804001d00c110001c0c101380c20003c2d01d00300d4150b018008042800e000e510340700c0103080e031101d80400c0c8e00ca030358404401070b407082c1701000c030528086501c640b8081c8a03007800b929007a91001c4150698005d06800e002181410364140c0f501d0405054860b03220409101030541b00f5103490780035100d000b0600a0740078444a24100c1c6400c00800c0011008228015842e0409903540b40b0b00403006501c00c0315010001503240010410214841526010090075030b01c44082090410008400800da65904115544210703030101001c92040c04c0f5000c46041c00d80a00900d901e0380c2030030509 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 999664037 1250 999662787 999662809
    0x71b0b0d0e100e1e010c05030412020a0609030e0a050901050a0b0a180608010609050f0306270328020d050901080403030b12100b03280f1403070b1005010c030e0a18050402 75
    0x1004c0d034108012007500c41d522004503a80303d41e0014116480c1240b081040303240440c0c4901c000c0c0824034011f841018542c100e030070042500421109120400d4844080c0092000300b0311419030403d841c482e0500c800c1d032061016188010036844d000304203002c0d01c142403500c2051640942d0100c6e08200061280c0c96003c410b40c409480c0a48485215008000c00303c0c2c2d86140013802c0c0e1005961005000318401c002c0c0c4580b003504055441120b4840943d02100c1c51a03800450b019200316181d50305c400400e07400481c1c18010350700161101400e1640d050010740d1180f1004004408140c4e036403403000030faa81c5003d1000301c01041d500c02400505480010142100d03004480240300303a0200b0740300185501051920036845200384004007031405c5602c0c16030054020118000c00550822646c6c40b201c0700000042c2801d00e0090b1240441612082003080d08805c0300c0c003989000818648516000c68040c87c44201102c0c00545204485c3c0d85d50010001c4940c2c1c24075807180c1e1107071900300b880306500e0803443c01c038 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 999665287 1250 999664037 999664093
    0x1205040305190201061806090509010c020303160e0405041112070513091a04080c060a0b0a060819112817090f12071b0b0d0e100e 57
    0x1055051035100501035000307010400e0101c2c01400d18245030b00d4800c1d003084000b0400c4410030701e01410256400c2010300740500681610391302e0400010074981050203090041c904607006035203940c40d005d02d284009585c0c0c00d00d4106200c1c001c40002129243e6100d210b01ca40d000303005002c902c01c1108100a403003401410049200c0e84010f80502490361761400d1030000b01e07a509030014201e8100e15000310034100b4024400034441c0d9040400042c80040d00041807503522170030540f05c056a60b074003c40225480d00b05000e0300040641410b000d050b01605800d42c008564050254003096243c00000940e00442984c1129810115491800100301009003540d00045100642698003141005262a42404554030411043c2e00812843c4200340040106409418140ca5968846034402074081c2c0c00f48a04440015080201541515111000400ba42c07850710705246802c800c1d003201d80280c100040c0c10301040c0540180002094805d02c1146001090300300035004203041e840300e074a108240c000200c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 999666537 1250 999665287 999665291
    0x6072c0603251e11010f090c05030d03180206070501180c051005040803030f060d0f0b0f0f0420060405031c110f07050d0305040519090e0d022a10080712 67
    0x2e40c2c100c5004160f5154400516143d10040c0029400d0741c09000340011030320703255250000a005220041f4800400d0f14020b800b207500110b811402201180d211902c44144007424090980062518100034005180200004a10ba0305001003007064050b40031801c44400070b00b24010810303410100c05403c001f17a583d0511505252030901d8158482c07100600c040540f81d1140d00081c199610aa01c0c003610716080340482e03010804514162401e04402d44502c41080061400034003a0380300640c01070f1007603074014140541c4800b01c41407031040074135890103036038821400e010101c1c20780c80400c0b08880030140c9002c1c0148281d10030401400303182e4800c80141d45a0001030204260b1403000440404840040d030704140070b20000d060032901d50040e42c1046900a100480e591009406002040d0549446600801c9002440400e580c4e407040207000400250308002c9440c2405502e001c0c0c2030f0200000c1c5465052a0303000726001500c051a12440680401c03201000c4c826044c0e03022100600c42d106808003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 999667787 1250 999666537 999666557
    0x910050c0c0a060c090317090406090204050d0b1009140a050a0e12030703021306020a0515011422050f150f06120702390306072c060325 60
    0x182076201c108681000d40141c4d01c0e05a0700354540e03c40c00c601001142c0015880030600c00410802181d9403154100380c0c881c5003488004100b0701224800c4400301e0304002c2440d41e20419a03500d4a14205005040030f0304a0a8228006024211340c0200d4100d07100c3c05011440520307200f14030b0310444902419442c121850082c003200400380004440e40c103070418130386460f100e60715441c00300c0c0688a000c078040c80014010500040309030300080c0780c1050303903c81d20964035420014080403012010911440550540354101f40c0380c4c608184021110106802425052014585040c10196030083d44c0d207031881e105410130448100240390f1030300815002118034410402401c000200e0a01880c2c2510350000e00301008110101c0c020440941080c03141e44400c104416800b45141403981255410558411915a11585072401180152242c095621800240b183c40384444408cc407850800e20b20b8407030074640100701e503540c040186200d0556190303626100d107214086003040800c0050000700340710050368 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 999669037 1250 999667787 999667807
    0x30306120f02011b020a030b061c11060a050d2d0207150c050c150915061c05070b03041110410c0106290406120b090910050c 55
    0x559a00709503024a00050900d6907650b40000b401c200d100c00942c441e0348040c0010402001941e9144503060031219030310b01000307200007401d10103000c041c0207240700c2440303031400340a18004000d04491101c03850f029060141c035080384011600c0c210031100000040c001858010b40c070a03050300940701d008880a40c1801c000c3c1e904ca0700c0d03c0091050081c0781d43d860700c00d0407100603c1070059600c00340b00501110f02c0000c3c05a400c400e542800d8502501c6400394444900145068084090007140d01816282d1819160b9901501d2101c91220460f403d00a2010024100c1002c601850149001d00786640d03580a00070b04200003440a1200c21050140c2000080003820b07500c40c4482503031098040c4402c01039143d03481c1c40c00803108061142401c0202080c006081e40e0150f01240c01d807070360f5501300404504001c403481c00d80d504800010034015801c12050101c1840fa10840341411403101d00401d00c10020070024a0884044981907a40e601c81c40100c032080b0154002c5a810001c001491454078103022 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 999670287 1250 999669037 999669053
    0x31804150e0f10061110020703171905060109121203061a1305010e06090d0c0503030a02010b03060702060108060103060e03040b03011205010b091b13210308370e03040803040303030612 81
    0x11048801d087d401300e14401854000c10030519030f03407044d1110900340d1900e00d48030040611a8078105140500e04000241154003c05d07030201030710205807031240050041c2d5110a26a4140d4011200700f42d102d40f000607141c00d40070b4000000c503091401030364441020044403110002c5d10352101381040114102e01703a40d80c80340e8080756603503070058401824a140d2400c1100c1102259031081e82c05100000302c22141c0c2e03038194044402c0180c00c4054a60a031a4450102c3c0c0d9403000380960722260300306000400003d00d440e4000342d10f00100cc0305482c28150f0300c150007407554009910044c4084000c071505800c124080c459400614802c0b41d0350440c0d401c140350f200c04422180c0e07100c480100700026035044074600da0050a402420800440390700c2003000c80c15401d00f130400b00343c1100403545204c00f2030846441c450010003a10100b01c80c20f0301600c080400c541a0580400c8000411079032002413190001007440200064841c4100442e505c92441c40c00800b01d502640c41071400b156004c5950001807820 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 999671537 1250 999670287 999670303
    0x7110a0c0b13050303031009050a050402011407030c0b0103080d0c171503011b11120304210e030a03020120031905040c120f0b010503031804150e0f100611 68
    0x31001c803500c40d0b020203000c03914040c0da03800144c0c0c144804001c00c925070207c1c10ba09010750b049130a051140f034403402000425a041610000e0104002c03013100c8503050000c1000c1c28140d402440c0a9003480451b40380c1070043c14080e0400e40f5084800180741400341064010301400024a2400b60910200c3c6c190300c1a003d980503054000c0125202814800f40e5002d4100c0c541d4104006d50601a0420458002c0e080c0b91418540044a020340ca140c04401c6200d40160b0780304540100b0040f12400d080b0200903ca000c262001c1002d1144c1b214122020392010411800c2c0284207800014521001c010283d05046440b440c4111031003040040100565142c95104d440f01000080801c0d90b80352498415030303441c119002035401300030300400d40381403180080c0c0c0c0d1100a8040c6a00160070790701c07641819100d1080104460540740b1481074084103041c0380c0d200f40000d500c0b0742004519151500511040d000041c0e548606c14140c00c002c0c4651200c05807904002000355081800c01c96050a5800c0c1d10f40102c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 999672787 1250 999671537 999671549
    0x807030f20121e03090604170a1d06070b0f04060608160b0703090519142706030c1002010204050f010c021e13020a051306031a12030c1507110a0c 64
    0x101041d40c02100100315071802c1e00c40c0790000f09584a14020b0011a904c1c0c104480c01d076030752503010301080703500c031000b0041342c24601c996074070315800b010505402846a4018001d4940280b420032045d00800c9007180000d005e050000075210040c2002d06058045ea40c00d030b049021690883d811541000c6c0350f0900303e4040380e80a840b829255000750805a034555020707440349030407482c0400c8c0003c0c40d0340d120054500392a802911042105030403800c2c00400b4502080c0c540054425040d03010070609030900e8594001002821070365258003100104052981d108041c0015079000718007405a4540f64250000000082c0b038009844022030f00092040c0404c0c29007000e00e101c48143d90030083c2c40f110503082c0048080c400955441030110001801540321400d091483ca41c143d40c0800e2191180c003c41c0f0b19404040710003162001e030002002802c10415100d8409444200030821080c04288940f0348501e008000c450254a010100507085010003e0050420b4000c42e51100008070307090010030540350 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 999674037 1250 999672787 999672823
    0x406150e0d06141608010803030c07081305042306060a210e1218010905061e040504060f170309010504030303112209180b010e040c030807030f20 64
    0x1d5410000c2c02442c203000c280c51003118010802c50601d4042c06041c03202c58150340c0701c103060b03030b0394010064680c00141c41710346040400300030100214141ca0003910017418032207044245281d41c4d400085c00c552044404e2134480e400f14100780c20b0030301d440d0503940d0301c00c00c10354a0518000c5800d1008100da801d107880600400002e0094506012840d8822100302080200300e40000c40d1403100100700341c100311a4024880f60600b100d41055105d4407410045480140105050410054001200c4030440107030024021040c003000032503907198003c460041c280c3e5814642501d080c10401034020780039403507000b16a481040007880690344a001c80301240d40614001691b8020382803210924403030b1000c2d00c1c42070790200307004000451107070f42020101c611b140c80400c401d90b02c800700120ba40d50311325809054801c0c8c038401082100031054081d544a4881d0081400c03440d1a079448070400d8100b0b040c2a4001101c51121070800d0707420000001d541000c00450b4080f84003204035140d80c60f1598080103d084c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 999675287 1250 999674037 999674059
    0x606010813080409021234030e06041b0b04030c050f01050904050a0b1e010c0b09011509050702070e06090a1a03010f0b03070b0a0909021303200406150e 67
    0x1089110104000c01d41c002182c9035259541c034003000c06500007414050140c401880800c1d8403a01e0b540f01925441a00103003403d4000c92a10700709032800300580d07a0400e150316600c000d01c1450301484581e00c42c5206105042d500100347c403480f504102e880e003000000100402092011034480000941145e104030b8502010703d10f4100122181e02980240c035820038207010502000e00519081201640429149400c100396070109504001580039a581d02051410712080c1c04a075004000c103a1003c521800411303003910b40f855010190402c6da010b816516982c07400d00c09416030501440000703040321010400c0034240303100010904c40011f0503007040190307a003010060181c00c51400d03400070403004000f00700843c00840f211024185c01e039003042c03081c0100d03c4085a0551448203440d03440c00b5079607507141c200d0304091062009500541e007032803108290500002c001341d111100c04140c10b8a940340c3d0b004020a2806000948205030440c829040f070390f00c01c82c15150703446690603102c2d45007124402130b44 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 999676537 1250 999675287 999675301
    0x10b18011a121306090f1104050f01051008090114010e091203011406070203010f0f0207020406051005030121050a121806080705070f0c14030d110c0f031501080105090705011106060108 81
    0x4003c201700c0100300c40d006688030b00c14845003400d59170040d10280d0b01840a66502d44500624110901405511001e009002c842c2e5500c11071b50643e000c000f4200010300300140d846071a112143c01d0744500e101e4880303802002118001400511a94007038140d200d81554109075030000c42d010804825809040b000c96100d00307558003500b10708940340b44d514040040b88040c411350006940850030603030080c1e00300030000503603081030b0b00c90044841880d5202800c41c3d0070107000a03050403004141469083c942201c200200e0300900945030042d10030481d81c000f5150190300509114003d103c042c2c18492030003010041c0315000400164404081e1510036580d00c0d80c0c1c94815158608424007034032801d8000f0001c140c2a4030503103a844146801c80c02c441c40701c10701c04022240c2c042030071303151001c58000603130078249820a604800da518800038141c44100440d0302e2500040c103800d90010381b0981d1100c060041042d0140180030151500781380c056011800095650342c3e910000d0082030400000030002907031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 999677787 1250 999676537 999676541
    0xd091202091b091002030c0d020601050d0b040201020f1906140601020d0e060409060b0711090c0405101101090b221115040e07050a080c250203010b18011a121306 71
    0x10308400804100d6081203000c0b0007981c0307030405207e0035001d20543c0c103002c02060000841c641226001001a102460150303070b0800300c3d22015000320f040d0b10401d0151740d95480d003805125481c0300b100d9005a00c0007910b0403e04151001011468408100001800840c2e40e003c1243c441000701800c00300540038280d000318010340b00d2a807000450910788040805c20002000040c001070340909070394000c1c001c00c003041080115050343c102203290001c00041025003000d80030417130828007608180300003007a62341c0c1c01425940010f20454000e540342d404c0141107860600e0340c0d0309041c0644103806003584641e9507040170004213000789200b4060044802070b415682000c031400380c03000707580b000b44a0401c42c1c006052500500e1200c0c010407044000601200e607844185c5c1c0c4070304401545540c0032540722440c4820041c0e0710030141e0b015501c900c03030010140c4841002d0003501503152011001d6600d841000c0c0a42c040d0031041000b280001c0103050f148400c40c900080c1c001c2c12079100c05849010500d80940 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 999679037 1250 999677787 999677797
    0x2040815091603060207060f02040b040e062b0b161b1e051515090103030c02150408210406200f3a0207090b040204090501080d091202091b 61
    0x300d0b69048110200400001d41c014100c560310401003400800d0300d0381b206105038021070042e1140c001042c44100b01c0f0280c00042c503070304448090441160840300710343c009010100540444a8880500b00410400060b441c40035403022a04848807480c6122400c0184000b00150100c926400011645410b1165440c5107280e406660010100b2070407207860000d41722030010400c44100d152039800030381c0041240e40002c1d207050b0000c00c2244541e007995821340d0842c2400109a80102e40e4004400324800d0070b100410241848800401ca0140e080c0400020b82d02d92003041c03411000c061108000300e5400c008800300c44501d406103541100d905002d69031504000c183d00a00c0740c4261900070403005108940d540c2d10f9407480d2a0500100c0040c29107a00400e001c2400c600164000e400421032000141c0c0300b0b0402d10700042c000f5142994070500002610000e800c041c51a0304071010100c41e8680005002c001804c41110110490305c00e0740001c0c910800040c00240e80d041da0740a04800440903004640c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 999680287 1250 999679037 999679063
    0x220204080307050c090c1204030809010b0a1404060902040b09010c0302030c0709050103110303030717070c02120d03180b0a05070504170604030f02072904030c090209030d030204081509 81
    0x82d00d40d040c0381001d9076105405188980074008200228642c400241c0403581c200c10f844850580c1a21a84c0e401c42d446d400040207803529550300c04103160965500003004000340700b0b00300c6080e01c85080310704010440f50b681d440415012710410080001500c403005407036a541c03003402c28524240c03007070800341d085200d094450612070040d204041244486940300f58140c9004506202405044009040e500e100c2503070a04c0203c0c281048600b540082c000c01158400c049141008060000d0fa02080f00c0010982c0444400c3d008816a0344199a0610900f800c070480361030010365181c141e890709c0ca0412006040c00c2800d50b03c600004100b140618101d03002010145040100b01c80f8500c1c0c40d40d140c2405a074210002020110f203c209136200150281c10356101c141c0c03c0381941d001c100b0395171010210454945000030103200c00408502444a0b041c000c0c8421880941d44208100425017031241902c01f030b1040c50b00c140710510040d200092144420a500380040c04280c90342d50380c40e4500007115980c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 999681537 1250 999680287 999680293
    0x2070309140a0b130f0905040201080f0403050c0a081c0603080f0703030b090405060402090c130b0913060807030c0801020f0327100b040b0a08030a0c1110030b030d02010b22020408 79
    0x1202c3e4504240e8050044174142442c415001b6124041c0c00217880050f500030b4002007000c4003040e4821541e9400d560803d100e81485442c0880e4030401c927003400e40340c036420740d0031320400703e815909141c401c040390311110014141044418190740d5102e4803405070780d003200c0c1d0071100071480b842094080d5110907084031009010300b05d185070601e0000d640c0d8804440480c020305000f07004c101a0001101940e5003804c103144100c0707400d414100e030043c031600000a0359a02c8600201c585440c0703847c40c46000042d21407180600042d908500300400c1a14080d801080e180c0c0c41000750084082905081c0c0b5002305c0d04903280b11611503031341c0402da4030800c042d540c80300314050201d46a90042099000c01e45c510001e807070900c40311000b2001c0161617421403043c05010b800030400b05203464070400b41c3e03558580c07040c0008030715101560b0104003032030042c405110110f03603038460001c43c0346800c00070100c540310302d48028414044030744040750030030305004503160001c414000b9150f84d0001d00d40550740500515011 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 999682787 1250 999681537 999681547
    0x507120e041a01020d1707050702030c09130b07050a05040e060103021315090522090f050d050d1a030c060c0a05060c120f040528050a2402070309140a0b 67
    0x85115800c8509680f40075100343c403035414140e405084030740c040002c80f4203c00200d60303824809650641c00108100da240c06541c50f00344181d03030703140381c02401401105004c00c082151460a41c22501014240d501400024407030042030517030050840c2c00340c412074840d00e82e10381c40b07200050b000390140388900b543d190380b41580494840c103030010311014060960348001d12282d50b00d0500408001c0f080070180340320800402e1f103107450482d400820226201c0c1007014082d00070340d11130b01c0c18422001d000c00300040d0001800405031405001e0344414400d84010031805c080f20000013560780c40742001048c0101804503801c04d540341c0a002910740d1344d0700401510010318041c40705a8240d030240c0c9001c0800020030001c1001c0c4220160481c1c4035544c40402810304031501c014403142400308031114200c400e0702c2500d00001a03018440702090a200300c1c2d01c101c1c1e40c0d440440a024510b01001041c0000388144144004240e0152034001213606961030303080e03581007101c00b1601c285941d8100480880d400a0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 999684037 1250 999682787 999682811
    0x301021b01060902090102032d04080601030b06100206072015060406140d0b15060a0512010509130209090c04020a11070506040308030c130911280507120e04 69
    0x4558640c44903420080040c40d4454896400703c1c0070340b17505e16005a000744041001540d1001200d070300541d06c225407003002c00031200c4c2c800340781e4065001100d8a8001030010230803c01054031460308082d003298107004000303503950b00950b00d0200a2860041240074450700440f160a004003a041e45804c000b40c81107840a1150341003107110503110310340283d1070702c02c0000d0314403041e070130594070f44030001d181d540940102e40b00c014200001074101041d0102034400980745940718070040030b1030320003516031586440744100c24200d0342e881644241c1c095090b9004201010101c0e80004500c5031781203a400d0182c0c1c94440309070303141642981600750414800640881d03001d401a039000205601c50044419040d2580c2c188082c502480c03000911102050012079400503110014220700b00110064481c80d0781d5401240b030070350f1880712201c441070f03400203400e00660b0039003103500b203504802c0e650b0310451500d0460010324602c650036020346030705900d4400d550924410b500008042c0700080c028010900222 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 999685287 1250 999684037 999684067
    0x20d02031e070803030103031e18260c030309100909090b0615040b07030e060d1103160c02090c0c0a0b0a3c18020603160906021c140405030102 63
    0x2000e0103942c842d1000028035010004220b034141c0b680340d1765a440c2e4040c401c8460380a881040008400e001c0c5286a01d0031000b2030b4044580248120481600714804d44003440743c2d10464401c401c107886e000103107035484546000040321801c800a89030802c208500e440101c0d2508030907000754200ea401c01c28040c0030b1040507054580a42801c544ca13510b00030290006d0007a52160b44944042c4100030300104002c40e00506d5866001900070306414601540c003284401120a401c1001c02c400c4000b10601c8008007507159141105085400c01d42c090006640020740d1080c0002d04481d0040c2d00001c040600c2001801240030040d4019101c44190800225134000b9240c07242c0c680c0300c1009081c4440e10183d1616803050520b0040c0024840010b4200700040d001d00300c01407055a502a100701100b005865030301c011441000c03603100c0d034500e41c5000d0764020b04d501025440281190712106d20b2040b402d01000340c1c0d4005c1000c505000c1d0001c904044043c0c9140604e511541e4194808510501801044 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 999686537 1250 999685287 999685333
    0x30915050c0f0f0d180b13031506140f0303070b091e03030a050a060e040b07180f0f06170c1315080a06051f03021c02041502011a100507020d0203 64
    0xc4426100444042c85049130898885d00c0f00c209110304480b010005510828024010043c0304104d5011807616a103550205410700d2103000d80359036581c407040180b204491068030809504440c03200d80d016204000a560340504180540410460310101d1342489082103800074445040380310f00c0d0030107195800325840740c02c00c441800d490350400002030444040783c800d1400781c03180d202c034401781c1d62555242d900d140000108001c060141d080c0c851036048065100e5003004003010505c0c81d4025080c50000025040f19512580a0006030301e0380c941d0762040030312141c0e03000d1075103c007440c2c0302c408000185070000402d41c42100409400d50741e160196502c105c0b02407048003061010b11508d0ba845090000c044036500040300302e40e258101d01c2031020f01c00c5c1c00074041403400080d807802c41d40003400998100d038040d03800106042042d0202d2841c058080c0075070176100d0800200030400603c032001154641c40d0210b064410040b00103658805c41d620342c2c004510f4250090211409420210031a920028034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 999687787 1250 999686537 999686563
    0x1207030b090102030415090501090209150111210a0512070908061501050306190302090a0c0f030c02070608190617010b1906030b060c010e010f0506030a030915050c0f 73
    0x50303580000e080c400140200da0003194405507080170303840340340c203001c0060002803000c6400d5500c41c42d4080140e92449502800780d0a20303520031510921040c00500101070a20001000b031b00304100d841100d07242c80016400c0c21400002c2e40340d82e120292402c45c0c46108910001001e41d0a00c420702075082d2348980c1781c0742612030b10030444031692075100e80400c0b5018003140060000c0c90400001d049400c010f010000380c01c10720f810700395032661039500045910104680e110100c0359a1010101034550120040a030f01c191410704110411484030000d45850b29800354034248981e05010071440080c10042e44c2c8d003419511010062a500c2d15844e00ca81c240b50302c0d0000300d940c28240f90481601e007a031040040000d07903110310103843e460480d0a901230019601d8169000109124500381d4007400c2c0228606101103070000107480324103071200421140c1c05130026020364025810000041c6d00212404240d40040f8842e00a641c00b81400320750320310540c03004400324081c0da00d15904030f0400045000c00d48032 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 999689037 1250 999687787 999687803
    0xd0e120d18060c050c0f0d0b0c0a180b030606030c0919030507091104090911120309011407030c031103130f030b0609160e150c0a0c0807080c040b0609120703 69
    0x25a4440c1100d40158050300a4015000300e0b4041d80b0924000c00a1b4000040203060585d001a840c0c68503002c02008591200c00000c00059400200e40d0144441e090418203031119940d0a04105030450580402024940104000000b282803c0080419201d80e81c80090000703c0000b1544003d22034040036200441c0e19120750000400e01c8100b0703001d5000c1170882c414071103007002d1a281505020703082014042d912011043d82c10462501c3d400e001d0700c1e62a562130000c6584284040c00144805a04004020407100601031040020b50001d0b03480ca00d01e8252070810390f100884041d207420341c4968581d1800f0780c000c14400080a03100c0100d0602101d0040f401d80280359203d409011150000711650f640c0c90006480100d14a4014101d510780c41c040601020801008900c916000307510100141580c1d9020384480c00801c03078440280c001a06030880035004c0b00c4c0ca482c080a44e154009202c0398881c0d030f102d041d040030382d4032440c0a172031801000411250030380300e0700c103165600c0c0e100a0005445042d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 999690287 1250 999689037 999689039
    0xc080106061b0f020303210a090803040f0515070f021614060c070f17011a130c0c060c0807020712020d03030203070e090f01140406080d0e120d18 64
    0x45062280380215800d5403158801e01507603110741c15003925440422551a82118480c3c00540c4081015140c02440050720040034001034001c600b0340b02004100d859558180044c0800080f9550300390b0f500303c1d9100888a041100d14500503081103a040c0c40c802540150300d0820020307a0784100180d4400c82d9580a6826002480d0314021003030f5414001c01c40e100020400c0742829082c80c10050081c00880410380da82186c0743c502c4035002200c154003c50f00c4000900712207903021420710500a1004c901c40340d401c02444c040002c00c040350308034100300c00899560140465100d0003003080200c16a4010001c102c00a02444c015000c1801640c05030018411020007190100d050b8107441050f680040840d1200c40550f6811030103540014100c608210459894220740c1d204e1407040e50088288034640603003507060200501080c1402d10f801440f443c10010b0400c00c1c405e02089a071181102c0c2d140c48844140c001002c80c08484009519050768803908900654070b55006000428961341e80c5140f030380d0f003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 999691537 1250 999690287 999690299
    0x6160314060a061103041a1306020105040f08161728090b090a050d0501060801050705090604050418200319050d0e0307050d0c240c06050604180f0c 65
    0x12001107030300c0381d00542424400d0040a0041300000c44400d00b03003080321318080c0c88a41c1550400410051100416400b044da0f00c100e100281400c0040c2800344020411450f160b190103a039075000070341c042c050350400107031036550080e90000400155000f5954820001e00c1240440d0301e940524204080d450b4901c1090300c02c4620283c0c5004034034070030faa41d03801d11402c3c807450280e560b01c071000c019031240d01d0443c00211900c80c01402160b0602072400001c0c001e282040c00d40c04d41c0e0000305a442000020002001140c2d2004195802e4a40a980008003161040d203040100e0040c80e001030120140c3c140c11843c04c04004240601044055058a030b0003031030803850002d10084001d00034a40c0e001100c42d240c1c213510449104611441c0101102d00080e9264041042400204170984150841c0070b418800c1600b1000044241c08190800340043d000260000b00620442680100b040341c07224041420350751a60040e200082d142c400090760180d6518040083c465103840448071098828000076071 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 999692787 1250 999691537 999691571
    0x30f03020408030f280f0f03091a0a060f05030d1b0c030506070f050702062502040219090503030c15040c1a04060e01030b031b04020d02120403091203020703030507060e061603 77
    0x640c00b21901c0720180300400c010240d03147c645940000b000c055861400740d0104191052014504500079420011400e004003040300b07030f40b45504802c00e00c052540080082d52400107405d08070b440d452a000e0340d80404a0b44031500c0500200c00a0002040340c0e40210600401003030f0b960007040f8507150b03c92200a806000c0c0c440d4001d17900045e5100c1030502c4424503500c00c0c09045070310101100900e00324100c140d4001422030b08608100c0213209920400180002d40250742a0f001d040e040700110304245c1244c0e1465a07406030401e510031010890b40118003001801034094001e080c41c00b110300c0e0030901d44240d03013609070007500c05c000004910070960245c5500911440d5240070024020781088042820300030000c04020387c4454000313500300400d141e05440b61002c0c200f42442e0384141806800c1c50708000700703151555003080c100400d0701184440000e800080d0202240e9041c02c0c406d40752502c5092150041400c0304110b19940103110400503160340c01e010000f40c2404503101041035a0f200c030442d0103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 999694037 1250 999692787 999692857
    0x209031b180903070f0c1a121513061413090b012d03111f0504060804150906050f0a0204030c0504020f0c0703080c06010918030f03020408030f 63
    0x9041811510aa140c008100481582c4200320800701d030300c0e004203039031350800c209055101a07441070820313101801008800800f07181c500d61001540750070b0543c3e60220400704103002d05004400d050100104981d621403c029803813070a2420390401c01d00b582c079901c040c80001c1d0200b0080c49052251100700d0102403520801e0600f0348c0025a80c41180e00b421954145a5081c032010a003480d00320600c2800d844ca22409480511f11030451032a102e14004c0c2407058801010b500300ba0100c20f1140c271080c096900ca010b0300d049518178030b081e04650316107060034180c036600d100341800420304207100380742800025000755000e4031820501c0e01039940c545030314100302d005074040105440d400b11003c100703034606500030700001c1c031030b03902c1540c5402c8200005910705400f55104803a82c40c0046070f406140344050140d680100061407090181d0150025280ea21030b10227400101800710130200e620300c40e4840c3d8183c401800080c07003120b0340d911103071108680c40d0b00201c10040044015840030342c800100210644 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 999695287 1250 999694037 999694039
    0xb0306250c081c02040504060807030507060302071a0736050a14012109150509060609010605070c170703060b031204050d14030d020a02010e1c0f1e030209031b 70
    0x41c2c100402c1801603c4858600c0c0c0009074019000c0c0004a250313a1140305800042c00c80c0342c010314585185161060800303003154030601c1450302c18002d04001c0380001445107800e418031851018142d070345400075182503501c13a1041008580c0c9a2148039581800680d25480203012140c21814594400c200306020300c45000b4100144407000b00189103500500941101e24600d80e0a0001c014140d1060340440f94203c00544c5c003240d075222032060080443c4115074100c61560080d00c09440d050000c0b5203115010710911082102c0047c6c01010700c0340300d4240c0c0000c1c082071100002007140d00000c0c035980300c0a80c002030741e10a10b0482e40070300070b19000a000c41101164503042d400c1518110401a004000040648050015100c42500790f0003d0009100d00c06080030016228560150003e08681200300c9108565106100c1410b507000d046111881d22521850306003046815403404a829443d281c8000c00500702485030118920742640203010020419801c17a03200406850103e01e101400040706 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 999696537 1250 999695287 999695303
    0xd0506121606050d1b0201021c02091f03090b09060108100e07050105071401290f011d040209091504110a050306042a0c060f140f07030b0306250c 64
    0x10025a0f00a038090714a80c0c6014400240c0c0c07050007440c00800c0f288800741100180d42c0020340903201e010051021016405009003142080900070110340da41028800084220910268101d01148650088640c1c143e0148080401d42021090386903a14000c0c02100380500850f00d11655030140c0e8400d00c24906a06001400c855103007000654060348030b100190303180c5103241c1c001100c909090060f201c40080345d1f6030707640482080c101e1612403900b215807620300c5800c040100f590305aa02c103024041707070701c0d200b03055400201012000400038482c8040d03040d00320303240104204840e01c2c1042e501d114850151018032020a2500700c0d025a8402c00407014081001070001c11200e04143c1e014155040101d5000840ba9000004a001214240c0d400707030700251003203480710200000741c0030b040c000882568040c0b00380ca0058400381e0000e10001c01c0b4020b1006c0350130001d440d40313120742c00034458a20040d00303642050400b08059041111510200c881c2d0301110700030100854411488240c00980040c80f07 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 999697787 1250 999696537 999696539
    0x6060c031205090705031507020601050d052a0409081e04030b04141f24060e06130e010305030307020d0804020f09040c0e1305061e041401110d05061216 67
    0x301c0c4018280580100070314440c10074045095101000703e91100d02c514501c021440c0307485a4000d1074214140c10080c01201c8000d500c1c000200000748202000d0044010303403003001450840d821402c0044a041688a07080501520034448041e00400900c1a0903001003e588452000300c18903101d03500c0002d04018100c80041c0221f07111048031050b400b0101c042d2070800e014200b0319001d1502962140200e59510180200200a0000b050b403002c404040f103e581940f61034805010310b0808820a4003480300000e002c80320500a400d00703000342071200002c0c2581d50716810019580e4204a4070003000d441360300d0415054501070000540700d9070b4020404140f04501c1000d00140b480040c10850720340b801044082104100c002c14140328504149038003400e01901d003403041c40c0020240c28055041702c0c554a02440d00642001554880e402c0030060040c81400d03042a23004004c0c040d0340009580c2c4c04194080c60180c1600502d0141000f00c90920318012880e41054480124000508180c04c00d820 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 999699037 1250 999697787 999697817
    0xe0a0b190516020d0c0509160203090609030a02040c030519060803092b26030c04032603041b240315050d0f060c050304050706050d2304050106060c03 66
    0x912002da0741c690a070155200e580d010035001c9109040071180380c16261001d0119040c00038075a50b02050f98031424401480c00740300a900c91140c200c0c0c40e0300849000600f2070103a103081000100b8158040e000b00101c00440400500500040d2582400481711660030400451540500001d54171031302c02031450010540e042002c0584601410300c00360040e07007600c010810143d0a1811041e02460450340d14131450f010038a44205242209114064207106010013a130205050b20140c0394410320440e42d0b803208040404014000c081600483c400000c200030030090401c00f6828011036514803003440b40d80b038002c0341020003011041d40c201401e80c43c41c0d144440b072090700145540342e60f01085010b8161620045030b60390103502402d8808030380702c10b488400c03c030709449110841c19280c50141d040d424141d450b0f50f12003040744201401c000d0081040d25101ca07103644800d004a07800c1030045da00380e0990b207440324114002c0340c0c155407a51900200091250044049441c0148c0c19620440d80c510444 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 999700287 1250 999699037 999699047
    0x803010506030601031b031a0d0b0c03060d0b1305010605011713150c051c05010f12110d060f0b04020414061c0e0f010b010f122a0e0a0b19 61
    0x281054101522940d044906c032901c0500d40c4004103407a5400304180a41b005480c003201410b451540c06040c40079400c601103402800c4039900000c203032040541c0ca455010028200b8000c85d1400340110b0005814010609002491440c0030b44c407800090208070756600064030765401d10948c0c0c0707500d0000003001a1a290040803210b200a20803004c12800d080c04090034001c98002c1d51890002c240e0000d04145060302034180c10031803100243c014802513040204418aa200c0b900c41c1130108044d082c1407808120014160f0046844090005200540a42007103c00f901080c0c1d03a20348141c0c030b41418405103013800d000329024bc030040300c03404001c504801c06000b296840080e108840b0f42d00b803061200d140305140510f04201e07a080e8001c1c01d03401c0850106038212220034441324140550342040107115604413445000794a0b8009001805c85003141c04884041c08443c2c00e5582c0a0303101036120000b80c3c00950000c00900c05683c2d07201465200c4440300c2c2c0303d100301810448100e40244028a90364850 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 999701537 1250 999700287 999700291
    0x503063d09322205070f09050409030203071b0801090320070608060f12061f080303070e090703090f06020309010e01050c0909061809010c1d10030b06092713080301050603 75
    0x20405100b981c0910741d4112130098400d0800a14002c01541c00300e0f5100440c84084d00041301d00b001a8a030036a4040c0da00c5c41031010060545012031842031801c0300e0f59281c9070040180078001d00407a1882d01d0000c1c1520150301c818101c10700002c11404d07019070009459000c1e140d107a1501d01964a407203003044031100740074040c07a50003421078141071500b0106001e1035001c0c19044100f10400100d05004648040e241d0b0004505580140100510707954854040420480282e480b020242c44030542200605007a8501421000c020102c100401910398003c41c89001040002c200e0013042c020b481e400d03aa0141c51485c040c040a00001c0c02030720b84240004e41203500140541c5540c2070000c503560415000301c030460340c5a50f4078100707202c119800040c903141c0b0050660307000c0c07040c1c148a000217a1081808142a041580d01c55994026403035401c200c84000000800c01caa2072003081c4440641415455050708141043c4404664078001c4403254191469110305010f085a0801044c06826000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 999702787 1250 999701537 999701569
    0x1305090726030c0615030d0f031a03010e0d180602030d0239070501032903010e010906020d0c081015120216020a060503063d0932 57
    0x10310400e00c1e40040c001c1004140412800700078040c6460058884030750030030310f404180d01980000c080c20107010742c42039134424800002d0038001040c05032001d984484500c4000c030340d030b0558a040000400244000341d18101da03030f81661001c4200d00d5074816402000e49d03511404001d0fa00c180035559000d001c540142c081e020542e00901310300c0c001c00070902e0341d000940c07095000f00c0845008503d403003202809408080c100c2800c0510074510345010031600300307100305032100d0207203980f40d011750042c0d400790001b62244900c000203010003460340c18800020b50256400e11000385c070380840c101059004a4443e442403403205044d1141d80e15001c070484120721240c4c055030420440f05852150840c0314409021003e0405c0030802c1c10703c16504c14040d142c0030035000300c024001305004003c840c1e52130701c012140800a006004650346065040704d003e0500350784c14410700401d41c03090919030a81c0561040102c03054440681e030700400c581c0d40f50407000c0c01c208011035200103225095420741840c2c1c2c032184207501 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 999704037 1250 999702787 999702839
    0x702060d090f0b1b0315180703060f090513020910050604090f0f06081f060b03010b0a0f08060616020d0210270803182403040213050907 60
    0x40d014069022205000030482e81c0c2140305120006101e88a043e541d440f8030880d000c074076a4403003482070344454080140b00600018003200c00c1021901c90400c02040704071190700d81c2816040080d005406040e081c014540301e00c246c0c8070000385112060061501501303091445403103120481e000d22410398001400f49804030061440082c103501c2d403400030001001c40c4c690001c5e01c990358500b03050599107100700c1039040c0c0342403031b0007070100b954042000200d910651175040c13088200c21104002400070fa134003102c1d07110004800000e11981000081074801b0450b135540320f01c0610b003082a20612800d554080e0003100601c0801c1c0081341405203148a103000400c80d018000a80c0d000460a0f880d114003000041e810058074009003c030320b82a000e0426040042c8110242442c00c2c107543ca01419100030380c00401c14800700b00f9501c52100300310024032100680241660103a040e0136803580f05440403030241840c2110f410b803030740c168841c0318003450244001d0b0205c01e140802840c0102c0b068107040349021 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 999705287 1250 999704037 999704047
    0x90103110d080d0b1f0f050a020f06160807020a0c230d030e03010e0d02060f0606070203070905010f121a06010302160b040203060a0501150518120a110303041208070206 74
    0x2031414005030030510920000401e210030b01c01c4c107029800c80301442219901c2402d92500c0c0d0b0700d9402c0403981d0074107070441c6413036038450030038803022880c11480103503a40787d41c02080e0a00461941040d2081004000f03030300c074034510752a04001240c0c0c07818100c01c0038000c001c00c0001404900564001041070483d281c40364030076546400b00003640d0300c104d81c4044002c40c2510b40340d2000340c102030040086151802024210802203070b5406901e40000601040c4188002e600150782541d4503419600f6003038000c0c00f2940041e4541c0d243d0b6000300000c1c000c10302514031500300098010044152813a1603548911080c20500b50074a9076540080c0c090010341c1030540078048030901021000380402403038010b40c000900350030240141800c1c4500a040300b00e0843c10100184410a16620f03051001c0406141055954030701d00b080402c62030b20110141d5000c0002d03241c410b410480021140b00c02030282c440910301c40c41100030541d584c0325034440c00c0c1c0c094424181c0301001c40d0504002e060103500242c02c062801c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 999706537 1250 999705287 999705293
    0x2070204090c0e04060605030309011403090708030c07031a1b0304021809010f0b0d0b01060c05070e010b0a080907061d2806020f1902060a120c0e10020c090103110d 72
    0x2c0c00d0b079002052940341110810041c030805002d902c0060105501841c074162010f40020402695010020880303440000410342081082002c01c000703142e102c040e00d8441c01c01c0001a07451360a144415101c640103000406610004d1909260051000c48680003826106203000702d0769800080007640c0c00110350b807101a02100218031039201d111071380b0001401d002c00401101c1216504000300d40503c605140d01e1000032007041c0240d0555a040c1000f00201e411450840c0c0317401440d4120701000c075854400010142c02039000741c859014281c0b24400c0b00d654404e042561607a480c4580d400040101c1203030f0301c400e1403440300d020300c0550250000c02c40341d4445010b100f002c68811b8228030781c0100248100011a8107006c168200c80036200502612101640d4494150090010203881900001050724110b4041d040080030074104c18410b1003090b02010307028140211402d0310358090001006240b002610203e045100031070700034902505079003503031684840708000010058000240a00b14004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 999707787 1250 999706537 999706553
    0x402010c15062402152a0c031305011b060b03010f0213060e3a0605090f0c040908040e0c0c060c041d1315060f061707050903100207020409 61
    0x14007100c036942d08000a101c0401101c800c441001c40b81103410100401440320030b003170303c034076004520600e000480760741004001d00c1000b14850160040c8100140710703800c419002c009000404444244100031695840042d9820090b403180c081110f0710311043d450004030740b54090701c0728007006000012011100e82c207602c00c03070f440509109200e4806078000c0200b503a010384109011401592030190000182442c400d0750411808900381c05036600543c80d031004890b920003403400342c00c1107090169040c0500113a031540743c0a1007400b1280118107066000303080600074100c9107079210030950300c0c1c00d140c6010420f038007801400c08501820104542184468104007141c0107a050600b6160349a00e8480902181084d0310700940c9403c00f0b660400c08a100c030244040003258000300d4135442050568a11002007040e80c104100c000d03c803c201241003540b00d0103000764162803800030404c54580c004151032601500054643c160b010103160580700c1255000350500c1480030700041020801c9a85200b1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 999709037 1250 999707787 999707789
    0xe0913050a1203111b101b0507082b0606030e0a02040506030309030a0b190c1e230c12090a030f03121805191104090807050118020109061103030402010c1506 69
    0x400d03403600105d50500c1010074842030000440c2c03404200804043d428243d40690044000001841004580c44003480140401c07a02c0d000d448001d00c1c4d500e4402c0da522150400c41c180841c1001c80d207064004540d05020384218500c0740d582100404c8105030503400c10014000050402e07030140002d024045241e2003c00112048034400d1805210610b407072000001c0e100400b840c01c900d40d82c200030022210540100180d4042c0c0c901c1109121990003101084c0c4030741aa0880e0b080200c0c072486025004003480c0700c050500322120a050782c11112a40940c20442d01415100c01d50290300c516080000603c0000780d020f0051003070510740f48042c400284c01040760309810404001d10700c110041010000140005c5005580500c51552910305039116000502140085140125034a803020301c18804488155a405075004000b8401342090104241c0c41c2a11200c04034049200701102017411805000203403802d45410000b182140e840c1d03001103e43d541160805d942d0500310301e2a41040b0072284c081c0c10 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 999710287 1250 999709037 999709057
    0xc0c0a0501090302010b010f020d05043303051006170f04050a0c06081e150f030a0c03110a050306073c0c05070f06021b0a150e0913050a120311 63
    0x169101e406c4005441c000c1d0099007207003103420400002480e65048002e4409940400d0030703201d441e4200301040c0740d90f452855030301e008a145000c0303550030355603040c4c020341c0c8180e441c0c0301941e9060355294030036103818002c6521f81ea003071103501c40000c54045560300382a038043d0144003161885040e5484000484901c0e40001c00000d07513140401041d40d0361f91012002c40c484d41544d004091505110683c914101840740921a03000400440b499a504003c0c55242a8016040040381640c0c0d2503d0860060020002401171072540d10005141c60085041c4d03115040c107448040510480001c10080200d00d400d03010b1081c1e8020040b5283c3c05a800000c0d40c04030038a45030640900d02d079041c524a05005540f01c0716490803920310a04c03100e60302184820404400c2c0841700030f940c07a0807000601c80308554101e015800401190181d0040d80107014103001c034820f50b0030320070361744480b101d80c104070520680151036903014030220000202c002c040144003a24070f01e030002e140124081c0019061340088005 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 999711537 1250 999710287 999710291
    0x91e010509070e090a0f0c0f09020405030609070302030d0503041b091409030406020a03080a060b0f130503240901090c080c031506091b0f0301030320060f0c0c0a050109030201 77
    0x119800720100400ea010b801c034414254078a180084c1c4442d45c4400e6184014004000394041c241007100000c281c00241c0000b1100060841c1c44040c2440290418800c40f03100384200000b01c0d48091001c2244019a07401502604029000070819502d030b0f070020307108840b0540884890f04603104082001b2700502300709100441c0100100344100040c00c0040c000d48401c1e0000c2104001d0f26400203811100190715052841031940c85803140310082110350700c0069401c40004e8039040c0302c0101c4000f00300c5011a5044030780701e1074540d8241076607601440411111182e0401c0c492814103807851405a0018200740007143c041d40907503c1e8041c0740c0040d4810146030f841400d00f6921031505021202080301d2400c840022407800300005107841c2d00185c03202d403c181d100c01003a03601d07100b000304450803150341c1c5803404c0d83c9594a140c02049050042c0240035102c04204a0502c1420040341c45409505298030b9080d0940340c4240c524004d81c00a20180001d219000c0d8030300c00503100303001c0e20020501031303000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 999712787 1250 999711537 999711541
    0x8091203031905010e0c040317090d060519060e0a0f0b0604031202070807060f0507050a020d060506010e03030313020f01090f030308160809070611030408010f090618030c0f2a030606050f0a0e091e0105 88
    0x40c040c400b53b18031120314070b07281015814065402c0780038001e81e020984e008045a0b1043c0101920002d02040c0140d85e00314030002800310901010b00e160700b5210281d13a00b00e80c0ea03207664164030350312031005010301c800251006101010391445000940182030007001522220001503000507568004168100c62040c2c883c000c1041940e0005042c604040c02603000c2c0d071440c070b0050000c0c910a4100301d0024440e03100d0f0214081e940e4426842100980f0409a03010a02a02d0f400c0c041c240401c03c44940d210034000001091403284581d45070703800f0700079440007000700d03505041c001d50f8081740d49592401740380720600000032145002d01900000000d500c02c0003030748a0007810301006444000d12034500701e0003105c0c00300c03001960003d00c1c84205030b0020100240c00c18145407010386030810030f40e8132021004841004804e100200140011644a42030400c855696401032246c0040750492150707011180c22010403031032800f0b8941f41c2d0f01000c03100980c0c81400c6185d4541c1150b183c84032040c0b20581d03480c41 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 999714037 1250 999712787 999712801
    0x70b070201150609030213060e18100605030a0210141b010609021e031e181005010803160c090213030b130b0408091203031905010e0c040317090d0605 66
    0x1c21840781440500c00e02c2c000e81d040140c0500442c58030700c00240107800f11415244940255030046004d070003041c070f00a003641046442200c01c1801e9226540c59401007182c2c1c611494000d20840080320800380151410003401d40807ca108940e0000f941d080c4442076680949007902e03400101403807c81020403c0c3d0061200006502710f070455040141d01c1803041102c90300a84244901452082c2c003901c00c242c3d02c1d5504040d84000c02c4201c507103a0400d1040c00140541000c10722044120880404200e668041230081c141054130f80a1080c9071103600308101c00341450751261540303900d041c0070f00030131188207640f085130300e0480e8000451841d0031510800103004000400d110503800c0300c10842c810070f407102d0b40d0b1100c031034a0b00e01400041501ca0001405582c2d61a11105520b2524005080c0c81e282e240034201c1e07c0b042408140c803030b5050361602c000401d4a10b102034500c4e00403158000300e5400c1a081d0303900c40607200f45120011007603d109115058072965100c51403481c0305d11a800109060420710 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 999715287 1250 999714037 999714041
    0xb061902060f0c0f220308040905100311010c0804030c0f0e0702031306260403030f0f0207081b070308160c21020114270f06271203070b070201 63
    0x38015110b1150100d06200c2410103031000c0e554404450000e43c0d9964480b150308450504001d90501107004001030000140200000504102e0f1480744041c4174642c1c0e4021140403080350f50000902c0c0140303802c0000030951140dd69024254800c80c03026261648a4076008162402a4040303601d080c11450248141141081080d80142c01800290704040c490310454150146502400042107003050942082d50740c200c80882c04101c54498440769030800b820010090080c0c54040c1c2805e0341450015100e4951501c02c4138401504080b1a5040a007401c1500203200c251840406841c0300310400407004c503402c64002c1c0245c09890105900c455844e01c0c0640050324030307500c110b00b4959001c26808519200d210a900710540c2460803142400d01035501a12500500f40340d148000c135003060700320031501a00e542600208084401c16071018802003004000d1007502c00d511044001c015002c5650fa485041a1034503050040a5038521f41010061929582203030b00141c03076003c442ca007403010a83d028 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 999716537 1250 999715287 999715291
    0x7050c03030403111512070c0606050f0604180603050304150206100b03071103041e0e061512060d0204110307080702030c251d070206150d0609060b06190206 69
    0x94010303600b098a142c64003000782000203d158002c07400490400c0d483c0c0282e03002c607a405d180d11120b80f40142459007005107003c400c40b904031416454888041107501c0d00780300d101010b91000301040c1c601820b120003144116030035801c151026454910220001e8000d0014002411640b00564103401c40e02c180245002c50140c5100c1000590f42c43c288046c0c0010000c580c0d0181050400b20006000091207030326612a640c84044880d0259000542412100d2040c0d4115100034003100c1203901c802c0c0800c08000150603449203411001c001c0c2c100060150034082c3d6002100030528255603016802240a0f41c00b030102842400000004210110b50082c0c10756030071280314401142400c284440081e1340300d4001d48018804d590700b0340350440040320315040c0406071540d4a20700b5811500c58000c4850b6400a842c40780240c040d083c00140e500c031158000d550f0300300c80107008045c030440640b100001801d9403c0c056540c281c4580e2000050340700d80c0d004203841041d602d0f0805071000010002030a090300 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 999717787 1250 999716537 999716539
    0x3120708070b0f0106080a020721021e0105160c030e090c0702030f0d1209020a0302030304090c021504030f0c030e18070e03030f120c070f05070510030b0d240e0307050c 74
    0x3e800010300c80c05070300c40e0205500c1801d0401c0180d03125102c2c200a0110203600e51651581e54599008025443d400f10f180c15140707401c01000b4103500d00480c9040e003626411140090000400000801d1241c40b840811040c94041d04200d00d07964088008180c078400120b800700800d40c03000400b40e04508017084210241d450700009003010854564006000451003024141c0701d507203d4505030255910150580c3c0203642c001d00302c0340da45980f0502c1c003020382007401c0903401600480304c41d42000c030f0503600e03182d216962640d2100e041552a5106032018284a81c09078200100c0350101031300360320703140c515001464480645600c00d02d0000c44c0208440088140140030703400c2841800001c0004c1c0f0148d600d00e2840355050503845e641c0c079a989a217400360f55009031000082c43d11101c1031103400305084003a18030940e14504440e49068056048c0e03500c6c0345010b60402101081d54000ca103411405004840100e00400284030aa4454074107841104e18500564cc00c00504072040010400144203640d034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 999719037 1250 999717787 999717811
    0x3010501110312280513020405090604030e010f0302191215140906180709031b080a030e060f0c160f1a0327160f150c0203120708070b 59
    0xe10140e124202c1040134096a60000760200c2e10b0301e11043c2c20030303100360921075004100503d14042500d543e140c81001401d0b80200c1c5050042403c0790710110b441c03071180390951285c85004c0d441800440e4074054036640d00c0300b0594240301901c2121114108140720740040e45d505404401620b01c00011030318a80c48001101c2c0d182d80080240381d207091112800a002200c2c8071029985100100d405036401c90f10039900c0c4510b1a041048140c0c104001e80151303406840c6458000c00001c0a1501144080c000c042899215200078000a8401e9904444440d409801c903410030b05269140e40481d0081034510660713400008d4000c010910314402d11008020012001c180180740c040c00c0100340c801d01c10744070000300c000800245030a8418403a2800c500c5001e06501002d44081040c1d41c641181c04c06000e03a0075440380c00055810b038a075000e80f01b545c1c030000880800240d6240107451a955101080b81c05008110640d42c0c450030380c4c005000d48070b0085000303d03903e420307516100b17600130002030040a10340 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 999720287 1250 999719037 999719047
    0x8090102040f03020609030a05030f21010b0d0f093201020723010b1504050103140c0d1503020d030306060206090109080306040902010309060f0e2a10180b030105011103 74
    0x702a05210b001200e406031101070382c034103541d000f080c00c0c2885210003400e684400981d074011900070340d00510034011882021500e110610750a110500421f21800e038546c8010f00014442100b190f0100c040302403820800203180031a070b61007071a13480408040c00c40d000720003100943c200e050304010b5080d8400300c0d23008500d009101e0742d41c1c1c44034402d0182000040e07900c0709010400c0c0c140940c03108000f546c004201c00c0403034a446824412603030042c020107000074205428003001000099403039000702d91460a290400d031035210104010f20000c0c91070070190701e01e0b82001001d40c440814580400340690340100702c0c0c40c10b04034064944030018000c1d100d641c0c0f6189060000c00c1a150569400040032240420400d0307450004a000e800e00300d4014182e0b03072400325008a10101ca51200e503001518100742e80742c0c00300040161000c180d83c00313400e00c01020b0b59415050286409054000f0300103260405c015040c020140d803010200464100e41d00455000006000341d60300804100301c04144100203500d81 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 999721537 1250 999720287 999720299
    0x130e032101050a06050c0f06040f11040c1707140c0106060809060f04031d18040b01050607020a09091410150f0b1210080102070f060b0f091f0306060e070809010204 72
    0x2412a81c1305080401c03c0201d003c10346c0b00c4080c40070b214150b0032401101c0035401c042c00d00b4040e50b00075035800c4540032040c554507052070030b103402000c8044180c0e0704c6a100b560140c0211004d5042d0050010f0204207a0862070f514112001c1f001e401c40242000c000520700d801d0904c0900b01c00c6002d40104001c0d48408100000a81c3c3d500815620560604d0403141c03d05032030320030f40600009851110748c401c01644480440c1c002c0085114440ca024015949903640d0301e000740003181c482c03007102a400a20b038800070311844e0090f17088800103600c107241907400c030304c10940400c0c2058078013207006000d03030b031140140e44210005000150140207000209040f4a180220f085450711490002c0302200800c0340000f45c0c0ca0049500700e100501c0218001d5584450a103800207400300700110445501d40740096101a0741030000740030040b6040904502041d868501001141200740d400300005003541000120028595000e08002890f9404080009080c1000090480c510041c038845650780b051001300f140b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 999722787 1250 999721537 999721549
    0x7060e01110f0f0901020115150212090a050103050c130e04030212090a0302011d13020a12020c06130c080111030702010c0c0506060f03031e04061b03050702040209130e03210105 78
    0x70783c010304100d00d555001c141c80142d0240442840e0f4101e07100042d5000200401d1070182d10650444070b44c2681c0c81da1444038419400317406900807460704503488490a110a50103030b442190814061070900c1c0c107007811a840f802804010b42c2207070860120309000d20081540401c800c40100340c0c0a0341aa080c5605c4030301107501400f0a00c4068100040203400629070001400d522400c40c00103080205210001605100030751b000c0444ca2000610714060174261224920a03155003000060150580d900c50301403001d10782102000644031040c0000e0005810102489600c141202c280490b0383c50786040780b000ba003110000c40480040c0301c8a0310820000840104019602402c1240c82000c1110b403034020a00c1e40c040d006a1aa46048028141d151590204040d1044035030035038541003540c1120342c03101c00c0340e005004e00401240c028030645005103015006000e2056024000c0d64100f0214821141640c64100d185802c40c0c200143d2810341c200b00180485024081f00e5a50310294901808540303 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 999724037 1250 999722787 999722797
    0x131a01030b0a0513050f0c2b060b0111011e0b0f09190b0d0c0305070b07080307140702130c08012106020c03070209090d230a120b030307060e01110f 65
    0x44465500c0000452035200030846401d1144c1005c1118440076800c0c2416a8a08040104510030f203005079003a0b200c0540240c041c400600550b000442d8402c1c01e0307986601425071448d88605101f18002d01e01503100e003d04c9100ba015400782080f500c4078526421344401c07540340b480c0c2140184a10b2418084a88582070843d4000707540d540b00ca542141c0c2c205074500100030350102a60b01103841084082805291085031065a000b4002c0d240460b640e600561424492050010700348602440000e2044e070191200e145144858200a8901a171982c002140600c0300b20103001e0180e500d50302411040d920940860160a140360f2804c4800c80c00510305024060009c0c0041400d50006000e024804060050b1240b06034050101c01e00c82c1000d140d29516020800d6009000421a10300e000901c00c02d0352032001034280500f6894540050141c080303814008240000c0750454407030320f0001e5140c8040005004450045100007080314509181b0340c00c1d901c80c0640072905400501c509040008080d003228 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 999725287 1250 999724037 999724051
    0x7030f050a0c0b0c1608030603060a050f0a0c050405040e0610060e0102030717040f0f1502060105090c0309070b03130c120c18090515060f100e04020a090e131a01030b 73
    0x1c6140e0b071942a21004c1348900200c1549015661061a08202541c2d001d5400343d1403c40136907010380d40b1522000c00702c03103081700c090300803c6241000c10a45202540134850f141c0740741c50100d20b460b4454012409840903404200400d40c8800204445007250380c007100041e01851420701051190000000d40d03a024100014000308418110000980481c004480c010242e41f440c243c12070380c2e00e003070840d15405103109d0b211004802c00310408010f4030210307035181070b503000810b18040b9445218429140d500001c00d01d20903840b802c80e002c1001681100039506c90021010012806a03c80c60281c41582c0315074483c03d18404001c50010000348030180748815116841c000421079044c0c07202a0020b0443c044000c0c1c6203010300e055410303012450282440c400c000503075443c40840340072001c1c09a0082c0305240c0e4000180c0300d07501307142c961800341c0084c40840c6262801c00109501d0307022207a40d170036041c0c1d800c0b00c602071105002c1c2c007007102c500101c0000c1d840d402c0c8005000e61654a400303030031700d8000b0191 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 999726537 1250 999725287 999725303
    0xc1c060b0f132a1e05160f021801030516062f100203090a030e0f010e01032c0705040c080108030304060b010c29090316060513021507030f050a0c 64
    0x380000c014a40d0000c98402901c9801d604030402007401516840e02c0d00c0360444c5070140560010f0300140120201c444031001c0072001640c1d12095191241080300500c0d041768048001240c2030902c0c5007070381c081c0c0e011314090005824210419411803401c000030740d01103002d12035500300c2020080d00c9180c1d03400c440040500344403140d212858000f8204080c140c0008034040c408000e20400e40d00005a208a1521940380e9080341e0301d8641c10481c001401c08001800a00c0c0055a103102d0f5201750401030503034642c0c8891054002010200c180a039400b0014011213500441d0200301314a45809068581961824040d00c25410007a2141e1207200041000c2c01d46512903164500b1a403013102c1c201070040e00080f482c80c100c40010a01180380300b00a81440b014000762005c1410b41d60003000300e030701c2c10003507000380004540e46030b5600002e028010b04490b46191108140405603c07407680c4080d0203d4416030040e41c403800d52501074030f06500e01c0d10040400100380500e81d000c9400c280c0b4061110b400003c2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 999727787 1250 999726537 999726551
    0x100c0c0909080f040312030b040b030606010c060b030f061e01081b1512090c0102010c05070b0a0207080304150f061202010c0c05210c0907200c1c060b0f13 68
    0x11040c2c0c80d12a80116141c1860005400401d01c410302d8088240c0710055501071141181150400c020b0300e028000040e816004140401d44135030017030304c01703201203440b40f20040313425416000020305041c2c40780030b6260705800580070450507901014140030b4500e140c001c50241541007038440c5a40700310441141c92021103078001100c1e00c0d075485880c413031083e540c0d4031a11f50352001c081d03c6c6445104255404c6042d4031429802e00107943c01030196000d41d0006680d150b090080f240c41d0f01d100300c0c0c0054665035115908000f0ba01c00700b090f000007036200310301409051034800c00043e054000c07210396071034541d1302a2a219081c40048140b0070072182c1d1540902c1c0400ea03d07020f90608407035480b45580441ea11640c550401110318448030101031141c04032505030f5840145500500610036021242000018100f80f20a04030082d01e0a01005000c940e008841d410fa00e90008151307a4a414a24a91404a82d101e00d1040144902232040c04030350585108402c0407006000c20301c100c05103580c101c6100e4441304 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 999729037 1250 999727787 999727793
    0x3070f0819090612090506150406030803090a03090f08030405121e07050301060b090307060302070302101e060801024b030f01050613030f02060720100c0c0909 70
    0x107803030381d41d2901e140315504040341c89405001100e10b4891040403038525134040044800354400c01801c2500080a8034159544007a8201142250b07951954480ea652001001040061020314404d46c2170b240104112522420080c08104c0940d010089a4405070020701107424084241c0307003218000e6507544513606000300500e08160719610a10010b02030b0090001c00c2941c0020003608542080c0e00800207151221220302840c0300c0c2544594040c0d010100801c050743c420340c024507001b4041d10599140f100489110b00c2640c06c5d060503282c144540342607d4840700098401d01000f0180500210300d852182c0f1000450001010341d01c070090320036802143d0a110313009104030038581a840c03c41940300041015100c2c2500161220115801807100110300c60401d8400c465400340d08456901d0380d585199a03903880f041c201da80c101d0704004144540d000040311080440d40c080700703071081d0303035400c111110511200400707000d405c8041108081c002402718401e001c1403010795080c2c81c008240000b60f81 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 999730287 1250 999729037 999729053
    0x131502100203060a03120f0e04140414340603020301060c0b18010c0206040b06030708061330020f191401022a070605041d092a040f0e03070f 62
    0x43d01c05001045041c1d5007140303c60340425900c4d0007031400c0e08e43d000c60341507060134842103500b00c00c10940c079104c1c00c1c2d000c9004569175075101c482c0c44081900700d440d601076980007503400241010441c030303c0c4070003030114a000c0905903009101406542c1740c214250340c03400e20010201051035201402180c984400705030554031101c0310030a221010002481100c012103402550790001300d80a5404240070004181d0ba4600400c0343c0c406c842144009082d903840304020001d2040c0314581c1294181801e8101100c503000d0780e955149140701c065031100244a5108001c1c0c10224003022202042d00918940c00070158009648940e01ea000440300080f419400d58041c028407814000b040803511300f801c1280c11030805880c000f0700d482003000717803074101c0d59881d0180d0b030380e01a41c00b0340d2190030034015001c0be030103100e100c24540c0007015000f240c3c15540c0c4641100c000544091020100c0000c12043d1a010b0602f070042c898080520002048584854404513842c0c1c001c01800612030341c00d10180304103108400c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 999731537 1250 999730287 999730289
    0x7080f0a1802030601151404050f10170114031c02030d0e0102090603130c0801050f071b120519050f1b070918200a09050606120903131502100203060a 66
    0x1600712480c6584404980d911001c06105006c0001d109801e401500800d550640c1e04641001e0007000c4243e074684100681c00305107020b08030400c00d0a14280781003202d01c0303501d10b0081074070086100304190003c2c281820548860011801d04c1001c0700c045410301d03070010032641403071002d80c0000780d001c2d0300e180c174140644501003956500c074401206101090007910000d800b054480e03035052414a41d5031000c0c500b45c0703400700da041084822000c0006d101e940903541500032444000e0b001e40d00680259030315201314414028420004001051540140c5a0300400c84140b142d10700b07005003000392240b40303507a0501c00d0712059240d900305200c0310303110942c3c204100d5010340740039403007440000d174201c0c40c0c84400c00b0710741d6081e02d006c840b04040c80c401252510180c0314006014003041d0303140307003045034203c0548006004035170401d41c2000302c0e03454035040304003840c041c03e0300320301450b904c0c0d95480d40c0201070003c130b41003d80c50540300c040a1300e885400003228440c0030025080980ca980e51500042c04203880d07 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 999732787 1250 999731537 999731539
    0x7182106050a1b0804030903020d230105041203140115110a2907120b0a0b070b0f0f01180513020604090e070f0b090f03011d0a030807080f0a1802 64
    0xd040601585214075000310700002800a0f00950b40380380725104443c10507050380c004d008140003c4c81070000d41001940014042d0054100c03241d02c0603032034142c21185c007a84860440e140d540e00280000c1119981d501140c441c968039041c0800704058003400310b00b04040c404d1103440b014003031805081902075a1141d00d01c1c0c00301425201050300ba0304012500104200c4580708c0075102d8001140c02950802c8105d000ea5038544c0c89400302c05a4644910080136100c03a00c0c0d502030080c0c040062440c00390001025000d1148440201c0d0703007803140004040c2a00a80340302515042140180112511040590880280010701013040c1e1281411820114001c5601035008000098042000c5110350003000101c040c0c6e0044a4600b40c0c0c800c030810604445000b112140b6000b04488400303403500340d2030b20398002d500600000311107040030303140d40080311030540080194000001000a0581000f08035600c2401420700e0601c0b440e20102801220703000134080301200d83d55500610017001c040c5619030311a54 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 999734037 1250 999732787 999732791
    0x61804050f0a030c03080f012301110d11070905090303061306080706051801020f250b0d09030f1803030f23030105040b0a14061b0304030b06040507182106 68
    0xba98140200010036031482540400c80c3d10020600c4502c1c0a51841e04840d402c52503103500b05038292028148842601043d8104655040680c1490380c0601c850024070703284d82c41d11407801d00e0058180781000c0d50b070303401200034503e80010428400000f0081701d5122108440101c00403004c0d070180402800f054009120038800e6460100c0e04640001c020321303044501c00c085d9484610a40012661036a8a040800803608034101c070010a480b01d54412940100034175041c041d03140c036441601807940007050000c03903071500c2380c0751002031580190b801005011340e46000241c8413070304a50940340ca00c41c3c0c0300060811003242c070f000c1c16483c85442405000d07007035440e00c00602007409442480b281c01c2806042d120358034040707602c2c06a00d440010802214045d910b0b54859882900070044581c000381e044100448841c00c0751040c02d00180010005107100301000c07402818004244000c4400040014080c8100c04100500c454800789014080f240320086240309450028800d1020b405080d6000701a68 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 999735287 1250 999734037 999734053
    0x4080310090c08150405060d08130b0d0b01030c05030c030105090a0b0409050c04112a2404170f070f06020c030d0516020a0308070e1807020c0a0e061804050f 69
    0x582c0c046012402013840039059107a80c0d2030541084201ca1082d80d000343d0000c150b04c560300009a806000c0c100108008031581c141549d540d2161031242c0c4004240c0c1610741d07407114103460641e058070404101f22000d00c1c059085103481d03080c009075880180070b49031141c50180006030610700785401c4a5554030000c1c106000c202c0c1a40b4210781e0301c072a460300c9103202e181040c2c80c0c846041c0f168010b5805180d115080d40018120030050b50a121500d03a80c070340001d0094900311402103011046440c5014103011180c482c40c13500d401c011044c1700003c03680c3c21100030200503031018001140252009075402c40e030301480c25003030b03460a20004c0c8911035542010340400300340507122034800c0c0c0c08984100f1a500408400c841c0c0702c60f04a0711000c0440c002008602d07120302107012a845003541c9401c1c020301810310110040ca4268007600350104039080710060344811620002c5040894000c07004200050344010301c1c2c10141c0c0000c20170321b5031143c4201d100e1308003400203050100400501c007142d100401964905 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 999736537 1250 999735287 999735311
    0x60123060a12060b1803070b0f0a260c07030f0f09050616020a0902040303020c15250606230109060912110604080105061c030816030207120206010815010302090408031009 75
    0x8201c501409520a00030f8039800600b24081402700d8861400c00d1266501d8124031483c203035003140620144210903000a920b00070300403004a1210b010351854a0756940790074a47c94028103240c69484074000704a06560408809608100403009aa17001c4502680380c115444038135002d186140e0010f58080e103141b0f800100340701154010310507240284e00b030369a800310502c18030158880c8800310040702c900411040c3e40212120366006840b040010b101b0580700d03d41e40f0703403034196103007500f0551100d140c501a40c0040d82009008038101c3c0f50030f0810000681c68254094010038042c0708028160101c0607510003040350042c280b20b000c92000700403545580d110302c081d9008000c00c81c1d0b0a030148035024a1607540f03104090504501e5a03050f030382e080150366419141c2d64006086640c020a154081c000c4c0400525642c0280582000350341c000c1c0640d47c50451075500c0c0441c40560003192040440c01880981c40b03c03041c7c15401070700418120341e030392506944842d55030515030000010601d089655145 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 999737787 1250 999736537 999736567
    0x10050c0a03090f050103050114091b0706021206031f050603010209030a06091a090303010b07031b0303150b0403150924020307031a030a1101031d060123060a12060b 72
    0x42d100c9005401612135103420040d002c07076a003130055a40d80c01080c44113416030b00e01541016070202407030680c0004c2360000506541580c001d0541103c04076000f040100da00d49880303502c6680a1011401401c04414414400c000c0040e40c500004821381c8800c0010000e4400350100e4030b0201d030140442d8058030950401100074019074608403403035014146a0034566006043c060700a9841101840c41c40c2d1a08111700c015a002060403401d100780182003080c03400d02880009901c0d40280c40108016120100039680a14183c01043d0000000d120500202e02c0030b000da40d400c81d40149000800400b107003801ca40800c0d14510b8645031244a09070301c1640c8810780c0145000304c4642d1801d20440c43c04403100c680046200a1030303601a40103d55601c0400c9400318550001241070400140c2922041c281034418001d0048080c034640c40800104a441c00c0001a034036001e1001110901c1d001e840400508603103d13007041c5c1d4080202d220078101105807690701c1a40244042020705a498800c102c15400b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 999739037 1250 999737787 999737789
    0x703180b07050105100f030305160203120d0e0c1504031b090e2a180a060e10030b060612040f06020c1006030320071e030602121603061410050c0a0309 66
    0x4060040304005130000b100e4006c401aa0b43c5600d4060509541d6483d424462000082c2640c0c18480d203845845141c400c07200810b8130b032115400c0854072440740c0c0740051a1001d401142d86c0240e5503010300c0f00f061105101500c0a6951101c0c3c0780b0f4540c1c6407294030713100c0d0501d10340041141e42c0c075109020f402000e0003e00c000074400400640c1000800c04007a80502c0b00b440810245c1112465061076605882103076281da1044681000013805501c1c0c87c0413611000d02110082008690100140140040a03c030039621440449080746020708031484140ca2a002a000818200e000d9141c0820854107406444010703003248100c4a014108641c5000906481d1005602080004022103070003401080f6101c4d03a440c01c00000d080092518080d403e0f00c03d1341d02d922001030180d0300d00200006219000034901b80c181003440b1305031410710385203900c04801c0c400402c400307040c40c001c1c040040405564020716001d03010bc6840d004444440800c2d9664465024140d03c41c3c09440111002c040d0800803401c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 999740287 1250 999739037 999739051
    0x161202010c12081f06050a050a12090c082806110c1c0e100e09090309040603060203040209060a1404050c12130320030306060a02011b08160e060703180b07050105 71
    0x165044e940312030803144007640f4000c03000010b50070850117202d58055001403034500b0360303403815501542d909030041c1c0c115058400c04403019203140200b000218010407101400700c09030452402ca4103440c0c18002034000e0b5448004109985072141c0030800800101681c0c080c1c0300c810191201c0c4a44a08100316244000c0d03036020200c0d441005c1c1403400c4c24400400d003602c0035182c440c0313094051100c040003908140103194602d144003c026a0b009600c2d14020306c0003c521036000035889040c17500c10404c130343c41c006240c20702415036203030304001c030342c25019950620381c1e81034400150b25250180f40b032940744918400c403040f407841441400300201014003004070380c40c000d50b200b0804018042c12880c071103d00604d168a40d0780180081841031411000610541c0c545000004208100411075112440d8007a81d440c040340c90300341041801c291455184c1c0d010406807400002d409818030004502e4090f01002034100301240088441e880d2032880300c80007071300c0421060380d140c1c07590b450024081c00d0201c44003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 999741537 1250 999740287 999740311
    0x1401030b12240f0f090c031b030c0121020f04030204020c1b04021905092815080606040e0a09061b0908061003030804081201120201030c02161202010c1208 68
    0x982c1042040d400c442d0003a000e0294068480c1c07200198481c2c40c800240c81c510f007a014818039414641c0d000c00040c8070b404080ca55012440c000303a420941081d81c240d01e10341c1800091408070002010609400402d84104034006031a64030403c0c0c020580e02403078000035007283c4005082107121307100041c280704486501000381d04000c0d0140500040e0302580584070b2400108190100044e401035000e8005084d01400c2002481555952010a403d002d106144000b00e4060203111000a454031240186c1e000d040c83d07240e03810104c001c201c65104901c2180d29034007400002c6501d2000641012264980122090200a81100d80f0342011200c94864002050245200007080032011600a10030149080321003d801c0ca15203082c2c8941c0c00040044901020802c07201e02f40c200600742d00e80c00780061601c41d0020b4801480098200d42b142d01c0c0700b0f019940034030091055071000c00002400d890702ca1200650040c2140b005a0752808904002080510b4010500207860b60264009108403224400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 999742787 1250 999741537 999741583
    0x4030f05160f1425090221010608061f020d0806011224081513020d0b0108070f080309091f260c060a020a08070c030803040c1a0f041401030b12 63
    0x3100c1e800401d00e108034145004421000c000c8017400c4e80c084d004d5083c000040920402030150b880080c0c0c1000d0f004900441c00800903c8003e0410b18000b0f00d02d08000b49001e00000c59101d8013035034442c5034040003070800000300c00246080e40310f800540c2052030304079020b006440e40c1d40d104442840300101803140d42009000000350700c480000e42d028200a504101005a40725019840c000c1074103454103a81051040710400001015100140e0003040808060030482c3d0400c240848079000b51340c01404154030600542c03180b84d456140c0f080e00030380d0441d002c0010304400c4001c15111107003036103d4048001c0c3c40c803a9039107183c0e98030700e102c80700018582130301c6803115290208801c031301a8120700b00040c2d0141d800c5800003040640104045401000c85030140b940d0795862890591003180c0440305c25145603410042d00c05082000c1d08030424510700141000019141582c250140c0d10070700c80151000c46030143c080e4000d500c00241ca07140508459840714010001030703a9140141e030400960255032207 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 999744037 1250 999742787 999742813
    0x1050106082406070f0f030302040504140402090f0721050612031207140720012c061e0c030a02100b0108040b2e0e0f04030f05160f14 59
    0x15110101403074884641100702d01d040b083c802c41e078002441c11103040c500394034403002007060742c520030104920035a000343e500e60401041c401542c3c02200382d0403070918400240001a0345440350300303074000c0c0e072a8014800f5071ba07003580440310035406008900a5401d030351440503900029400c1a03210741000e0f501d044005181070025507a0b1702c100040003031250b1070140401c001c28400c0c205800d15a95082106052500341d03150b06444003203075114480c540c031503440c000208d560000345031010b04c0b40070400f00498580c4540460702034203d80804600c0b80f20000b4080c6c210081448100d00003265144405460310090b8040642d93e900480c1100058800d11800c80c01298542c020f42d0700d2007406039147d80c625111542c03910960300d0701810900c48200c03466400c8140d03643c885120820320fa0322102020180785444101c07040c450001d40f004417003064007410400466040400c90346410a80d14142d0b0f40c0d0304d00031780090305e1000e00000003091810302500036000d0080258202006540210075580c0c0c44903012 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 999745287 1250 999744037 999744061
    0x20304060908160b060a0803031b0408010213060305090a05070504230c0301030302100515060711300319081e090601030b01150f03050910090807142a120f0105010608 73
    0x8400d00207642e108000044190034031a60020310302c2b4041c8070304c900f0503486030f1645003660403103880e81d6031082c4014000c01c0240d9040c0107468210500d000a0100103405459154591205000340382c041e913100c1008140c2ca0b285420070000c1080302c101441d00600301201110490fa200307100690041c4102c0e00390500d1026a889104c1c00f645092048942c040e07141028002d060300410303419a10f0307040b48000d801c01c83c1c0742c0c4100301d03511403032000d0500c0d142c0b43c42403462a030061149803a0410f5a0052164441a401c00840713640b450584e0b087c0aa0a0703901d5541d40c45680282c40c06814141c0d1138034040c41742e40d050006109069a21520b924803042c0c0c1c072400144080300e0b080c0f035000c0c001740c0c0c204080c4540501030b6014035000901401036944410741061501e0a503100c0d180704807013034040016408144042c03240c1000902150b40007800b540d03c400380007003e003049007984600351a4294201c022007961140008000d002540040d1080c107150704140f0740c002c05092141802080081000903040c480d42 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 999746537 1250 999745287 999745289
    0x1206030c1c0b04080c0d030e0d050c03041202060c0706050d14090307120212310f0b090103091a0610020d020718090c08250e0604020304060908160b060a 67
    0x2614000203400307000d8031000e611980103071080c0c950a20400401400b07040901030361651045545021883c00301c065292403034070312510800c0c02007040a020840001c803010049170100c40c0c180e04019103010f29400040c40900c140362481000780301d07110001030091b42140280c4070f2944500750820102002c100b0618010384200c2e00d00845030810072400c000205003000310890344886104890745500f070380b03036027600560004001c03169a05142c1c200149180d07018044e04100d500340c00010602c18a802030301701600005d4058414681c00c003007040d4100743d129901402006401c03070402012100a0b84090300c03004410384e11940902141134080d4051800000d0000c0d03d240c075507006207121403030100800c400f0b010640b03941d04410780700c03403000003c0365a0300382c040050704a02025141e00c00403503010700a018480d00c0200d09a0269543c104002070365085010361142082c2c601598030703921071810000500e82d002004265041c0490004002000848072208003886102d01096684812040208008035 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 999747787 1250 999746537 999746569
    0x90e010801110d1a0a182702060f0c0a060b03192001110d02010c09060807020d0804030c020901030803011503090b0601270303051905090f04021605031206030c 70
    0x420070402031104030759070001c01e1001002135095000c409030310001e80741e4116940080100c444090000e8079030700c3c09105410301e000071606003103210712000030b6a40c5041d2551401910803140482c6c94003440503008225020540400242d8252072000c1c41d042d001446e880e12958080e201789850304c0041c03001c880c100c9840301d40000d03091048100240c4c0380c042d015480c2e500c0030304121008d80e01d95803010742045031041c075000350b40010541d258848001403c820066001c501041a400c090103c2c590b004140b101001c000391521011640c3c8a042c00c0d00c500c00d0b0460001d40000099000009000c516000396040c3c5500054549240c640302c0d50440a9800c42d150181062030400c010426940c082e090004e03407105441030b0110005449200c10324020160703030095000c40e0000894a454040c0c0000b481c010988606007141003451841c04a0202400c282044d402130341d0005021148007090b004a1004507030110441e0741d40e06a000b2052011038056415070b000744038482c8a04180c0c0742805050607031100b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 999749037 1250 999747787 999747821
    0xf03010f0b0c1e0f07080105062d062b140901092307030209090a1e0503032e0303110601050f0d0f0809130b0a05010f090b0715050106090e010801 64
    0xb2420780780c0b00820f040010f58000c54481d60f00020407010090107a0300040c501c68000242d0792418206101410070b160280207181c03204621172907201c460420304400c80d66020b6400340e849206803c10608038a15262030441c40ea21a045080303d4020a50820b03a181400e0041021050f140c2c0305940382a680120700080140c00c01c04c440c4c2592003144040421100144400c465410380e44e60081000100142e43c1d50f0200d0300a4000e900c1440741000c44c10491102d11164801071403403640751661240030240403081d41c02d45c10307000810300400e00406100c1028941c004140856524a4040d0812800148940e10340c0100d500024503450403018008400e64003400d0070420065542d2110120001070708105c0300303107105110210301c07903c554038441155244a40d00203401c29501080180040107540454100070b1124019082e0550066016080303512150307138141c41e590a0b01c0e105000c2000b4001e440c40e09071400000185440e0703c00325082c201c8030403d86402040e62030712a254241c5e58141c8080820038 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 999750287 1250 999749037 999749053
    0x30f0f0917010213030c080d080c090f0a0b030702160b0406051b12030c0307110109200d050123010609060e060306120d030b01030c08010e010b0c10020f03010f0b0c 72
    0x1003810401ea0808540c600c0006103482d18420754185941000e4200355050a4816800e1103401020004070a0084d12030400004924104400c030b00d4038428800c0960203411000c19181e40b43e2a9464001c1c080c100151030291280b03803004000b5503d100c1c00c804a03400c086203610020341c42104500f102e080d56019070303c0394500084102c86602100d0182141102d070300c2030a00d0302818145440256014540703840050741e0301c0c1020007000b8003480c1204203c00c4075034900100d610000711245007003154004903016907003440300c0880006e216032900c150050015405e0200180d4102c45039810105106412540c1d6081640c0315402102e84c403129014110200d0050200c201c400c0c642003015586c0408001d181c8105e4a41a21640e03041c00c040f100f4000c007003a100c6410311190360b058052048002c1861030031280c5585004050955041e062182110031080081d179103441d04010710046010303c2c001c00c402e540e41c141c9011551501d50091181c2011440c1040000c10302031f411000311171030b042940700144445 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 999751537 1250 999750287 999750299
    0x62205120c16091d0c0d170f030c07030816120f020f07110112090b040228030f050709091a0603030405030f07030b1005031002030604091a04030f0f09 66
    0x241c0c0c0107401402480c499070340e4440307290001c0a4020043c040440000c41c2001480e52800b49918405502004d00d4000d031071300b102c1030340b03d400300e0011450300107614174800c5a0445501981e8800c060041403000d02c00410400380c04c52179801414075900c2503489000c5c0e951001d0840b001c101070300106000080c1c1c07510500001c0c2d00183c21600808110500040c9845001c2c401c0c8030003a0b20150048032404041c0d000c0c45590744c1c01800d00103d0211411062240740e40d00c1d526403c1611008000138419151990030040408130300d511100d6001c601d14420410fa9145e040801c541081030b0b070102c980e88500123000c50142900c1c0100c00300c89600652203140f402c2300b60030000254500070003c540501c003e100015043d83d080000340320034020103000e043c400d030840c209004a80c8008044119100c41c0e03480400040c2c400050ba02c8100000d0400107850f030b1101000580549400300307001e0203011007941845482c100f1420b030140a0762282d00c0321b0618800b207000665110303008201c840d000c540022020801 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 999752787 1250 999751537 999751573
    0x60503032205100f030203071b0b0f01061b02190509090a0b01090207032c10050d0605040b0d0f0804030605252f0f0102040b0403030f021f0f0902030f062205 69
    0x4900e03080c004010b003214085240c0072449d21100381c81084c0628184024103d66030b45e05805003c0d646004602e988000c0700c1100040800003000f40945003030021600c00c1d4041c5413012000e494001c000039143d0a02c60b00ca55942c4042035000e45140842000025110342c0074401ca60b010355054035500300304001c234141206a50040402c0c1100b000c0c0101c11440740740c1d20080300c1d08001c05552985030300c803403010f421a030403160103803c8203000d00c6c83d05009080a5031000441240a0b40c0405100074000c40d03440e0070b1f45240526131004002d24105014400348000e4074121007225889403040c05200500f051342116881c03c000140c4140d10b08803c4121800440344031300c0000000c00b802241c02c000c011038002c0342240d001da488803400080206041c002c150303020345140031210291000f0420703000700030325400d410420014001180b50b52000111a41d03410b80d00705144440c3c004050301d2854858040305600c4140880f1144004909000c01c000f0401340c401d06000c0345508500100510b03840000718442c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 999754037 1250 999752787 999752791
    0x130203011a031e0a15050f090a0b0a03060e030a32030606070f11030c0d0b0f0402150328092f1f021b031f060503032205100f030203 58
    0x71401600d9480c03843c9803000e502c0124016420b9000004100c1d40051050509844580015119240140954107d43c0c0c90402058000202d0240000d4900700480054503081440d40024812400d12a1240322003002101400813440d0a8030b071480030410150110114401140c0311005400c03800e02c4401c59022007002135a4010030280c00e06240444e030b41c4881c40740c5421100300315695880c004a102c52800c0c00d2090020b0080140e694580c3c071215580da401c40c00c440100343c400b203450000001019580c0310a101c10321100507018895481c2001c5128030710684808520385a1411180044c1921450030700c2000706142c0c10990008040e0050b000d100003250300901d01654881c64000080300b65640d000d0300411503084070098000284425802070b090100341e5034601a200c001c0209004107480202c0d040100e041046294240c5640c5420000c00512035a04165098403000c100c140501906007d5a4586e80021400d0dd202540c2c1e9420441c080d184010319100244080610710a031034000d0b00039503 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 999755287 1250 999754037 999754051
    0x121205061e010905220b2b020307150f09062a11040c0507060b030703030f0e0310020c070303110a0c0b0c01110d020a170705040b07111002010902130203011a03 70
    0x9424640c0d42e0002036a1003400d5100c00c0307400b642410354684402c0c003c0c4500071140000b620003040347e451382ca88030703104c42d5444444114181c050001010840d03405020450240c5005600a84c24158900004040b8040000c04502007030003002c0c04207071540506480d580b0080490b003110b24051034000c2e8041900110b4404584081c4000320401d46a96140255440d0010719502c80d80c50740c019040039420380b4440310215001c2e030032104090002c01d500c203102c1d035001c0c6000d04000c0c02010502c0c010031724103402c070000c8000107440868030704107500b40400e8502c101c82c065a074402c1e064030401c04075511065105130090403180102400c011842d016030240c0f0100211400004203500051004c5429501051101110790ba00041d03403c14144c21010304d101d84003468690450a240000020b41648580d0050907020326011600200304103e50070b000c040b02c01d02030b02084090898031f10203400b070f004c1044220302c0340350000d00000e24800e8034420f490480d07240d28001500343e805c03001707400b1103940003a01203 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 999756537 1250 999755287 999755297
    0x1003080315060f04030b090712120302030c12090d020c04020f0d090516030507050108010e150f060c0f0d080106020d080a0903030b04090b060a06030204030537121205061e01 76
    0xc480380300c143c0d07406080110302540e0034090314545054468140700c2e00d90809018038003050300c540040b80c40341840e40239284060a0069886d2540b0f070314041c4500400007504141e0320180f0401490034004070304a0880240c503002c41d405044179004200507801024680e480c0101c3c01e100503502c48040d82c0103e41e100d40190141c82d0400d0700e80a1840b071440c44c41e04180d505e6400403d0401c9656840000d0500400026050360740500303049404051138603200c502c407031081c1d0300c0039040c1c035580d90780c9811140c0010f40c950031140e4450052003000d032070308100b0354001d000c81c200b80000604e050000c01c602800308003070380d0b8161180d5181d010110041200d03000640800d80e503405983c2081c6c45501c501c00345940584038404040c5032038010000bc815440c0c10007000c160060200f040000c0c0b00240364000c442c0302031004a02c6a9441c8060720308550291900c0010b11802c81c461b90034000301201c103412221059603892070b400a03812441c01590000da17080c1d50070410000d00a5030024006584a203803c4052400c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 999757787 1250 999756537 999756547
    0xc141608040e010f1e120b0a11120a0f02070b041403040312080603100c1407110306040b220f150f0f02120916150e0306130308100308031506 62
    0x25070010442c00340c000301e0004410303071030610445000200c0482201c3e00d1100c04c818990074000240030f1070640010013400da08240010410411309504280390007030701101201e450f42e185000307c1c50b40d150159144200c10740303098507000700c510150084440580d0804098502e40e205c0d60f4554010381200a20500715000901001c4001281090360500900b8103035204010790422074105828940c00031040d81c001880c0c107408085040d0000f06d42103103440d000c5445902c41507542400081940000302c55a4540074a000b003004101c60008a607010308041c000b0943c40d40d0003c0d81c0328a14148840d000f80403240754980c00800200701c1030102041040625020136121001d079182400d443c403103551104860303004220700000ca0480100c180c0d11402400c01040c400382c8400c80312005010034001c0b0714556840403900144540600c0b4030350f43d5907502808031a5a86030903032800000c0000c420080380087d0b00d05021170b082c14407a84a0300c0c10707207401c00744003450b544820303082c0d2110880d4044aaa0040c00901c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 999759037 1250 999757787 999757799
    0x30915091e09070906020715030603120c35030603030c0a2a12030c0305040b04030818090f0a020a021501030507062304050616240c14160804 62
    0x18080c00309000406609010014440c1048103400004010307004000c4c4078201000826800a000e008488005603211080480078504801070041a00003526a184515110001c1d99000c020245c02900480c8030650300304040d10441041d01c0c4a18130301c0c10700c1c500310881d1420030040000031a0019002400c6915000001a5103401d062541c941901c86030000c4040c0b001c41012034074031035005e00b10580d0591403181800f0750301c5000e00c2440000740400a801c900c038820103024038102c50261240c850f0a98a903641c902e010681e95200c40026114010030112a154609000340d28a0003284080040d000b15514911884025000f0f03110010031480b03400390716982c488502517581d0185001e9005054a01e04002d13003d440c0ca01c4a51640c1c91600d00300760b04412a12582c0140c50684004880c166078408201c403c0d6411400382d1400944178140241c80c442140701c841c168204030440545d001c1c40b442c15190710503600c59800e4100080e54034000c1082d43e007200c040400c1075004903c42c60200b13007010f480719 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 999760287 1250 999759037 999759049
    0xc070605180904110405060102030901091802040e0901020a0215061c06110c0f0601050906101d060f070213020406230c06090a03021b1807021e0304062003091509 71
    0x2507030070369134901603182640241c14640211680a1020300045150031010310000b015aa642d104d02c0341084d095180e0041d110b1010b40487d80185186030145a15042400800b4000e600c0805508003602c44c040310200c1080001c1d540f50711400c0005d01a00310041036070080b15520600b050100d4005a40d107500c9403e800c4076034090140040124000d0403c0018041d03828079049040c0c00c0a4480c00d4500c040181c19502c20b00070442064003450f0a44840031032502c2d03c0c800b1082400140e900141c042071216004040d600606040f03070080305c0c00c81040149144610881c4078034050600003031384500c41803d080504d0700182220b0745100105914011160030500d0a01c0d074140c2d982541c80e08045054010f15904000c02c80d00710b0100038841d500d0b2125000068440e0640b6590306811602810000e02400c0c004d02441c000c0480c44c201401c0c004c0442080503840b5403041c025080801e9505004503116a00c070782d100c86072032110f00d00452503d0004404c010444590700700c2d82d90058010090048207807a40 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 999761537 1250 999760287 999760291
    0x30504090e10020a090f0f03121116030812150102191e030e1905030c040b190308130602120a050f0f12012c01060e130e070512030c0706051809 63
    0xe07942c0e031072400c0e00b03250710f085135421b56500c2a45442000c0e542800416241101500f00c45864144841c0b900030300310216042401c1031a104148021860001060207079880040c03000d070303140c001d4091040d924003115045000c160441c3c5401a4010011221424074046400e15621b01a01c140d0044140341600c00e144110075040880006041460f525170a0624400c1080105010180300c1006420500400c0e5a6a010600503128030303191600d101107511038120342004940c0903c0004c43c81520390902e1102940501c112a090540d050000a440c600c0411103000c140021001070b840c0013418542150150040c410400414008000c440400d000d0900244045e00c444040081c46614102e41ca6004014140001424242d075004440d03000315440f046a040d01c85a013450764942c4c5400003c2614440b01d4005107a9840c03074600b100b04a201c000a00004072075045a4448800c0440714034252032303000e005200034581d80000011b0143c2d40c040c40c06444a84003481d40307441030241003c0065114001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 999762787 1250 999761537 999761557
    0x308130504060f2d030b13050f0c060f0a1404030609030f1706040e07080d0909061a0a030e0c150c070605032a070803100608090109030504090e1002 65
    0x102a0041140781018052100102400c001485540d03151259012200e0090081150698100403645140c0ca14a42c0c6220146030040c00d124a81d1030031404145034010707021800e64092050460100c56000300065011541030060859814000c1403031255078a600040050b00512040200c031220301d441c1c0401400086000310b074003050400e80790501a0003c11424000c20800520030300050407200100307486908200c05440010313900d0003404080d4104010794210508601840815100e00c1c0e038441e0f001002d50340740380000c014855580d00d030390031400c1040e4092203082400780507180450303000303034400d84910702d103003080d00e560a0a8400007024083c6030138203440810004158070001d40d80810410001c1c0040341819840c0d410305034400b0050001b9105080c2007c00403401e0750407070009a0044d00c4c0030070751082040340c803820030044c03140c141c91841c010031000681c1e00000a03600d003014007600b000203425407074184c940390801f080d181c00342c22140c10030b040718030034200103440c600c03d503200070400d07041 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 999764037 1250 999762787 999762817
    0x20706021b03120a060f180b041d0f070303020616030b090f0114041e020c12030f1803030609060f180a020a0306120b13020118091407030507020a030809070308 70
    0x11840850403c50030300034041c20300c4149003200621404902c60304120948a0103004040d0400c00301110030081c11000c00381c1368115060180040d1501c41d20710b02c02440540307100903101546582d460081e17603803809200c0035005a00150100b0812003022503003440000c50b03845c02080e0008040c022485180c41911010020710a14004000ba0b10385940014189481141d051161505008140c000340c0180c0c198040100c0e4002070714406084104004041848403548031900e0b440d0a021035404000d04407607040c811005c581802c1e1414070044100d0f0712480780104a11040d0f1100002e06c1401002600d009030003030084c8c81721000315100700140c130784078490320900544d03280d000307500c01001e4490302d030f00c8003554640e01d521503400142c1e03618100358400d40005404100502c24001211414059010080d184401c05d8002c40e403031400790000e01d407104542a2910194680d944110708580c0100d401c0e10040e04400e0780752000034440c1c1d01452300090031400300c501c0152252994940c40c1c0c00742c509144159 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 999765287 1250 999764037 999764047
    0x170a080601030e010506150c0f33070903060b0109080f010e0d020f06040813050a031401270b0912120f0703090c09020a0c1203050a06090c12020706021b03 68
    0x50ba060040d40411038841d00280101e04102c400704a0401b4000c10880c1c00d0040480c040c0c5008804104c001c04400501080710443c0900f8040c02504104c4005454504c5800e10745007603040c000a20310700d015800c03950b0781304281859a1101801480c02e913040c84e0401656203000244001c00b004400e84003008403000151340c0c1030408001e4a00040706080c9001d5402400084080c4c450200d40603034000c0e0041e61b8640e40d0400c0428140c2140002d4005950203048174801000380002c141e00e07022078401d90b800800c0050b4039010403000c03a0f81901243c00703a070418010800000b61100180d141c000c00721400b20340100f41e2000c0c0c01261900510010103501c41600e04000c00d552001280e2901b081c0141400c00c07a40d910b6843c2e10740800e4540c0108040244c0004044040710f00c222031600805070803d8010318142660807004014010981c0c843c0640c2d410f020003ca04029144544d154911300f0782c45c0c0b0064132160308011806500050425605544d0901005507840210380200700f1007411407001c0c503070310 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 999766537 1250 999765287 999765289
    0x30a031113061d01030506060d18120504031407032001091a0d1b02031204050a120906020d0e1c021201090308011502030702240d0c090f060503060913170a0806 70
    0x1010540f502d00d8100b500340014820301d611480c0841d96007501d80e0f00041140c0c4481070211490f03000002e130040c0104c074030008041d41d10354044050003e90348145107060b900001a121316a8425444c003002d0320541c074218244910710000100a4010701041c1003202626a07103505000344450074003046621004000f0b1510f130100707014403404907a000b0300d60300e5103060810310300002c2d83c0b8040e010003124038011400224003030002c108071111545610058200c0c04004ca401c00518505080c4508000751090380300c1e075464030f0b00550000c00d000302d002c1c020040c450030700880c241e169aa14401a80c00040e11410810085003e0048140f07550007274a40c00c9881d49401000c02d0607038084511036045400c14480b81c5c0042e07407100b22200c0c0d10714080c2001103000e50121006402c910404c44070459092a025582c201c0e140c000c1070820841d40c001c81c1c2441d2041e0784440a80d1503200c102c1d0400d500841800000700d02d50000d07240c1c40056030041005641c0245280c00d44022503000280d02d00228023080304024507 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 999767787 1250 999766537 999766577
    0x9010f090609020f07020f0102030c060703020d06080312161b0809030c09040c03061a10080105101119030e091504110f09090403030f060f030c090509030a03111306 72
    0x2c05050b001140340003120440d41030f26000d071940c0244a0f1441140051083c1c0c42002602c050000601c191501c6040ca040050025804980c0842a00f400c1800006485501009032808407030312030300840316a038030060ba042480d28080110740c03d1000504031020f14540c07000505906a124440c01c0341d80d008450101882d1190304604148158500010000042e60940049007184d0f400b1401180400408050301d117450040212203400c00d03078250b810780c0c3d0590300c415254101d070400d48028046a115003000c40307405201030b8070003c540c2d021032044000449181d506803443c50080ca0015245100100041c070401d0040e62102c002c4100300c0f904011500d0107104003a040306c101d0b0400c9207000b5a0800003500c500850058511609040000600b4507000350403500610060035020061191100c205280454035800b0a4444454648011500000c14400d203402118604000e505061800400710064111001a076164070811312445c29074007031510003400030f0116038031407224280d00601100d0b0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 999769037 1250 999767787 999767789
    0x905120f030109181205092d0f09070f2001020a08160203120408130f15030b030f1f140a0b01030b0a03030f0e210609060a09020f0111010b09010f0906 66
    0x4c010042c810100000820340c000c118500c4c61a0b04095858800c0c7c0000580907000e48040b06040610003071800da5801c1c0311500302e45c0c03400d6084540c5100c10581509200c2816022280d56002c00c0c4c40070140103442d401400710500d107034260240c003100f008401000509981015000c0804540c480b010b004071a52a05001d540c014414401581020611000414601c1011f403015001620008101d00180c00b9005100040d0840d0480100110b613641c50301902201d42200307000c0020301d84a00e054162802080e80304114690740003c041c0398800d490400c00c01c9419080d09515255210032550003407050040e2070f881506d011400040710614040090103844034250001e1081d41c1802080c00020b8120421440c0c0310024030300010510699008240c000e55681e03e1148440000011030081110028800d4440c078510002e81d5415100c0d201d180381038902002c002944115a0202422194030801202c40003040300000030896104580214a5522080e0030000c0130b010042818450403101e0700400e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 999770287 1250 999769037 999769061
    0x6021c15080c0303040b220803031608060a0302040507020f0d09062715090e0903130f0b030408090d140d0908030a0909181505040605010905090d030905120f030109 72
    0x1d80718a100002a403207105d107010700c9240703a00100e8070030601b8101050700303152030302d10f1034400101c40d4991050540e17070740048840d00700f400c101e2030440c00e20621844089026a0005d8400b4080038155806c210150a0040c610310440c4134604a608007180304014440046400762101081c50f82400001011000d40030741103801031208a250702001d020744200501202c1030110503441c0340c4034083c401c4a50104660044589199040c280320903c40040010101d40701d8511940071040e65070a585000c15440d485481040300b02800050b0105094100a10700c80310003d101a480401555407007940c03400c02e13081c2440719402003030041c0c451078000e544500900613040c0118107241c410381000341a000c0c7c9005180c072a80d00c42c00e0702001d0b41407102c0c00104582e48105400b0103400d240261100600049806498840c100310002a035031040c1e2003007070300904104000d004c400116603400d50180c061500100c1c0c003481440c241c0f107140d80e003a07005094218089907500c0e41e2949000074010036904085110 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 999771537 1250 999770287 999770293
    0x130509071b0209090c100509030c1f180e07020303072a0f1502030c0a021207030804021c20040f0515271008010c02072106021c1508 58
    0x4461404003141148001650445102040313554000c492400d000d12494015008007022040c1c0d070610340c0207006454162010b404440610440004200b00e14070225039200d8006450300c11060241e00c2070078019204c07030b82454003800c01640d0310020081803d01b1101d080050308080306205c1c03c1640034030a6005c021140c0080c0d40e5072a0f20041c2d045441c184d0202c02442c10100340800e501b04545150705205c0848660340445d2280380c00d403040c0c00a0b500460309000103005030f066004c0b804041c00c055403e0507406546208180d0340d15401d2010410400c20704180c1c1e604c0e1b440d40341c070001e980c02260300d0071002586c58454a00e011042800241c4e010180b1040145013890100702c094042da040a11b00d504d800c90740d444116107806000051415588605400c1101140c208002e0b811442700c0c1004452201c4020000000084001c0b07880b0394281c05094070000321400280c1000c940c90203201c003890b004410051810080c84102075881c030394900540402c98030f40c900d4000c00b0480b4465000242031041c05 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 999772787 1250 999771537 999771557
    0xb0a02030c330603030d0917030115201507051c150f140607020d060608030a0908013b0a0b06180415050a090f0525050d111513050907 59
    0x40d880303000300c40c800702d000e503507e101800074818904200c04003205000d0f14940d507075840e0001f01c0700c0300c8042040e1402040143ea961302c40701c43c02d411502d80311074461000c1d0a41898188001d0f0f0f0882014101204108040c04112200182c0e4121a200041d81450005a140ca0a1001602e00b2810b9010301082076909004000203018080d80780b004240c00c40e406a40c0300350314400034500c0e43c14500c0240045107485004a16904004020140c0724515110581d4081e60751a481d03003070325880145101501380c00c000000400484040030310500c0100c01d1a02c610464580303464ac039041c01001d082d00d90444000920016041182600c00410700e0305005890a01d010b4488001030006685090101c90381d580025800760541d91000360a1544040495409451070900c0d640e5280420400424020070b020480d4181140d501610103c440c0544440d0f03407141035071100305141680140d5190800f081030300c4413040580c0d00005050708190001050103a41c1460700703100d00880000c20400074440a010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 999774037 1250 999772787 999772789
    0x6050108041b170102070201140a1b0510141f0806130c0b0f03090705030105191509060605040905011d040f170a0e12160b0a02030c3306 60
    0xc0aa60040d040b042003038407494140641081034055a10402020780010f546208054040d0001c14480d4000d0380c03400580b495603032682c2c0d001d2184000b140080760701d5202a41c4481c3c44010302040550050b000c0d11900c107400d18084044c0d40070300b144c072001c1c2141a410000036904014480c1030120791041c1c02440310f03007132812507a40c034000980503515031810410203800b0070071007030010405071080103461a26120b2000019075030b50802da03480780c92030060400209080c241403048a104543c502c10210205e4054035070031000b040000f51150b4a60642032010444203068042c0d040103015559031070766640e02d13140311503081341d5042c0c0207804a40c80000110350080102074000360000d80020300c100a06096140042105002e007841401c000004580021115000720544884803020741c5c1380103034085500e40385501c5150300302c5001d890946450741446084070348005001c2e170b40f14600480e031412800c3d105e01450040324560901031300001031290035180903e1180040400d1000f4105140703410924 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 999775287 1250 999774037 999774047
    0x1090e060711250302120a1203021303020a0602031c0c051b0c090103060f0e030903031209070f0e160825091707090c020d02060105040c0509060a0206010f09060501 72
    0x3030480010044031481c035944201e02806807059000b0802008400004003c0304129001e81900c000d031300c50700c24440c0303040290320045101d139107040d40445591804482070b88243c000b50408518982616010040400143c450b038250f08060101c0781c00964603084510b2022118108041019031414204107080d404203030408103640d12031546404940b10000300c80c02a5140c04580c5400c294810181e4000100340141030740a526441c80114051190b044901800c0d503807807103140c01c0550942d00070003541c203115000454603038001d01e07400161603440c0e55400c24004104050f410184e80c40c0b07855014801401855142d40d00400f000b401c2c80c00c40c5203003002c0d0010a500c0740003030042d03035881e005044c0400184205d240502130108100c1c100c04442c1c04401540c1c2d44c1440c0d002e501d03003440c81e042c0c4c451186400000c1c0081d040d103166005114981c03e0000f488040c00380003050300e062001c18800c80c0e06941c1c40c507000d001048500d0340141000c2d031420034140a8482668020b03031049140803030601150341d002c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 999776537 1250 999775287 999775291
    0x2b05042c130c1404290f010f0e1912030215060901060f030903120c17010509130807021f02010f0b06191103071205120f0c030708040f02131401090e06 66
    0xf400e842d01c1e80f00c060301c002c100a0440000c82c044068103c140704c600f0071980b61000c4182c20400e031000704280c004900107645000c038a400100101d07844a40c01da010789041101a13404c2c1511b025510407850f96000005100d43c02d5010480261300f0020110401c40c0201c0842a84042d04403210071481d45884406004070302419030313010815440700c03080420705010b02c20510700456000001c000441800c20020b02c1001d00500c001c200260001c00001e4910304584200e02421070004000540000760380d444d103840c0e209070012038000c00d540d02c034181e101c1c401903040d2346c0d1100507800101c1d03020000000501213600c01c2200b20b1080a05000300011150394489a001090075410f0004005500b203d409265005824006100300704508010300000d5001b07002c1e210070384458150f10f0068541c0185580e51031000c88002d80d142806000103001c29100f514400d81040c00380e1902074156200b43c011915503130020f1215810561a440c88201c0d07403400c100c0d1350f8010800601c0802c041001c0709400c0e0303120040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 999777787 1250 999776537 999776549
    0x32090106050f03092a01030608010b03032b060923090c04091b0b0705070b040810050c09040e030306120a0203030901030c050f180406082b05042c130c 66
    0x48009001c1000401c00600798001340d25101d1622280117000200b540c0450320301900180c10312000007400f00c0705010320003a20f07070001c0286d410850001284403104004602f0270003070361450480185018518450540644a0b58001182d85001c48941c40c44182e084000c1c500d14010100c1040f4480c0e202040c07006510340103d4000c1030000c05030910b4824191104000c2504107105000025540804002040d0781880b90701a9490107940b1000c2e01c41f1406288281c4465811490855419401c1a800560700000300c0c4c0c242d6040c81d12003004123003182e900700c07242111070348004240805450528002c4d9041403098004090850300c03680130a490780980c0c0e03202410308da00c420165181500038410348191191030903a1035201c000b80792410051840b015205401540390240c0807a074108045108559230080400c617629407507682d01c440e8805d8582c0e0402c0710400100b408041110b0410712034081420700c01c00b40c0074903440c1c0030081b40051035074090610030b904032880015500103090011003000b1900 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 999779037 1250 999777787 999777817
    0x20f06070e13050c030f100b1e0d0905010b19030807060507030603020d030206010302040c0c0503030415020c030c030d1413150b040f0516050a12050a063209010605 72
    0x10900442d0060301094526241c4504002c100013140f0701010103944160030b4000300b00e0307054640c00c0c54042000720a000d601c2c105141045250602d9017020916030904000c00c43c0186056100b04a00c4120384901c0e60480b05a51038101c404040d1800440d10900b40e80c628802c90001460360760b60070160310805400074030707090301d582c0000e100f140254410001035401070a409103083e102d2070300940f0340409001c100d1040d4540001c030b1442c50310403d09003807040e81c020000c61464485846004800150100500350030303030204841e074000c0400b80058140d82014138025034480a611101c00c09803443d84561042040d01c02080108903c1041000100982c00204019408025a4941000c1c2020801c0183c0050074400e64422000c410f83c0424414000d03070650030081d03203041a0403281417041040c90300015518881e04079025100b07074032490304224160030000304140d0f5100d120074262803c04046114111a2101a0b102e01c0114010680000c04442001032981030100103403107030107024902d8046c8a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 999780287 1250 999779037 999779057
    0x108010f1520060447040f0206040906031709010e090c0f04120203061f050f03030d06060906080108030f04030320150604150e0708040f0b07080610020f0607 69
    0x550414042c0940010309070642c0c1c494985801c1c56441c96040c0d0600726080700c518000090f04032100720015015019a94404c00d80001120514030200d0014105642c4040c80e0200c40c001070791441d000340002c085170400451610302c0c5042a03103881041c00c00303e0040e50000c025540550b0381c03045d4003080c0c448003200c3c41540c03915500083e4019000e10780c00310340b080c1c400140c00b064020042ea00e06410754400c500f2520b85540d41e10318440d24806e4940c0c0740041c1003a0350414840e51400055035804d400024003200d05203144a0b000c0e00985010b40d000d4400304460074010b0040e070307038442d00c2907001d0b1a4aa008601c2c28280c1c50b0420807a00c15480b0240030003070304140484082c4481d11078002c1c400c40210031180b1041e021400180021025585148118601076088140030208410b10080310419500020345981c0c00f0400c3da18000010301c1102d40c040d11900d2040020f00c040c00c45030240390303c0d581e02d100c50301d0120306202000101018800075588101a40800880300154482d8040d85500e00034060b4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 999781537 1250 999780287 999780317
    0x1a06030c0c070305010f0b06120105100c08030408040503070f180203060f191806080a0206180306090604030210050f0a1a040c050304020406140d0b0702150903090108010f15 76
    0x503001d41e01e8110514040c030600081400815001040c1561013100100032513942e800c100519032081c244044441078031180100030700d2401580b40960b480f21410020410400750341c070f04a55500440c0d085800080c0440c040c4241d0a0401110001d4607250742d81741c00031420028180e100c0c0c121104c10000713243c3c0000000d50075443c0d1201740700701040c016000c2c0707201a48034640f84823a01600d0180b041c640c2800f9900841d1002980141c804441910020303103601000c0d90244052580100b81c8241c80e094042c44e00780940d103040024a10400205001c0e0045e070805140003410114241100400c541c03c000c10300c18005044030360303650802100c210000e0000041800f0030340054003040d8041d846031034404101c03000d0b504036000b50b2295100f00c608001e059254100324142e0103d50404540141440d0b002000082c88000703040c2e005025401101c4403106404c651b07081d0301c00100c03504517040c1c0010644440d6560800005400361840700c150003200750420094642c851741d201e1802c41004040c41e164001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 999782787 1250 999781537 999781561
    0x3041a091903170a02130902031b1914132c0a1a0d0314030709050a090e0d090510051e0a0302030613090b01060c02042d0b0102011a0603 60
    0x4107000e10010044540d4403410081d084210342d16041200c203034040005940e4004601c00c54800041a00301903940c1d5090921000094000030000302008000c0d01030f4072044082c11000d841d9414916032036514801e1662002421080d01c0e8850800840c828445070100000389480801034402c040d140c8030100c1d81042c0e01c440007034495203801100d0b814000602c00d000d58180c0115210002004000c0043c1200c0c20900c000400200d00140c002103050103400025008180290b800010038034010510940740c3d03000440800483d8403510803155980112050724001f44148801e103c441c0c04c00011603403a04020955448480c4c3c1c00e81c1c200100010048140c3c80b07a10421905545100071107501c48182010140095000b610940c4c420105030a80c0d4070401d0241c083e0500281d48118101c00b03592074100140e900c0e0908210483e03000f41c0710600c0c4529190036000d0040c042c003242c4500060210380c84d0311082100d42007141e007411641054820801b0545d2440c08440188090303410b03682e00c0d0346130030540c18 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 999784037 1250 999782787 999782803
    0x131e171005100501020c03030f0f0c0307050d030614010e033003010e010e0108070b1c02040803030411090c040e0c1b0d11061e0415022a010b0603041a09 67
    0xc00e252404050054121803035042c0030985000f81c0071184102c241404040da603011786c0030b11404003a4100309001720700311071802034215100e00074101c0c0e0a01d003181e51000c2c18580360701070050029a0f10311040107040f10404141000000c2070070661300508400c00403030f031114000030780107501c10f40d40c01c80d04c0c1180043c14a078840001040901648a5865100c40c400c100c00030f01c100c1040303024032400403c0001c40440c4080c11a2201c84082e8030385000d009041000200340fa1039103003078039401c1c040040c400800b440110f1140d449580d1008103040304004005680402070710400300800e09020030b00c0144000015907403c9001a98007544600501d03000d83d008260882e4110400d0003040301c010070390764100d5442d05842c000340c816a80d0950b10078000a0018802030f100c071098655400108000c070340325843c580c07007190020764007610381460040702c0300d40c3c00400000e42460441900014070075400a00c11003410410440b851480c50400361a5006000c044102d68202038404102144070800c007040800 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 999785287 1250 999784037 999784063
    0x11212080415060909020306010902030c040320063118020f0d0e0a061b0f12060801060f03020406080d051c0603230c0f130c050d090602131e17 63
    0xc0300e81038a0b0142400984045d041c100d000b4803d81002080200140c020740e841544150748141c00c05246445200310307034240891091060b2468580b0481d10f40303490f0000c3c1100b298440ca10040030f152a00d56503254100b4942000b21406069000e00c40891050540b803001030f000030f009611401042d4180419100703802d0344c50011071a102d10301c2046000890201c02c2d075400b4607800c04c624105000c004110304006040000050009000207003d94080c00405110b4207082d60000b503000d403150212401c6038841e0b040011f00c0b6106041c10011480d25024820103040c40f20040d0181a11a14014140780509a042c014622101007007805400d029405000219041151800a4000d5008002141c030300b04514066501541c418001241810a100000c0300f00262200114030034045044d0b00411100c2500001c0100800100341d81180602400800304e0243e5401691010441c46814202500d42e21401e40a040c030034200442403207071541c0d030044548a00c4210010881c400000c3d040c500811640 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 999786537 1250 999785287 999785291
    0x15081902061c150603050402010f08040804050d0510090c3201081306050109060906140102070501030e0f0a052b0207090216060c0c020a0b0c0c0d0c0b0a0f08011212080415 75
    0x24030ba45d0b254101901450003070701e0b12a400f0107a12011150440c00b140c01500301081003004021600f07102c20f218041070300600a131503078400d6114900d005d48500d00c60948290012410a104812180146201d0480c0014a604402d03410b041288060907900d01d200d41402640740c006900c910f100c13a24030706240d41c021003c1189603103884843c40141614040e600500785481c0011840c008002070784611100160024145189001c00440240450115640803030140703400d074220301441085030044032407140000e0b02601d02990701c024104441440302d0112580c0b440c05c030102c03481e001b08055091302d15024000d69100c03c04180944104d101d07801c02465949810780101c00c0c103602128a441d034034801c5585004c2c0503074a40c15200240031322481000150803d41054125180012070300706080d11540a05000b0340d0340d000848283cac4c100c0c000b14008900119642030545034005a16405032140b45904100810292124081410003a5001e41408064000f04090041e45240c1c940a0401c807801 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 999787787 1250 999786537 999786539
    0x140901170a0b040507081207020906040c0e0a06020c09060102012d060e0a0b0f0303033106050f070e010804030e040f15080d03050c071a1915081902061c15 68
    0x4a05d0b520b040c1480713541c1950140d00d28402d0111034010841b4140b680040800c0110340342e0108000082c9541001c50303090103910080c014040d101c0001c114010000b503000b4081e124440004d2203101c00c40106094116403400e601c0c1e042031103004070007550862510101900d50014040c4030002002290850589032490000b00301c0400c0c041d411502d21520f061310135216150310101811395a000648040c2c4050020384070b400300d125001c44801c2c4141000c0215884000c6080d101da40480314182c800059216100701000700309a0048042c01c0c86403403c1c6070501103807529480040c040644154218800e5032511040c40f4a5500d070342001900c0d02500e400c01c40c12554480c0c000303a86d245001c01010204e130070400081c107141007800640303042c150070100b0b14200000020310540c00309002440350500d00d0071003890700c1e0150b0080c2328090365030742c1050a5041107420301c04824030b0300c03506444603e0743c01c0b058071000300103884010513103031101c0080c040d81c45a0038400300e151010b001c802e0100060006803c0c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 999789037 1250 999787787 999787793
    0x1709041a01020f1605190509070e0a2106020706090b07180b0f031b0d020403111c020f090604060812030a060501140a0513030219060801140901170a0b04 67
    0xc0c030400309a00342c08031885902100c0b88a13480c1e03900c8900840710818182010002d03800d00d500444800190709140520040c0c441c400070b802c0c030b0010340e01e50b00020000e01c448803440c105404014050860350401005a003c0c0401100400781e88150081c01c03103802003011000c02240f03800100270282d004828510314586034500910441000392180080003c0210019900364060704454545400540789031650391048001c40038080503800034103200354100311413240c1506030720107000918070400a103250712941108110700954082803501c00e03040301c0454480180d030356228a801d14071003612003a81c540c0e40d54001500400c01e0354002d65550040444d82d42d503020042d802141324420601080200689a000442d845040c0c010a00351140b802c002c0d9860b040d0044010b4004144c1e1318003564a926243d50125688540030001d80d800c0d0902c010080c04041d400041580c09050b003002820031540c9100005841c000c018410040e03110398003001701003201400e01040d40b405410480c0b07401203090501e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 999790287 1250 999789037 999789071
    0x11030304050d0e060901080609040507080f010605100302160f0c1d091005060a0b1c180b01080c060f030901180c06021501060804141f0f110c060103170904 68
    0x64000c50003e0701400381e5040c9858004141c0b521104c06035190301055480710140000c1d428003600c1039804d48202d9400040d04002007201d80c0101a580001103400e920701401e1008403103c0c085080300341030040c0492520027450708030b02402981c03c80303000e070a01c804a081520145034a034000c071071550320f40040203a6600301c1014076030141074003000b107403241555072000c1011035030f042d40c42d2a4000440314040199048030005001880d14540780070b003610308810300b6901202c0302c00324003068800344240c551080c065031016050042441070050111141c500380003894620410f030030081d11003008400700700d00070f1003580441c541651500710300c81c142c0c044d0300b000340e00ca2809109000c010300c01c20f40c5441c420280742c100d0a048804903201c081040d183c907642c4072039604140148c144184140150082103500310b09041c2010054a900014882800244042515801d0081e000540410400000682c40010b142c6c1d0441c0d8000c0ea41804c200703684107189d8220b02c540c11249030f005003401c48060b0002010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 999791537 1250 999790287 999790303
    0x9041e020408071715010512010209030a0f1203060e0109181203060305060711060c0a0e0d0c17030304051c0216030b01090509010b01021519020d0507320a1103030405 73
    0x1d0300340c1c00480011444265170301150204840f8249080380100131074103000704201c40c503505a42c005030030a140701d07010038a010f1115800740d50041c3e6180a444c24004200c0c01d400d940340481c50184451400c22001c50314110301841080004d99948891400060024040045440d40b10340340c00401c01182c00020040c081a020548090140c4d00100e181c440c0210140b207807800c250b80142842d540c800140c1e411540040c101002401007428002900342c0d5401e00000ba030710302c03070a120903800c0c2c203204c90108100701c2030700509150780c010002e000210b880004e00351502a4050369150f8440c0550404074184000d803e0030550301e0ba00080f000c410003201e2000d1074162179102c5010400342e80c5030701009084e610102d07503a03405a040346607092101d8401552040d40078480d400315483c60040c084594080b68002c61000714400d0b0b884080c0311049900101d030345c1da5241c188015121001b560484004220654400000440c0001520390001c81c09811101e01e4a650803080c2d984914150802644802072 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 999792787 1250 999791537 999791549
    0xf03090f01110313030804020d0203340e010512012c1204350f061e070906031a100f082818050322051509041e02040807 53
    0x30001c000c0601c2c0c801c1000c1d24410940c80202084003003443d01d06480f0710001810580c0c11504003c0741902584042060a80c40c1a10760030354801a042d2480c0380340c1e11082d025550500210305070040000071110740300241581c50407640c0000242105172031074010300b41c03100e0030501040005403c1d0800c1c2c231036210014005400340190380b0f640715190f84049162040340516201010041c034601c92003505041000780500818542c511204851031030149400d1101c00c00e2001580725404201c81165020b40c03085100c402103880c02c2d1142405074001d0a1501c81c1d014280405569485039003410b40c90341400c450b183d13801b40c154008803100501c01007600b035541140c0c82c00309007100041284420b21180c0c0800e88000090003ea03110810100e2201a050100b540490048603031038081c0801c106100410020380644219803a803440404030190105090303002030300c0b410710007285001c0001480100c0c1c1900c2c1040381c000070a0b00380380c100c0200d10100500e400d80103c0c408035021801c803400048080944003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 999794037 1250 999792787 999792791
    0x1805332b0c060f0c1401140c0418090201050306011107120317060d050c120309041508060f040b06150d0507050307030b060705030f0a0c06020a020304030b06040e0715050f03090f01 79
    0x148910090343c4500380b1000c00340c00900c0300310010010501e18041201c80c0f04410b400840d0604004000d40240c041c1a00c01c010000740000e010400d5035511901c0402043d80c034501840704905540002e07000e1f01000340501e06101c4182c03452010120140300120160003010440c150404507420300407c1d03414607650300481e1051801c0419814036000c1c0020b51f09660010003480c03400c20020600102c01c0b07071284502c03000e00c400d103d0560281d03107600842d20000401d03203100300b1542c81d000c50603141c08406480b80b40607082d00d4040c080440c40802246c0d50101c42a00da51801543c3c240e1a81514800c1001c1499010300d410140041290302c0740046000382140e503070900c0300d51451805c110380e5203c1c04000400a80c0300700000ca0001c0c01c90006003a1381c2d0b44506108030340d50566101d10781a42c3c000c40c0720344c005800000781403042189500706c041d0407007003e90701040418000440250b640000f40101e10080c4020320301d40304842d00c0b61080390000014240d60f1502d0303040c05000160754042d190070200040d4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 999795287 1250 999794037 999794039
    0xb1308011b050d15090e160b07060b01090b180a06020f0a1103070305030c010b040f181511071a0702010c05041503151805332b0c 57
    0x10414010080500e91140c5001c0800354500000d03076860744030004041956845a0f2452442d041400550009202c00e100100c0c6081c0e205c1c80c203900f060040709034020383c030180840510500b880803060b2410940c2c00329001454550407001030f1040c000d6a070000c442002c000034504a000e0702c409900419650540b503180d40c01c1e07102c5400b81d0700c610140c107202c0034680c080c0a4102c0826000d8001c650602c20160980355840d0310303030716101e0941e8054082400f05a460f24400c0c0264203042c0300e6840300c0c1400707410400c45105550000b5407400050100606441c04600c001c50306184194025a80000c4940245903039040c1460a030201e8032034100005c0c1d150513980c00154040c0e0040c0150410b800b01c541c1d0f524542402c0100410204100300340c40c0040541d15031084900c641c2c080c960002130f2403240c2c58560782c2240c0b25203070026a00c0041192442007200304000d07800e2100705d01c0303541400e9091160032448182e0f10012510302042c8603203109124020b68103a0090101303d2580e060356a0242c241030f0030b85 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 999796537 1250 999795287 999795299
    0xc0a14071a09070803070b06190f0f05060708040509062e0327031d0d0b2a0f31030201020d050304020f2107080c0a0614091c0b010b13 59
    0x41145200310720180d08100203140004118000a0354882c08c028060103120803554018001c19000b0340025841c03800c80c013424400d0300005000c04004110444205141c40d100b9a185200307800f6a2140302c0c0560110400700f0181d50b10380c0a4019803002080c0d400f0450037800819503403d900c0700c00908042460450700fa191040f03401482d80d1503410000c013500550100d0b65044410840c01da0000c032010b599403140c0d20543c0c0c1e80c620780288860007003070b81d02603c2c20312803068030b0b000c848104902d0400b20324880441554050304182e4480340400b03c240b5031240d0b44100501030181c1c0c01d41482c44581c01d00c0d80e8524241030a280c015003904e000303a0803540740100b8038409503042e03c41650b001c5d43c00114181c0c500c03034078a0025201c2001614004041c1e9108044850070351803c142d64200c1001c03070f00496450101e41c02d2004007100246414a010030503c801000f400009102d002c41c564091107107030740c90060740306a01160900c0d243d80451039001e00d45e943c10014582d900110f00c40c13030b00300d81411000103103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 999797787 1250 999796537 999796543
    0x60302030c040302060310090e070e0906040203072312011a0a14151c0e0606030a031e1709100f050606090112150608010503010e030a080c0a14071a09 66
    0x42804140c01c0140703481d065400700b02064000610152003414010030101c0c030b4142c6409482101c101c0200109001401c182c11102c0724600205a5491a40000104009658001040d108560126500095078205900d6800c40110405c8255401c4400c03620032248003441540060710001d40403c03c0610100c00c0002c00c104108503100e21808144170034440070b16440d2034005070492400703514420b07151044000c144c3d080b10300840c4119030400d6a5408010080d4418014998071201c1240034042ea00441d5801071700482c22100c0f816001e100e80d10180c03504034016108890040030b009080459803800409145d520000069116082e900308060ba5a00c1d41e0280207581c00340e80003c02c40d40c10708180400444403140700c090690f0029884881c0010380c201e074610408054070f203580d910352040d030401c0300707140c2558910440080c1660007000f80c4028647d1007100c030b03608040201c942c0c075912815402e040b1000b80000040c0c0032583e8000442404201140d0318004000e03040c45118112551043d40250b1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 999799037 1250 999797787 999797791
    0x3021c0507050c0916030225050a06053d030203031b0d140a030c1202160228030b040609061506110d0206011403011107030305071707140703031808040f06030203 71
    0x803804510700180c010701036000f4024258441901182c2400a01c0648000c030708c0d51f45040e21160005ca8120081c080d003401042d5115009031082d0303030582c10440d050f424140080c1c91004080d4080031101000f012400039560041d600241125122020707864200074080640100440300e106034480b021805004515680c1d502d00f60341c00c5035080040e10b0340160098005483c3c200100f00001900610180c01da201030100c0d45049201d0412101e503610510880b023442d8844501c1d5180720001e108400d0343c050a1722000c0d00e0340201e402c030f06c2d61120314140c40070b401c410f58010f06103070624907407010031410020240d085035081d903079440c440100c1600f8030380c40740a400c414500680103040103110800e4850740c1c0c403201041c0580002007803103036900c03030400303d03040050110000ba4a40051007649503104400b0491070044c41041c2c0340c207041000c4050105401040408130181c404038071103045c14029070000031100c2c0541400410843d06181490a80c1e10074000d11400103100a030225419109200341c0f4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 999800287 1250 999799037 999799051
    0x10050108131709010201090f080901180308030105240301030b0f07030507090509060d020d0c060305220f060906090b04060e190f0f0c03030504320d03021c0507050c09 73
    0x1400b2803208405095074031202d10729056640f0b50080f2000141d100e94100e06e458001c40000341c89a40100004001e040c81e000c18001c400d010030024000b26140c0000c032411181d088031000381c030780e85200d1600100c12541035410fa0398400480000148064005101d01c1500521550f070030079501d40400384c0c200e0350709a6503080051600340c0306108505104440710f0300b003000200b84146910003580040c0f440c01c0140340484d007080d44103c00f040221f0305070003669000307070040d9004900017066800d444d190600c00e1101034180e08a4400c0c440c140000c2d03620542d1104d400c164180184032450520090802040d83e08032401031030700049844683c404a0450844003070940318020300c00781c40c3c03203001000381c0141060b00e009109248050024008014120056100c5e458254559140c440600c800d184415904a407094134502c0d01d1081b00c0100d19031001c4903104403030142c0c42480a0808a1800211001c2e9030754003030100c200c1c124040d41010150140b24407800c102e81c016039000c414401174607001d0f2580 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 999801537 1250 999800287 999800303
    0x27060212030f0f091603060f0506010c15240b0c0d050405010f112803030b040c05091908251d01062d050a1b0314091302031005010813 59
    0x442d00d01d40f58414400d0b00034103e1021034142e41102910f03808203002c15030048a03d29a02d188080090708035004156100c1c10034204042c0c800181d03102c00c1c5a512507a020100e40c00d50b1600402e0190307a079a43c1c4e01c00700000614403500115110800f10559a000176109062886510811030740c0f51f01c51401c4405698040c1d449040e1501c0400c400c3d1035805007200c0c042614040d8002802210507031010070000c0f21409500501102d0050401800312241303044023502980c141011150341c150041c00311400004140c03500c5409042e8100010917180c01d41d00f00079003600441c40c51481c1103840704000030551480f458840f0496a542c201c41012040c15220554001c060000420002e030190300764a440c8502494014465440f10284010001584c0207207000704001085070302d0810f82c455614a41148042181001048640c4019100b0702e000c0040c4000d2076800950003038151641036400b22988280c1d0400c1d03440742004d80c40c07401140b103d801610700103a10b54002805024202d250610400e810204c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 999802787 1250 999801537 999801541
    0x6060e06190b04180e060403020a0c08010608030a0e04090203010f0b18010302030a06110c120d0e060f010315060504050a0509010c05120606161202070801050105270727060212030f 79
    0x104000c6000c90401003c004d0303602c00034440443c2040c440302c2c1c8194030035805402103441c41c2c030389480b0080140e00f21049503858600c06000b022400400c5805800d01030414902c03022050740010080d255900d0029019400d25404400190b1207400100c030744901103c121000340b141d003103040b000c2402480302070340c0740d481034031202c01044166201c4004085840c031000c0c945200007540519101050074100c5400e4400611030360200031520401c02443c1030003020340010b0800810108041c441070001810060000300c403455075140c40e80c0200c00410003c0c005000034070b0310f1915200285012144080d8950074410081300152041d4200d4404010580e00b0f181a03807210014000d40350071003c1d100a1083c107041c40c403030100d81c8210414001d602c0583c014640d250070300c01420700b50ba1040c0d10040c040e02c095034950036901c03506441090004641c40d81402195030703c810445001c1d10a402820b4038090002c2098904036640910340140c4611384c085465118014003099403610048030414601e10341c2c240 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 999804037 1250 999802787 999802799
    0xd0302090f0d0206091005031b09030a150f0e0c1804080715141312031104030201050708122a03060916020c09150102060121150906060e06190b04 64
    0x3642e9032000e400502100d01301200c01c07000c03810b800404001803000c20004000c10400d40c1c03a48900000b00000084510f042400060110ba5200c2d1003400081890b95001c019401da0f03a0f00c1e500030890742c6001d0b1010f100c2440f031840790b103031500360f503002882c065800c0c1c080c2e8030340902c2140022030080c0e0344401440c1c544160768030341e1081100c000c01c520311001d440301f200b1380c0d40841c910312060141d012403081c1c00d0008603601c0e01745500c2c0d64187d401d009241c1803007030103510300004c0d100f034400701c94081c00c085a841126140402c258410310400f004014650410301c06d03502619182c901003031010b82520142c00040076041c1503a4041280c005a1226000c0001450f0816000220711640a540100c0d54500007002c0000c444010071642d441d080162a0344410003903030b04001c1c3d680101828000c1030103c4440300054500e0329103203500505440c1d4840e016010600581e8003001096800007003c20100e41c40d464007180c0c4110030b8900714070540440003010046400241c1d804203c904441c110380c074041c9080 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 999805287 1250 999804037 999804049
    0xf040507080c0f0f04030312050610021e030735090d0f0203010213090f06270b190b071709010c060c020109020a0f091b02060609040c1203030e0d0302090f 68
    0x30143e449100000d0001805100b0301c0800380005e0b40c0b0a4442c81e1100c00401907102c1140d40080c501031050100104a0302000e03000b18911944000340364030749a194034104926071540c400d1035001418059040740311642c01c008116410f8a040e454418442605910f80e8040f00c07a0046072042944107001d00e0311000000c02d03207010501c240d807000e0005410f1039499149411030100342c2e4400d034140d980b1940f00b10882c0855102d0301002d40407182a854040490140d2114000d101302e0b2400c170b019596448049507541d030b044c0b44420240b4200b14015440382c4400303182a607500510011240700904a010400c001c1841003030742c0b42c00b14181c0d03801f44140c80548529018080705c0402e2000e6541e50780c0303c1301c0540c40e10310704400a460500d0f0700c041c2192600c2c03101e03000c880ba05001e40105100003590100c0455001c00c2480d00107804551080c1681c031542402c04010200303602400032030071442441070815400d0b030806003c995001040d20a6018a84002c2d001d0344901521b9940c864900c0380c600b078071443c0c02c07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 999806537 1250 999805287 999805297
    0x10020a0c0e100801050901050402040e1b0d08120916060806010813080c1002040f060206190e01110c1b0f01050d0e031e07120c0c030618200f040507080c 67
    0x1640118160703075501d0b41d803c2c0c01c581d010356200030565120801c02081d8141402094060340c0044001c00303956030a038401030191103500542d00d100d03150500d010740910061200f928203860301c3d0900000c16091078010583c2e12140540010142c01c00700b500012103c1c0200c1c8020302c81c80c41078440b03e0041c2c0d00e00c0c01c008100c0c101c1c9041140ca50400740588566090104030524140368a2403006a8807400c1c030340017250b03a000c80e6020000b150300100810003885415440b00d20325111043c000300700180562007260242c1451031100002c85000304080c400144001004403044000d905500400700c0c940040c40711304806000040d01182c010000c0c02c0011905601403252000000e00b034a04191901d02040d5403080d91200c2c80140700c4000c6589028000e0b0851031241d01ca1050604001c051040c0c0e442171070f4800c2c0c51002420f480ea403000400a5506100c82c250401544005142c001400f5501100c40300203900101318000c1183c0789036040641064466507004100136140c508082e07640f89a20f408950203 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 999807787 1250 999806537 999806551
    0x605040618120b0414010c05040602100209031e100c0e090702210d110c2d100c0e040f051005010309150e0709050c0a08091902060a0306050612040210020a0c0e 70
    0x41c403002050420a208915981f1181d40c0c4003903550b460008000c1c0342c40303c01c60b00081d05501c108001c466581c1d0000c1c0c0440c0fa8074008000889403240944c2007030800e0f102c50450102d903414018058400750f4000c1d080c1180c1002283c1c1c60070692202e142c06c903520490b44050f41d212465540340341030b902481d1000303400301000da950007182070045520b40b241d16030407400041c0c1f425441000c0191001000c03c20010703103c08003c0100c85004e09900d07083c0d94404210700c08001159036000801d4986110f42800c94a20303202520600404602030702c034100412044030801c03000b5000d008045119842030051101c45604124020115030111603d03500908090350403101038800c440b00003504400e40d005403840b0701e00d0402c103140c46143c3c001003e04004e40060079040c094005103e03503410a8030b041c201e006c0300b980507103007651140d58441e070540c01003402d9040607510040106480c14481541600c81e40718510a803200703505580f880c0c00c1669581d030000705c01032428581302020310001108102c1c166000798 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 999809037 1250 999807787 999807803
    0x5060f0c0702270906130303090303062403050c09010c062703030e0105011a07030f031d0304080705121c03090c38270402040605040618120b04 63
    0x10309a800155621290346614510703514411a08481e060710f40120342d0300140002c040d1482d840c103e52140b02d00c05150300c0c02024035580d03844110072302d440382d4402c0010708a01c2c911242c00741c2c8412001c2d0880c4003801f07800400a824000060035000ca44801e4455a034410703182c040c8010101c2c0c0d41c500c00b4005812140c1650580b84184101d03401080c8040240e89003c0e0303d000a2150074142c55500303480f0140c00c0b41c02205140010f8440350100c000413210245e41625200c1c1e0341c08054900bc401424085401003101003010224920360500480104100c5083c4800c8848641c0d035070040c4449208080007103200c0c0e800203900035002201243c0448821505441c00003110960303981c810b03400c540c00781c2010400c00d81c3d01100c0c082c0c0c01c2d0b006480c030300d4010103640040c21010014861b8641803080c011801d000301141d0180032205001042c60b40d60f60b1a0040040d5251078607544010540d8225105600001f8405145030340d541c0c0302c00b0600010307202e0410b582403846003a501c443d400f8000191040f0340c500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 999810287 1250 999809037 999809047
    0x30218180319120b0925020307020f0618061c0608010c090b131a090f1e0f01020708011a13060605090402090d15020301090e010b030c0f1f09031502030405060f0c 71
    0xf6607001440fa2003070b0461b107000801d4034880d0302040351020803d221201558130400891380980d603414500404003604803010799a07103500625a20300705026041c8a60009408116445403000c049400410035110311400c1204035650a0300c14241da1000e22000080f4507503100c140008080500103000c0d20803401700c1c8a0446554100d0075481058002804801c440c0210f00280070789071a58036081064000c8460003407143c6030140c00300d50343c6c0701c80c82d03214071410300712034209a164001d0004000510510008100030103400384c511581c0c0c03151410f010320401c84560200c5001140c2c1c421030f0f003641c2d502d50390a81801c2440c800e1000950092080e1640800560b19105c0054403480d114420308828a0025807070f54500300003034040d80c0d0302801540071a41030103202501c58400003100a0340610072901005150030300f101107501a2041c140c0b0400c82e160000c00e0700c00603600300d604c11080764402c80c180c2c0e0072031440d141c403d8104e002c160340080c40c541201c00450b0b007088541403625004400e01c92114640 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 999811537 1250 999810287 999810289
    0x12120516140f180f09040c0b0a110a0b090105070203040e0a0525020a151e050a02191701050103050115120e15041104020304080706020f04030218180319120b 69
    0x40c2d0401511081103801e03501d0000754600b0885140d04c0c4000041d1400006801c242da40d81d08038a00c0e50050411a51021420b1054a441034810b047c040300f5041c142d540400c140c0c1004110010125903091040d803e201c0441d4800b840001114219410f9903000c480070780325040c40c000074180140c0b0480c092451140c1400a040c0d0000c10a0004295900101241e80c214a0032010305e007134241000042c03a02e00705071010030701e1030018450010642154002826518030380300c24024021040441d844650340c05581e1000c51300074502180c024207400444810b6a60341740110150707502405080700000301c00b212a210b01d030007100c0c40c1c08a28200000030070b00050f080e00140c90900c50f984080761a12101d000d0000b48041071a51450218003994194035502e40350b01c2e010715622030848001c0c9020380c0066281c4a8405030340590b0003940d802000d003440c80b0900100c40c00d490f4001d0380c0ca48120300c103542a180780070301c0000444180145008504c040209108401da4429040b00d070f041c268162100e07608525 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 999812787 1250 999811537 999811567
    0x70c1b0e09030d05060f06040e0402040906090507080114070f080405120d0c030f0b030c0607210f030b040917090102030409020408011d030c0703200405041212051614 73
    0x20900d60301e002991108060302249044d20b0000d0806030103100c000782d036486c06480c3e0104450030b46d154844103061a031582c1c80468018002c83e01c0c0504658940002030040000120321841200d58540081c044900c001000c0303172540400395051400710701250141c2807028007860350503511500580a41e007243c4511403c00040f0f520003090021800d51f0f070000b03541940e03054481c2c107090229401c0d04000f14030214012940d10600151118072950b0007080d040c0800c01201c150b0000c3c4c1c034022800310745a40f80000c000d410a6034025043c008281400200c08075801d0501ca080c44c0107030017030a8091807011044540c150b950000400c18110b0001300808104c5a41600040005004010000540500e6641c0d0b8404090307441d110b42d10550410001c1d00040d5100007904800c3d81d402002d034402c0c441c1d4518031288034400031081680c116040400b000240151444040010000c81c0ca580c5d0a054003024120100c40c0d04a030440c4c04211166803d00c034207445603c0c4002c180700f07219409445c1145034030f14018 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 999814037 1250 999812787 999812791
    0x1020d09060606032406051b0a030e091302151606020304050c0f010504060e060a030e0d0f0806030c1507032c130209062d0a03051509070c1b0e 63
    0x31890b4850400308021075140c4610200c160a520004103800c0c41c940840c004480c1510803c020003c001ca000305010300400518035060252074220340c1030440342d10740640382100201815101d0a0200005078507044440f500b030f07043d607900526024605a111000304100d03004010b018800d2440c0c0403401d400100300d84010b5001c0e9000f5002800c1002c8145c1c01c000d4044140c90001d030411100340001c02405420800003070104004494240c1ca0300602003003140200300d0002c0c0b2400510038005d09492094105580c41f640c12116030720809140e03034200a055482d500b658909030442240044203c0045950002d080b50506c246094100f010028107070070181340307104801d0b502084512040710414503040c00800b98141c0010340550400c88500b000503100e00426036400101c1c404050318910807030302c45810928481d0028000b40c1c5589824900800400b803c480c00341c107404027641908002c0c540003141a11806080d9241300c098002950303241400b00b9241e450b80303580441203070049070f6070000d115032034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 999815287 1250 999814037 999814043
    0xc05010b0d060603140c1e0d02040c0f0305010501091508040f0209070215060a06081306060f0603021c11040605390c15040b1305030a140d08071e0201020d09 69
    0x480c680741142402e0b44800c2d81c22030789503001c1c0d11503142000d46480c2c001d241021903e1070310061f0407014003070340820780380510180008e41c428030348031500503d1604101c00e107241d902d056400708181d82e01c950043d149075105004100d040d4403e003c580c00031502c1500c14540c450700c10440700c031842855134045091080290f4072440940c100c040780040706600d01c242c003544000c0481e07126082c0c43c03812001401880b070140c0102421001d51003880e0070301c01c40d40c00c00c81c0103000016100403080d503680300040013904030380100c0c000d03401406010645100c0600420059200c03521185103494904001038426911540c2814195250200309038040340340d20a480d03c0c03540d00202c80e40c00240c0b401d007000b41090b0705002002e104007004491214400312a81c15103042e112a504034075607500e03841d1003d000f00303e4113601c150b0345481800700300010040c08501501e2100c214008484d0090019176080e00d003c64100c400f503001809081c10900c04518048c02e05c0c041c6110303400014a030204603486070b001c2da50170342030503 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 999816537 1250 999815287 999815291
    0x906040b0c0a12020d0e100b0607020907031e1b09080c01080601110f01090c080102190305090a0c0305070812030705031909020303031018021810020f03120f070903050d0c05010b0d06 80
    0x180740b0180910003020b050462207c1004991103820001e0720500803507501070b0250451a0004d4200e50081d4841c1c5803401c0d50740c20700328110b82048440c1c1b0240542140300204205680b030100000e9000e03001503020340b030745007001c1c1110308005001115140c0d001400b1504000c0000504580850700303001607001c10011000102d06581c0d2400c0c0071215030786a510108040c1c2c81006080000c0e000a0900400594a483c0114044d1201e444551410100000140c07424050780000810850001100000c4030100c3c0c0c03c2d1400760306100310740c2520703003c12074400d004282c0420010301c80b01040103030201d21541460740082c14103d1500804d00e5500708503250b840d2200882002d009002c07400b109031805141180041d40b418202010001200c05030b0458540211324102c0213000d031a0080c0110b501e20940903045035110030312203030701d1000c40d11b050340c0c0440746c0c50582c0c0116465a00c81c15072035068076000340040c2050b460280c011a100146020180c2da99503031007803442c227281d4a02c41d410541901172180 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 999817787 1250 999816537 999816551
    0x703020c090106050406170709090e030c010c05040f0e040309090c260702071404140f07030b09011d04150e0c030c0303070b2404020d020406080906040b0c0a12020d 72
    0x601c5041c09040c2c20620a0080a110410905900c0441d980c3c42c030b46081c2c080c00e00703030700d070b2100684400f1910b4008091541c18145e01d03030760160000010300389403803050000380032119291400392064411070040743d6a14640340d10030300c00038204021f00c580103442494011101e642d41d25054044400f0345610900081c200b20004220581d843c0884880620000000f1558185404065616021803050b076074420951103505d0042c0e07a4640c0012607a298484803c0303154a0820103500105074100c9142000c03e180c4110607416050010500d41a590b60800000340c9115020b4031404081000740111400c284005a40040120500070380c0d210002e51070007800700119030400c06051070b908025040c044d40c0140321500200d402d044031583c120114110f0148054540350103000720036a0441c180f6081800016044104041e6034010800c59481f5560a525038984511381c03601d8040c1170781c01038805030310200815801c030200401480101564108400141c06040c0260140d13040481011120307070766059 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 999819037 1250 999817787 999817789
    0x105042307111b1807081602031b0c130903050912010e07082d0c101106040f0204050612100510031a0403020d021f0f022206020d0e030a110f060703020c 67
    0x103001250044d5400c1010b4861510303030707001080440d0003440ca400ca04940d5554002287c001d200322a4480340f0744107414001c0172004001c958907007801301c40c10700035400c8102d220321f02e4142c1d1082c01c01441e895581c9915084d03d4004000802c503842c83c0d07003500da550b5440014070402c42000090000c0c031a00c0c0241080d13288046d2107141250300407841c2030345102c58001150700c2c000c0101306403103005000c032101a01d610440c04101c070420305c01c210507902d92062209000c00c1c080608000f003056442101e051181d66034140500842c00c1c20107102401c5944a00602c005110309070708840d40c8105401c103100c0c142640c0c1c2d01c54800035409007101c4074001c2070720b0301840203055040c0850300200304540000c08000b24109004142c0b1452004004107540e030383c600b0f0030182421901140ca501100c012221200e4865100414100c8076511405015106000da04d101f5640a00c0d110400d040c0001d010f001207990944031803404800d031800c1c00742e0200c040205825140c2e00c850142c4000e5010382d000709030242c1024 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 999820143 1106 999819037 999819049
    0x15011203180602011a3f0a0b0f0a091203020f040e0a0c18050a0e0612032a12040306150803041401080105042307111b 52
    0x40000602d43d905402241c401c00003007a0301a2240b04110402658420707011074500045c40078510301690315141c0c0075a11040188500300e40b040e030480ca190500f40603100c8070854030b81900350140507810440e151100c0c0e1105165104000c00001c80d101c1c0d01d8088111031800040680004d40c00300000145400d44004000000324400c0500b45142001c0150851840d140001000200e0285250100c9000340301207400c0a40700c507440c9810a00c0640d410003009100a8001040100032000c1040800c0100401d42035811103000800c202cec68420304004040c0303d030401c00da1140c0c0c442821442000101e4007101c0c1c0c0024001980c00100c10341503041903080d0b0100280d400f011500142e8880c1d60400070322040801d03603441025a0300c0f0700400c4202c0356103c01b200388003400c210444113036490045405800481c40c0c101003071010307800c2841514040412030101d440c4401c4115180c1541014 = true := by decide +kernel

theorem cover : BRFrame.Cov 999640287 999820143 := by
  have h0 := BRFrame.cov_init 999640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 999640287 ≤ n) (h2 : n < 999820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
