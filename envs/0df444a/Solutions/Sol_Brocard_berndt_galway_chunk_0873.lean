-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0873
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:19:42.216902+00:00
-- url     : https://prove2.me/submissions/74a935e8-50b8-4c94-a0db-eef68ff6dc33

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 156834532 ≤ n < 157014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 156835782 1250 156834532 156834551
    0xb09010804060f050f040308101206020702040615090305150f01031b080a030e030607021b3a051005071709011409070815040515041a01080d111902010f0c05030706 72
    0x3400000000c9c84188a122040300c103209600c1d2100c0c01f0044154042005a16503201d403000401138002ca4000148603000e10450300c106030b40c400e00c0300040307d002c1c0064410100007103910744500141210541900c44c85031004000145072242a0a80c0c4110261030550f11501c3d0201c0c0c80c2405443e4005030b00042104050754420320381400358a4000510340018980d141c254408910540b401d051030318031503000004843e560a0164240001c035803c0031000d00c3e401c440707600311b48819a03203100302a5070340d03c60781008042c816100c0c40307030900401309926a05555408050203180a9500030041c0b038555403110b110b8110070000046042c0200c0418014103a01030803c440c5915002003401300462010400040c0310100d60041004181140820450b203e80c0e661828440c006c0e0142110120904541c00300000302240e02142d00703803205516942c2c1000302d001e1600304554594981812142102c540074440e4010749c0280103410901c2e0309810040441015501c0f4035003190890502554a40d49820b50750 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 156837032 1250 156835782 156835787
    0x40305030d02031b0a1409040b03070306240f0306050a0e030c0a030210110906071103030304050f061003051506040b060c060a0c030207080406050a05250506010504060b09010804060f050f0403 84
    0x101d03a0f1030740e000c8074036003081c4841100401a10351149106076504c1b00142d1400a0b846d1508101c0c0f840c03401504036450540c0e6464000e005141e01503010090784080300e038410a040018407240b00b252a02c00d004980d081c25915034000030800079001400e0956110120901c90740c09001070110242c10300043c210007003880c10080d0604114a5007200034074a031802c5452404020000d43d09181829244542c550020341741050801c450f60f500254144808005c0008100000607000801d25001040d02c526840b030f20800e5215000a02005085820615420341d5410011a040c0e60000f0003e00102c0c18443d00710110360141e01c0200801000c1d04010104005082140030303140000c2c403146421032501915840e000f4850145005070380411070006486c0100901c50350a580c150780034050390660310804540c0d080b03c0d060403407400701c0303d0b806000300000d2240740c10321404e0200c03400c07801112310b8040c401d00115003111006104a030000d903103d18104904040740f050620034040710a00042c14113250401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 156838282 1250 156837032 156837061
    0x503091002030622091b15020303070f030504030c020a091d070f03080f070b0109020301051c0203030d1e0e0d080a0e0d030902060702040510150302071115040305030d0203 75
    0x40c0000d0354010400e21096441e40f5800e0300030804109000c003005403804010b28042c0c034490344080c18164011030200e0304120040c103484215000a04041010905400e05036100d0200315074050102e1100304100414600a0700f05680c0940f081c9040e04544c0c00e1075000980724031180c0c202c1e4960a0360b03450004064064200a40e10002c0d1010040441d585403240c0278007225200e0100400f0f400300464091080104803080d101d040364840400c07407403980c54a80a00003034000b4441e191048005419140c812089140c00c0380d0079540250107545003e0088441d64007504001c0503030300d082c1c18085003c2c200a041440b540008018072405051140020340d001005440060130241450740740c082c004000c0d5500040c940140b100b01c3c2804542072025000180c0c0c0c0d40541c400c06074015040004000c480780707120f030390385003076500300000007480c40751303c181c00c404900801c94010300380d5800c40c1369025240307480142c1b001d4585540c20702a00c1c1984030f0b90780c181550003e401400a0342d402005010328010000321 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 156839532 1250 156838282 156838303
    0x203011b05190903260f07030507020411031506031b070501060302010f0801081b040902060c0a260306090c0715060302150c0c010e0a080a08030604060e060a090203060105070c06050309 81
    0x1c00f150140e0850311050340c00802007001481c20302071011604000d01000d801d4504200c00c015409032204104d0901805641c08001c00f01c0c4120f00e03202d13090841103c1c070030070740f40502403450310500d44e500d03500e007401303d154000703081e070403400c00c10800e004e00d40211080103001051107040046041460b5100242842d1001840174060040410040c400c41200145038140c1460071003125001c400110082401405031100c065000390000440d440c0401c00045c443c0f07a103a00c00d03150010149141038115050003040c0511402520042022400d01c0c45c20395005034102d20700c041c1c2c840ca070445643d212281c00c0b0003140c0c01030003d6200c0c03000b04151321b0220807200c0500114550b0614002e1007142d181d840d00c0c0c486007120305102c0c1108080c001d503160460302501a111507021108105002d044c40c0380560000c4418038032450500c03502203001030403400c4c0c2500415014069480709070810b81014013a400c001c02250400c6018003410005c2200703448a00d0050034141c0362160350303081500f88507061201d8580b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 156840782 1250 156839532 156839537
    0x13091b08071b0c0509040303140f010605070321050117060609040c090c0e090c090a0515030105010c06150e01090b01020625090b03090c180f0a090203011b0519 70
    0x400051540002c0c90381c10075408402c0c500c0106249280006080509811051304403401200b00400c0581540c00290080000d542e1102e15540c0e002091003660401d00440000032000d0180100007406490415800403c0c504040100c102100c446022204268007107200f80c02d4020300c5405080017400399a801c1a0160351400c05403070b060b154484110120320a4400c06c03680c1d92500c50742c2602c02d8810032141030000b404000207050440c41c0d8000b540000038030302e200b94480c0030300281c0e5142464082d0b074805038019039203080d6840d003001960305a0819100351505074a8110b401d01e414410110b150241c030590003070340785550608018004841c1d18980303050540d0b000000b40155a03c0c1030030a8040c40003403100c80003010b60490811a8036880d20361110702d201002000384104c0c07410108107070130384d0042955681c0c144603050101c801d4030f03031003600d079400c14049040100740000c400da0043d00241d8000742c00411142c200310300c20301036244000c55810001d040452201010340400406000040a0b071 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 156842032 1250 156840782 156840797
    0x10b0409020a051e0901090b120f07050d09030509030708030403020901030b0702070b160303060e1320090a05041101050726070807060606140f040509060316121209080d0e03010213091b 81
    0x4103060700700d020050082b9102090500010b581d90744a40111441001080303c24400c0c5d603000d160103803441e0004144c29120f4001c46d400404c071003800000707560480742c005003100e00603443c5840d008080d003806001c5408500900d00042200c2c0a0580182100d10b0300b554031482038000c504000b0121000b0f600f042901e1171215060104903414011492000c60308252409215110040b1007146070310222002c581160100e801c200301c00a00c0e03840107208034060910004049021801103c0610940c50028520140440e01e09402c601c02c0c658420f00c6c00165140a1500005031159007542e00003020490705540c84600501a650303100c02403a034084203140007942001c1413141c41038498080da0103514060f2100701c00041c40c6540070401c550580c2d50101034035042d03a03112003c1c490380e000c0d1070109603005009040c6403d21640700c6c15601b0115010341019103024445240101d40d0805c2c80317041c0d0366040d074007400720103281614075a41c1030041c0602440001e00704c0300c4002c00e517200b40741040100c0500441 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 156843282 1250 156842032 156842047
    0x10803040f05062b2d1406010203070f1106030c180a050307060e0a09020a0203071202030a08070c020d080307020a0512070206040e0a0f020a0809060609010b0409020a051e0901090b 79
    0x8052907050303203090b910060056852429424014640c42c2205080c2020304840031922910451700404821100c0301d0078032843d600001c0c0c1042a22090f50100d0040e4001c00542d00452549041071402c01d00c61100224262480c6000038400d400585856101d10000190203600603483d907441003800105594500f40c00c0c2c41d00300041d440e506603200d51030902054a50003407090341da0b90300303800c05000003031001c5440e0407500300000e560707070400e040442d4140c000051800800f07000000f5a01c1c01c1c1e600395900034141d5640b2030100e46220014500320707007008000e014080040c050002652003403c0903802094821103c2c00d0142c42e000308020b111464000400c0400f01580b2041c0071107055514807443c004a0761203007281a0010040180c0d8410f00e94808a4000c034000d6000d5200c500924602c4100e0700943c03100d8080042000d800c2c4190405182d04000410a1981135000742940c11402e04096091015a014030914041902d940034107035240062418815a008001840640320354100981040070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 156844532 1250 156843282 156843307
    0x51902120d0b0607060f02040e1b030106030c0e040f05100608010b040b031810050f06221505041805161404020f070204091a0601030207080f0306030114010803040f0506 74
    0x3580c024106a039445400daa10692503d00c201c0312125801442086040b00d0405184000e407c94007860521410714004035403581d90b10014210b140412002051450746842400c0d8001d09212124070700b44100181c10f04420b40d503d1054000400300071002085a15025445590000aa0700131906028902c070051017459491780c199407e803500c00310032990342c0d103445003503080d01d20020b61105014490009840040790241e04454068440f5560707414690300ca2204000d540c0707942143d420701041048086101003480b9030080754100540446080c0842c0c1ca44002c5400d0300c030100c0d004280c00000c2503d40081050402c00200c2084002140c4c08074941495013940020112149441c401d98000c50f0b03040300030680f00c0071920b4199000b0000c000024a62801c21208050b501e80142c02070701d601c0000d0040e5010340200d036035280c0c0c415040d6107459410303a8a50341940018010300e8066503244c1c9641490071004503468060714804c030055449516041e404903a614180e00524040e12050280016400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 156845782 1250 156844532 156844537
    0xc01110312040201050408070b0d110a1d1c0302010902031203130305030c040f0602011d0f0c0111030c010e0a12091503050a2007170412020907030e06040305190212 72
    0x2101c401c00340a403514001240c890189801040c582e00803180d000603684190b03030051804100c0b0400074404066103d03c0302140d401842a000c01090071207009003130503140492400c09103100101088920340061003e03805000c10660201c2c00b40c0e42d600c2d456002d602e001c00103030708440d4208140f1450b500e0121802482e0500003400103050001c0800030800c1d0040b074030181c9001d040d2444049007440e603990002030180c0001220009001c06011105219040c042010307880030040c64024942d5058070b01c0112600c0c410381c04a009a0f00040c40156000c0200307006105100f030f002001000484480e040404252020003106030600600a04c20040c0c48422501c03011000210308001a080d40d482515001924013041c400c82c1200d410041c4180e0b85400101429005003e81e0512241640ca00c80c00005132181d0b00030040c4984114030100b00600d4944407042d03000c1181e03e404a83c2615401215150807001e40d4210049034021403d008107412501c0440d04481040c8018017449a0401c070143c45803 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 156847032 1250 156845782 156845797
    0x1508031204050f01180323090d06090b0a02041707080604031209120207150509090105330405040c02010b01201608010c020601080d0905061305060313050c011103 71
    0xe61a0000101804010b10403145035040c1000284001e1001400602141803140c07011804100341c3c044081e407108000b20914055164a005645070855280c10006941c00c1e03100202c1c1c00540741d0400c800022521504a4000c8868401c050703262420440c01603005041642c101c030701e6601180302082251400100c07141c111350141040c001c000b0302c04400fa00984884400038200301051912841000d60008070380e0111080300d01072000c0c0030900c00e41100c1901c68000000d0f8411100130040c491407424440c2d41002c0074481030711400310b038050000103509001c1d1102031094900040b90421240c1002d014038041c2203028802003141e01c42080c0040c040d5040f000020350300420500b1902c1c0c034410104001c940701400102d00320342d1907075180d80b0b46000c0d284400044d80140a103900000d8200343c00070303e45440c07200342d48034040d0644c00c4c00c0911560790003154104c65009001400003c441e1280401075008104c400002e1440c0751030b605280f440c01d41819112410410060164880a540030080d204c04 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 156848282 1250 156847032 156847057
    0x705070c0315020c01050708061c23070e01060503040c0605093114060315010b12150a030809030f071a0d020c06090a060e060610180f1206150803 64
    0xd48200440340c5009003d01349039101590b1901040c02a0b00390818030700c6209035001c03190701c03110002040d6856864000410010100040c60003001c2640c10b44080c4681420380740c0088500440e540c5058068684081c2c4c003180c00f1841c0082484280500c40420710b001e403080d4105145422000e02c0840c01072500324400001e0120307001d420b03209844244901070102c0c0480c00050210949480701061441d0050320b005101c0c1c814003019003103800d00d40f50035604907525080710500704104031003403034490f004c0188030f54803c42500320149070550710007a0500c00b85010b0700c42c207a11001c090050501d0107202c45c1021210362312400d07040100440100444200b1880301041c540c0798610991408041e009071718100d00640a00001c01180c10710001c1e0f280d00950040000b445518481e032034080d100c420a40b040e540000d04c07003800514840c0503c000750720100d160701001c0d01c2c0d903540f10401c04580070507170031030481c00c845051f100b030501c11180500554031303c40c00000e80d159440c20540aa0324410441d41942 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 156849532 1250 156848282 156848303
    0xe0c030106051b1204050f0d020a0302010c0c0504051602010e0c091303020f250f0b030708071e030f0e0303010b0702010f0c0606140915090105120a23060705070c03 72
    0x2185141c06403c095650860f41c21110302c4403c1c802c0c041c185801a00031240520203110181c50b440c03414140844072181c000d0002c4550605540046404654250003a40c1c80740340201c0004a607212031191510480070340412080b5840007070402800d6599013048000b065000c170580c02c1d8107a484900c0907802035450441c00842115525090342089040244020b40e4043c4405005180c0707c1229500200560000e007207001c80c1c5c48845011040b0428002c880b840d100601c00550064003410101750004810b0034505d203030320980c01c01001410020070100c80066181c000030380d070941c580d024054013121408080c50845d8140a8908914010a03401a0402120f141181880c0b4015131a00d03000b503400200a109440d2100911601c2c480d25818140c001c514003c00542c9911580b00007044550006002240c641d1800040103803811020801c0c1e0b2040c010580494000307100c64044031586005001d840d010440405000c030304003c402060142400801c0084000003030002094105880c3d00c40701126 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 156850782 1250 156849532 156849547
    0x80307120503063105010803041d07020a0605040c03020d110103060603060602060604020a090f1e05180a0b13020a030506040b0612040b0a0609230601030b0a0909110901030f0c0e0c03010605 83
    0x2401c5040802e800313a035142400124102c0b401000800a60f2901001800107680301844001c2c000012640711006030000d03090000094516081603400c03601644a0202d055140e4000518299038550115000c082d8000320f100e0550305400759000070902400e0800c0010715009020392581c0d00108064030a80d030000300d805035640500400000750100e05101404140c6400030007026a44c80d040c03900300c2002d040d03000074203403802d500350720f0145d80d0040008590f0703180e018929001d402d0380da8060394003614414001c0842001803000d4a400d8459a0380030489080420a000c12a40d2039040240140d80820402c605410401511508a039010a000c1400c0d5500010764000346103980108030201c0c20107602c1c507228000c1c01440140e0f00085000d448064841030015403c45a45039403007a0050f0300310303008000384180d0b644183d00c194010003180820142e000005020f24509070030403101c010025a458003805005184c44000d41081c00b544403950030004154080d5010500c12601044800550785 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 156852032 1250 156850782 156850849
    0x207050102040e1006081f0501030b0102150a0614030703021503130b01090e010506011d10180e010f060c0507050f010c022d150706020304080c0708030712050306 71
    0x4a000701030f03607030690581d801c100080d022541c1a0388038080025420710003160700300400c0424880c0601090b10888500c5143c1801900582a141c0300075040d4094903503902711040140081c1485105002e800181e075a003410030204d06003041c034024502992240741c050005032900c05000c2c901000c81440d80f9220b40d180d0074648500a41c03504000d04044c200c800010340189075801c80020300c070881009005594030000111840703a6805481b064101c0c2d081401c0401d030400300070b071195100c40d600c0d100301082c4411f05e1442c000c85a680c4284080c10800700108041202c001800015001074500800c1d0784031944c075410794581c0030b0300500d84544a408007a20a036070081c50b202400550203088203070581e070300c511440e580d81d04d4060510078001e00100842001d10707100201c0011b0040700110107007064803a0b11034100a4000502c00c58030310600b080400f813481d90400034000204400320045640350007925001038032075080541c80013807240c00c0c030034013a166070741c01000d10004200c440000300401014848 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 156853282 1250 156852032 156852037
    0x30e070e0f131b031208090c0a06081801050411010905030d0e0f0103060510030f0c021518030903030408030a23090f1c05010603020f06070c2310020a021302030105030a02040207050102 81
    0x3e5628145008038000304200b10100d00e0303503e1880c0e80c2c450305516502c8401d49602e94020055443d40903502e50001d010190148021541000f43d0030038601c0080014100070782111402d4400ba900301c42e900713407003050710f41e8804040000b40c8020b0300944204103c0c410701800e05008600e078188a5481e407003084416074030a5125000800c0011300815500882d054003070020804140e0384c1480034201321440c808240009802051030303150000f1120541d49070300706c0700e450381c002c04000202d5000400000d400c0c3e607030070000380001d03020305405075030359060000c005400c60724990074941c488401c22138413000c20150841070f0b903403900c3d041c0d035840f0a04400c40002800340c50038400c9044a84041c03605a0140038055011005030f03403013500c4008582d60402e04004042c090110020220322103a40d013841216820107181c0640c1c1c0101015155090700c0c0382c0095441c56243e5400f40060303002c810300c1015460302e011054071560240904519550400740800d2310f0781c01002c0c000e401030703800186c04410418250304 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 156854532 1250 156853282 156853313
    0x9010e0402160c0e1e090f060903030f0a0506010c02040b033d0b0a03031b080a0f121103070c03050403060207030c020909010605032e0606030e070e0f13 67
    0x11581c1c2e014003038000c04a40100341c0180c982c110b501d50041a0410b02c0c0c074405001d801014101201200280281e070790134000203019044900940c0d00101d511902004541d00170310304030707000e036440f0b250480d01c10800d030400800c0541090b05010038000caa980281c400700312203405480200300010340b040030a01e082c944280c80280c20a10062140c10b141d040250354103951a01040c0d64014000207124a082c1d40780011030550040d051401007002a001e81200d4600100d8088010790403a00c50303c600c030081d00505000e0002c10910380c1d285811541c0038180210001c00017004000c89074082d2040305003800003c040314203000c1c40b40c1103001414000c03002e50300116070081e42599981403610b4014909031009a049000e08003103804100c1d030701c6060140c1c0082c4e400c0a4000c00d91780c9011445160b500d403481d1440c3c84501c820048004141c0302c58054200680b0468401088481006221341d2920120b0342c0501941050b01d0f040c000813100006815401400c0040d002401c0c0d0903078200074500002c0c418 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 156855782 1250 156854532 156854539
    0x2190c06051b0609010c0f2307020a1512050c130e06060d0905071e03051b0f0303031005031c080109050402010e12010c03150303080402090a0e01180611160809010e 72
    0x30100203052405400a0340701d0b51b40c690b2007000d035030301d1500107584440e000c13810940702c0c80c0740050282201c0111005081c1e85070000b462140c0096950b81d20340c9507049100107950001d41085145c81c0c42ca202030055541001c07000503124588440b404c0c3d0b441c4000518060040b00d2a0071308082400e65590700c05454000313280794400c0000405900d805662680e0a100310020b000c0d103079100c00d484480041821040729000400380109004103c8400d0780c025803001001e80c0700302d0a00b214103968808201071803207219403004084205013007104152070a505407d0303900c420610801100030b416400301c1d03403e044410454000c101c6807030b54401690350b95114511507802c1a01036801d00f03029041500485854140c58400300000703501d07802c3c082d4411155020180106010601080040c10018201e560010f0303203910002e480003001c11440e095403002c01c9206031702d0b07940041c1c0c0d0041c005103229100840900715a414034000d80d00040c56a0803512480103050184041480c4200e030b409a9002ca40c401e0004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 156857032 1250 156855782 156855793
    0x1030b0a0b040e010603020a1b020414010311040b0303030c0403020d080d09030906120b0a050d0204060e01181b090e090102070602040b0403060b04060b0f0f04051f02190c06051b 78
    0x80881d4452a0002c0c030401d02501144000080c155010744215800700304aa41c0c1e58441800c0740c0d141c141c070441c5000c400ca80055a45295a0711382d419a50340034081c610130351812888041e480b00304401d0300c07000902c06119800030000e20803c0d0580700c00f198200c039415100254520058148040180188100030580d141000b8003102050381c0459850284c4000b07484802031044a20074030b004480e030000307500360403048110081c0f0592900f0354a42d00054070060001c120240c460110a604040c00e03400210300c0000c014000c02c41080e18083c070030441018040c02d140c003090044004016030414811030820210070b60205151300c1c000c0d01141c040036009070b0207543d076580c1e0703003030280c0c140c2c0c840e103c01d580301032411108454500d0035000300400c5500c4080403504003510b4102e500869800440e4941e9215810040040d054861040c42140b40381e02c100076488240c4902000390410840103c0203000364901001c0350000340000080805441c0301e4a8007640f951040c4031402c408600680e1b2541071031050 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 156858282 1250 156857032 156857039
    0x9030304021801030203070306021b07030b100902030609160c0501051014010f0815010507051203011a0c0d1412190c02010c020304030618020d0309051005030105060904050601030b0a 80
    0x85005038426140391103035650010302404000b40a02000f03515030011907040011542076009843c45441500055070441e170002d40e43c9240050740e0303000b19500d160500070070506034407001c042070040c249000e080d4a5403908800048040340f00500301c0d40d00d40d0801100d00c40340c5100e6011041c1a50f8404c000300b01e5801d100c03859000d09401c621941c503010114600c1d902480d481b5510b15001005507031100c120035103412001d03424480142c0f140303a04205c024000c900104808106400c01d41280360301d616900c0d4117007840c0801d4000d562a2031180e65500704000e5505840000348918401c03030a19140d0f66040d180d800d040d6103442007240703012800405500b4050400c80c41c084421509502260420040120100c16400e89000c4031048000d608180010800700310b4503042800044540b0040032001c210583c0020340103c2c241b1400d030300140c40c0c0b400c1440f072800e00d241d00c11100318642c10418110740c0361100050a611a00c5415400795880c0c60214020382d0003600500410a00140395603a8641c6 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 156859532 1250 156858282 156858301
    0x40507090f0909050106150206070c21081b0a05070303050c16050c040509010c090b09040e0d020601031e020919060e0108030904060e0603030a0c14030d0f1b0e2403 72
    0x59843e800e03030b43e179481c0c414002070f00d540c20144c41c60403074610740103000160b55192080d1140481040d043d13501c0c80d40e031100181c0d408000c6003c8a840e40c0d040e224a8400e0600d4240d041c0320750002c11030b88104a20410440f1510707904241034500850745440c010a03160764002505442c0e000d9034911400707505c007001080d0100700c0042030b9440c1e4840165400c0183d603484070415400e980c0341303504100101e0900c0070140100c544480091407484c0c3c01400c0440c03410741c0c0f4000a841e210403940103c0c01a000080144200852045001d044404041d0350854800180d00040e201c6071300130300540010180340840c440a0069604000010003a10f5005441d80d81c1d20503480da181d62000303501c0c5124920384480800d0640341406000d000c0c0c0405801181007526900081c1c98241c002c040270b0316181c050f07a80c81c900384002040101510050843d01041c1c15603150400e0003560b01040d540c0301044100c1e00c00c2d5481503441082449003107801c80741d04100e09140c042c0c02804184a4080120b20140042001031085 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 156860782 1250 156859532 156859541
    0xc0309060c08161b080a02010e06090f0304090f09050607030f0605030a050a0b040201050d06060c030909020c0c040f0b03190b09030712030504111011060a06060e040507090f09 77
    0xd01880e001e10101c0c6880e00c0803501c28800b1200320703442140032480c0d4908076102e0006028059040c035103042e1150001d454450103a0031900c034080c0141c0d1100044507840b071042c084640c2007150f503401000a2000564020740740e008502810b07030429500c460181400e20690451a2100d03007102c240c0e100d074100160010050311907411104640c500700040050503050005001111540040103000f084502e41e65070700709040e002e48141d04002045c072200c0d181800c1482050018002512616421050307807501800c000c596501180600d40b051000054050b40842d81c0702d448401140c00040140c40000080300914540007078075018880c0d4035000c09002080c032101d190550140c50300d50010307903078100c100b503880c4201b00300186000381e601ea203000c40c54082d40080350081d1040c0b526808246102e804581c1400e584100e4030001600e50f000c4003c503000c00c2c070070035802a0003100284a11030418001810201c84915a07901640d9201c000035444e600c100c084402a04101c05080d02690b5140700203400b80 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 156862032 1250 156860782 156860801
    0xf190909020a2f1209041407030c0206070804020913150f050103020a0e0403021f0204150206040b06100507080d02040503121309090f02100905041d010612030503012102040c03 77
    0x31000229000b43e4269200c00420740803c140c00140f02140d021060040140c01203281d01d5001525045000516207000c17460510414150b640080c1c050240c3c18000e14101005d003c5a0a020300c1005110141c1c99100320307594058140d0640e00003c600c18075010224000c40c2c21040c214034500452526030003640c0c1c000c01d04880c000c07035490151984034560f4148003041628011b015a11980710902190800800c01001101d1070000508050b5241c0000da4410300344403071080141c11030020001004101c0c00c2490b00020144c6640502080e071450107001c5104140001c1c051000c00b188050070110303690112400b40c00c01405271003d0000d4003143c56066040b1240c89010500b9281012580c14020b100d0610702e6600803001c080c40a01740d40a011502507200404000c11140c52070200d15a1210b015a0302c00309625408400d056200da4201c41c00c48207250403481000b03100d0030404010035804003c0d80d065400301440c00c00074240107c40f2640c00241400003c0d0810308203e454001550140e2182048 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 156863282 1250 156862032 156862067
    0x305070801050c2506141f0f120206040f1d0c0a0203040302010c08090d08130503030c0d1b0f0b01030c060c0f03030b0102070e0f0109060b0f190909020a 67
    0x11140c603064041c0c01d8480c00c0f500081210740c140b005115030300701c480e80300d41c0c20845480700906004294461200b500c0c181101c40e8107082c82c1205200800000c006c8010008004400301f81c0d81c9030504400c010b5003002d9102d01206042c21507600c90035503981900710380c003c14804070503e40c6280d070790306040e00c0c0b0540c82c40c00d0380103401150001821105400c044890502c1c003030b406140342c207046a005442c001d00c82c48081d10070780001e000550080d1101d240030360105018518080d11142543e80081c505100b81d04a180250002c1c4181d00303d583c0c0006003421041d0711402c0005170f180020540c40807080301c0120103030800e442c4610070414004900e0215061302c0c00b4644801c030543e22047d040c0e50300c071000c03c4010549803580c003c91010a00c80d41c40803840040c148140c840c0c030360b995500e40078480c10580e0004da2082a801c0100000c2403540320710002482e20701c00d154101003004100114a0040c41400060741d500e500603000d04600c9064990090b042e003802c08c54603a603802c0d02c01007000c907810302d602c800c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 156864532 1250 156863282 156863293
    0x30c0703050c011107050d170a0908010606030204030506040609050a080304030e04060906061b08090621070c0206030f0a141501031406030a08090301061502060a060b180906030a060203100305 84
    0x1465104103e00b404c60610900201200303440c00007801010350f07214600340c410701d803841420050380601c20000c041c0784006546600718541030816003401c5507107560141c0b040c18030400042000640108000343d1007034002c1d00c001802052800c00c2400c01c14121801000c1000001c200010180c0010000c10301c64011360f0304010894070340740444e00f01e4107140940030205441c0c000e68414455080b104413070300e034403903c170361403d11a0003000b0410542052840250a164020655100c04c90b07500032607601848501d46440f61501076000700b00c86210240c41d094030540307601c1c0050203ea41c076410042000d854100310341064030b803007490b0220300405200540d0000303003003426030146c4540d040c03140c03401180020054500e440441c0d48130031880d84010702c0301c3d41554032000f0000e9042884155044001482d802a0001d032911f8400907048500641003a14a1a001c1c0310440d0030a400348140c118080094407425a03940382c2100092401003000e41c0200031500010070854800c00804c604030450384144c0481f40c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 156865782 1250 156864532 156864553
    0x91e060b090105040e060a0905090c030f0102130506070c08060103150515010516030e030a030807021c0909020a0c0f21021f110d140601080c2704020408030c070305 72
    0x64030301c900410640041c8050200b0300c40d640c103100b041038100000401c2403d241d6561081c003415200b00312440c0300e55410170707410401c4500301401a0000d07080300d20000c51500c0d000c91082d0f80115070300e01406000d0940840c2c0d44003040040c0400c103000c4d00c03001c0211141c0d9a500d242000c02c1741c0c0b101d80e0380d120080c01d00d004a44501103900b03004648945c16180c0d50306285c00c11000f030000348803c03503042c2d08110038006445020b85051140b0310b80d0501a940d0310300740d803a160b100079250205441281d801c4401c0e1031100c0f00082d90200c3c0e56410f07030fa2501009a81c44c03100da4002c940781013807410041c10501c0c4040d4210200100c1d01245040d085440c1411000303030b80804004e07601c03151603800c1502908182071568000c3d88c01c607882008142c4900c2d4285003817501200490044a951240c0c00c000d1091041c02c0c00207646c1c0002c040c3c1d50002c100d514607031401c8164440325045004601010030340310052016824642e407941c066a02400c840b07400c50342c64940080d11956149090311090f80d480c000d03402c421 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 156867032 1250 156865782 156865799
    0xd030b010815040f020f031816030819091e06020c0a121b030506040803070e0604051003050a020d0e0303040b0703060302180703090c1502060603010c02070605070c091e06 75
    0x5074892000d07030100e920b07400c00990034000500880b00095203869070811098024421600140d40984c400785020b1ba104030783d000b0380c2c901e084400764a1300c540d041038900400025910200700d49104540d0f04a9080503e8507210940c0c01caa02034001d2502c00022a0200a9501082d041324084401683c00c5035040c009400510100d0b200342e0191180c1d6100407a2134001090307a81e8418401c0c0501c030102c03843c295607039440751420b1640030f4038125003028002051201296121540d500f0546044802c1c602e428a0000007868522880d0352040602d80c40d540050114840ca03816a0080207210030103100048001d2910341e00c980c0f0486040321030300710540c007040c1c40d90b100784181c406a079409403408090005d0915440e402800082c01107041544079140c801c0091904d40501005080361958944803c48200019042400040100740240c1c50094545061070340042c40204540080c00d0aa0359040281026407040e4201d401401b00c0c01e04000034041007000400c000c107446a2010b81c10860280c9607480d8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 156868282 1250 156867032 156867047
    0xb120106050313030e03031312061103160f0e1003150806010807050607050703021c0b1803190e180906091501031118100503011512030e03030f0c0d030b01 68
    0xc40b0038980509940c400240517101520590000a08682c18900920050340c000719454021b6440c40014101c240300f04100d9018090b0205070905e0324604501c2d0581c072001d40b8165940b00c41003040300481a02e81c540c1e014001c41000c8100190090044020901020f8061308200f051150380010702c5600051800c004584107041c1c0300444007400b01d242c03030202042115044040141e030310380074840700000107a480c10421052081002810140c480550070700c480103090003000d075400041100f82443c6a031002008440420720311500c2c0788c07c1c9224440081740c01c4e0900301025900456a102e9004601c0c80c1c1344900c030300c211181022520030b0740c0d841881c2612100d02c04148c4d449415540b0042c030001e200c031880b00c858144042c2152448c030208042244407176405441d400c0003014107100c180b0903805c1c2030151400c1006041c1c81c10301c00d9464026084800b405903940501000911048008035a07410b0080740c50415614001d15140c8012044154481c031503c942000441d2a20b0019541540280e84 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 156869532 1250 156868282 156868291
    0x90c0d020604030201030c12020a02070e060f150a1b06020306033a14180a0902040807090906090f050105090c010c03120e010e0f072313020d06030209010b1201060503 73
    0x4500300b0749164015400b07000c0c40900d18080c05000e009901042000344050800c02640e41d0003020051319000c000050040003410a0f4018000341d21544200d0711a111180030100081070b020780d9920100d1012602c1100c29400c11f4400000c0f60820001d10989801850107000110b05580c0b0b86015800e14001c0d031084180d40c903603a0004403119480d03039529041e90580640c002e06090706032140b0460240c0d200c1d405008178030382c80850a10000c0480c104030710703d5000352021160442c81c050400b161156160000c0c030583d2002030f146c00c80a002c00145801074801103134071500081d40305900740b4000d4041c0504031540111442000140c83c002d41c0301c3c94280c446103405403a8551a00950685100a4505601103a5041d904c400000c4d00340c100c104806102e0014840c003030103049040080031101c0c000000c0c0c0e43d1010703945d8016040d41e0f90303076170a944101201c18040c0060356030440750b031a44054803480d40060b5106c01c00800000301d00711000700a25080d107074520101d542e0303a04d1b20030a650038002550b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 156870782 1250 156869532 156869539
    0x1050301180906110403060507031407020a020d0224030108011112040b060109081c0909020403030206060618150406170f061210050a060602070f030807060b0d150203090c0d02 77
    0x214140100c0d01988600302d501d02410b00070400e00182c0114803420b522a50048a050303603500200070b14140d05108090607240c1000780c200c424101034100a50320010040e01030300c100c0018a50608640c0d504c03042e060020300d0307603021420349044200350741c0780d0b5007092041c40c44d15400e103012001407400310f004891071168641082c20860f250351325801404a0000e101c2418400525000705650f04100181303c1c00010f103070400c8a01c222a8a001841c4281642c426100d407030060009200094001c07809550103030701039a010b40c03070f55140e6200d01d030030b0340e54804c5607078128014181d04501e5800420050003514101d44031801720409010340b03041c0e01201120380354844c805010102c1e2a510b841407604252102c0c01080724000e0045950301402c8510070f403140a41a9591201040a0303601482014001c0c000110081e00e0305186448601d07280c4a40c0c14020201580c482071305040c0d544007030300410015080660200804c0f56030982d000250b0098403034110601c80c1e078140d2043c51410000072181a139015 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 156872032 1250 156870782 156870809
    0xc0e130305122d0109060b03090303150105071502070b0609060d020108060607021207031208090705060304031e02100b03010612081b0607020604020411160f0c0f0f090b01050301 78
    0xb6010382d19600c101600851450002002c02080070f50505281c1c1100d500c0c110040000e549003004207021985554001a141e56003403041040420300801503a5014501c08101030914240310012595072207103940042c001030722413018503110601540603040440c40b0308040d161300c1e10784404101340c12804544165101d42c030b01031103c1c010b5214480d100e8220001a107150f06010f0360307a000070b07503112141c00d86c080941d004a0f030030411301c1a141101140c2c100541000d000f1418085141900c7c2c4007039000d01c1e4007480001010a040603c54031884549201c00c1601a500104d5107400941b22a1245425607840d03061204c400014607040c4960001c4511130074051444ca8044e0380d034044c441c0c102403240c0e6030f0741c0c00400c00188011b2091256a00c902c440754040c04886c41c061040204035215485407143c450f1061080b101020b500f03032100c0c100b007500803101aa07014070340e00d00b1500180c1550000b000b142584400091040c032102c072120180d5511210600402081d200119044c0c002480b44074080700b84c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 156873282 1250 156872032 156872047
    0xd06020c010b0607150b040f0207050a0c0608060307060f02150f0f01140a0e0a021207020f0d0806100503090109150c140304030e0d110907050702041d060a0c0509030105040c0e130305 80
    0x55401244903074000b40000c0350b0888c24881d2401281c100130425144d80d04800c1455003000080e4070540d01405441c1044001e60601c071010a558002d01d000f03260900c10240f6100301c0f40e6000b04101100c911556602200f02d2400301940e6403801d00a80321000f0030300d1040008154407032000d0702c400301860003504541000e4504801408500c00190002c1ca0841e405c00005401c000c003601c0c043d1045180c2d80003044450101d250483c58200d0f03071300c007003400c02458a0502c4043d94520070550380205103460507541700c1c1c490403403d500500d8503000060002c20612620b210202486c3c04c03058a00d8040e482d8082c4280003070b070b4240e556110442c3c0c000c0000300d4101d441c078000c5c90710910050040e4001c20610f00c00e03558150101c0c6c2640025203801011849c0466104110f02c2c02c7e014011030200c1c04c140801d03401002a141c16540c2d0300207040c44000d540c940c101d10344128130680c1070b101d10010040084c0440d0800d410501e84281c514018140810004e07070000e194020000d80900000e030745613490320315000f00c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 156874532 1250 156873282 156873323
    0x10f02032a010908070506010b030c040308030a0e0114090d05040e010509090a17121302010c030f030b0411030915160c030903060c1d0d0302060c0903010b0d06020c010b0607 76
    0x24110040c490050300e01d050307480701c4107003480b070061002d1241c0e004540d074402c5402c00300d141450507032140e081e15804104001c0f040b113659003030714100c80d0701580700f039266158252000080e04000208286a6190034200c40c0029070f01c1888078041c003155000e60b8031f08007005c0302c125540d00c128040d0280b0010701070010012030810850055201d1420320580d02c6840496881800b84081d40011500c01e20f0040760a10280c0b8040c45610341154018051901d540344035400a441c400702c440300501884545442c0d812458003079005407090000007801000301490b8906910790f56002a00d8001c0310380301b0b00e144071104103048200140224001000207412601c00402150360b00303402141202008910400080090303807a01940d260700d12070740c0701d101d40380c90600304015841190020b251f103d030164803400000709802096442d0080c01c4603030f41958555003440400c0c090000c107003407a5004041100c80c0014001d40e80d001c1e00d6060038820092004820000422086000e41400640204922034605d01000d6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 156875782 1250 156874532 156874567
    0xc0114090330040e0106020106170c0904022103031b1312170c1e070b07020423070f11010b0609010c1103070803130506120c181c050c010f0203 63
    0x2c00610382d11007410241d440c10b100c50740042c0e001003032034012900103200c07940c0c0a0141d18090600b81c0d00700c50544401031105a5180071100380c040c0600c404001180654a407250120314407400d2044c0c2c0c0b1a4400d02051403540c0c0d80c0101e4807606180d440501110b280e200318001c4692001481221403c440d04000280443c10407402d02143c1340b51290952a83d51144d15010700541a2144090305e0300c0d581080f8624070b0710304e4035020b0781d1075a040224107111844000c8280c07242c20390190b40004078040d0b00021a0403910b40040c00f1500d4005010030016800d921071a88030361405160344894400c50310307035145800c0e55001e003031150384040c0501182d8030952040301182c023002d000301c8507034103040b44160211f8200f00d45500a00303074a4000041501c5c40d200d800c0f495000802007540c03044d00c1c18070000c140051039a00607200201d80c042c005142c07454140c0780c504c41103007000001c240c084090b14400b144007104c9000c110840311401364588801e25076014414182d82110690051843c06a85e10004e04071070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 156877032 1250 156875782 156875833
    0x1b0203070605180a032406030309090c030e010e011d06040305070204020d0b0405041b06050405030d0e0a0b0a0e04051e0402130905031204060509061302090c0f0304050c01140903 78
    0xf2455440380021342e842095030002107000b00910b14030b4104079941030042c0781890155003071140c1410401c20020742c1c80400381003103818000c000a1007104402c8109e0141142c040600344560804940c6e00710300c0700c1980541d804150421407402844429501035407901c0d0101d801070081401846840702509164005000110800c030002514442c0d950000f81140c44c15101030310040d11055100101e092114407078009032010f42456402c00b032806e0000703540e8100898042c001c00c014018016115191443c000000e001608000f40e203441007010028104034504007401e10642c102800300c0c5030140c048043c2035002d0542c9169038010380d40c0303800b4001e004807040366880780980d0b108014004660140098280805c1039148004141001d04269003a640c01615061a903000b04040c029000d03031001e9850041780c0d0594404074141d807000610311550003400c08042480c18000200030402c440450100200e40c3c090b202d1104800e840307200c84400703000e401480c64041d44000d6418200314000104030010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 156878282 1250 156877032 156877057
    0x151505090411070f03080604141501020a200f0f0d1b080709091209060915170c07051203010b040b07060b03030a0807090501020a0c090b010923011b0203070605 70
    0x10704030716492004266000c0a804c0d140813080010300c07410994000d111580140c0111810b0244d81199485030300c80c0c00014100079060041d104000125034003d00c1548070003500010b40c400d20b0070811520500320084002d5061003540300203031050b602c0c40e000780b0902c1020405041908103001c5503903403042c8410300c41c00880702d20070074041c0041c80000c20040741c07002d0542c0c940085400750240c40d21a000c0d0b616000c03041c050111704001400041e038425000030888511022140c0405061031090f121040381413101c8054100c2c1d40c0c1004180c0010500905045101d42d04441180b1620b600c1000c943c0400c0c0204814500b040008102082c06880a02102030084500084058811b0000f9146500107200e41020070b040204222034181c01c10701410040c0820f0016002624a036a68029000462b0141c0303101503a60302469100c60344914040805000d0041c000c0c04034489003031019804c01030510a0b980043c90320791346080d2020b902c00420300f541d54040c0007003803658289481602c2ea500007031700c0d4044 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 156879532 1250 156878282 156878291
    0x1416090302060406020106140321070305070f0305031e090c060901090b070c050907030b0105070f050c100203030115020f1504030212030a0902010e030114060103051503010207060e011515050904 85
    0x1d03940e81e00003403009000075000003d40b0b0b4902030326030b07044842200743c0038840e03000180801c8a1607030b0304101200100301d441d10142e480105140070f40e000d0003036070400380805506070100070815400600940c05080c80808500700d6044880d82040501011500f00860b5002081040f403642010000380010010506201c0d10701d98507400c9500040e04208015502c008079a0380c2003040c0d04050f0481d5410020a01d030034000303020b0040c00a8603a1040c10b10041190410b80b45d12010700405020301004000f00030000f048800c0c103031000a541c5e810071f00070341910300380d00c603601e451650000411110000c48600038240c07502e0b001c28031009640c0010070584c117500540707224021070440c80d40150f10549011000140b45691800010114946400f80303d0080e031401000081c603400304000aa0710000911300400c0c50b940d00c941488400d80380c948541d80640c000710340e2104018060300000850300203600200011444840780d0000d00c2d40300d00c11844203200c0e40c40200d124510031001407094500c041d1010a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 156880782 1250 156879532 156879539
    0x3130621050a0504110907050f13050405070e1f02060a1d030f0c0606090c1602030f0d02150601260a060510020d02011a030c06070f081219141609 64
    0x10241d03802202c415001c0c5595204020802a071005040c081d03000c01c0d2440542454160f402070401c1c03040b034440c000c603888003080101c045e00303403440c1c0303000036000240003403107103003005800a443d01c0b1960b007801c0e2250146200781110702d00c9140103003000f0a46035000300101c2c1c4501c0300e50030045c100038002030082010f8103100c4a01c1e440c01c2008203185100541c9030f03079507211a406103d04041001d090300d031182070503a050040d102840c0c01a20480c604004407030400c1c1125100091604030916990b82c40390040c515040400794001c42c101461081c0d0300071541d019600c20300111440b03524000103003010042e4680d082c4a1201010107103078000140000002c3c0e040c0c4840000d41034000400380d11005a12210080000c2e070380c2802280b0400c2540c800b00b4004202810010b0707201c4031020049800790f6004103100781400302c0c0c20312400413260003c3c00716680741403003080011f81d148211606500840054110500d41105210340488440704950180c0f1544551140d40e0200c00d0b0355801c03400f042021360010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 156882032 1250 156880782 156880847
    0x606040905060307030c0f0807080601060f1b050610260303070f0c050303010f06170103021302130b07140d021b04112b1808071b03140304090b03031306 67
    0x21b00162181c003110f400181e2070f001c0c155180100b0b60700001c406810180040020a4205a01d503074803e02e1410406145418219105011164180c01429a120b28010701004030741c4050700720140c441d00784074071030100f100d1040044041c89000300b5000d2640100002440f0a20885c1c66840c0b01005252400320800c42c1d407103451a5410a8006c140d614000070001c001080d0850101229825a02c291700c0007989507400003100c1c51415400400751580000d140c0d50203403c80c401d02405450320824407a1502c046003400c0b201010121110001442003010344200749000060720040c01c1e81300c08032060504184803d02001e0400c00400c481030348424080582441a00040d40c040c803003030050b44201f500c1500350715005a070800c520300c1058508110a0001041030142203c01c00c2c1e0b013140c812800d80d03600d540103440d28401503101900c800c8841c0e074070740b07401440440203100315a180d0105100301c52121080503200d01c02d100c04580800d410030801c110103030203190b54a040500400c150411003074900d451 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 156883282 1250 156882032 156882053
    0x11060c07030c0915120f02091008030309011a0306010f15090e07080f07111b06090d08030103060b18160e0315090706030e100f060306090807150203060604090506030703 74
    0x20210030307510340040c141004d100072103d0009280c0e19410060740140307a154500c02c42003500003e4082c1004e0800a00c04080d462484002464640c2c1120b96034600880540d0082c0713031074400c1042240200705c031007009140000b14603043c0c1d0346854440ca403a91170508018103012048007108107200c5001000906000034558161041d00c1c02d40320101c07103180410017100a0f49000340034409014140c190469000f41c000354112001e0030744d00c19003031108444d10001d1800d0203901034581d4440003281d0440200034000c2c1c09141200d1141d130b400c0c040080c0c8a0300308140940c440725101f19200c0200c001070440b01041c40c04101411550a000610711300c00b1010130f040051403d044d221000f00303102441021281000000b004184529080004541c061080e80d1141440130070b0002054a8080b11008069a540048015644068204080720342ca18080b00b05e81c000590903203840c504506140c81c2c040590080340d21071540100744501d02810070350f030700c80100030207058142c01d4801d8038404000180d15101 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 156884532 1250 156883282 156883289
    0x1107090204060c050c03010e0a080903190f0b09031903090215040f0e090309032d0304170d020c0604150c0b0109091b0302010c020603040302150c0406020f010911060c07030c 76
    0x12110040310b03a1303041603450540c1c100681802a858140000c8000d1404a0142c1186600c440d5460303a400c80d181c00039240c5042c81c51060107031000440d9400401c50981c1c0c1b900900392060f000e10240d551041c20103926400788420381c800c07401e1900340c40e001d0b0780d10030361000212900c0113200c40c40c1c0c0f2300411703014041c03604503400c03c0d091410000420300c103000c0f950300030603404031070300340154602420b84003c01d0312141701100304109214188440110041c00b6512810380352544405c490b00c035a665040381e080f06401042c61044e5028410020b42d80c2d0384046034807182800043d04481ca003030f00c0c121041d45404a46c400d001c042102c3d40c650080011900e015076402004215400b09545080c2c1c1094131102c10408510740030300410003420401030340c01407407400d0103540450f516604d82d50b03507041c10303400c0490b010340c1402c10b501002d0030480b5a221280c00362098811a501300c946043d80d50104908890f003542014100150f8a80f41c0700540ca00b0030000c0900400c05030507074000d640d90340c2c0c0b5124105010340 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 156885782 1250 156884532 156884537
    0x5190302091203090a0b0903100207110f1002210c03070b01080706080915071b0303050702061605040b0f120103060204030b0c090907080403020319260105010f110709020406 76
    0x201d40c1e0007032400000d03540c07958020030091407501884100084110075203200310019040d01147c450032560b024420080e00343d000740380c00c7d07541d111146002d500803403103107103954440c40c98414581038505000e10255031241140e00100024a130f900c600d20103400d8625040c101d405410000310700a0034060000c0d107034a03440303540c00702c080d541400000c5080034082d41000040101c51010022100c400040d9003440c1e905206440e802a10742d1442211207032a8121041d40000d08501610105641544418415030256080d294251600300040b80074610021940001038001d01081c0012a41540202100452882028a040128142e9081d83c040990040c0c0f4410381c00b1808005110610811680c040c600b400e40c2441d02d16010006401c00b0b80c0a0a060200b000c80d0000a04040c000c10440b070541c0c0178845900100c16809400800c088a000d0800140b01080c290790030100059045103816100b058403001c1a10345462002c8031805100824401144035541000501b03450341e02c010005801d095 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 156887032 1250 156885782 156885787
    0x106050a0906091d1506010c0602040e040302060619091a1816020d0516060e01021308100b030606101215060f09050603010b091f020610080c0108010306050705190302 73
    0x500081100c81820b40841107409140e1031050b50f110103d00100c03111784d00410240c080e01c9250040714620111a4024801c0c1d10020b008900700b0300d0401024401da1003a402c40b03100c0d94030002841580d44440c10401205281d021007403100b640070350007510241c0d201c09000e8004210b15800640302c814040003020f0817004440501040305c81d03007448031980f010035000401510903010340c01070442c401d810041c41d0110300d5030741c40c0042100c00d41200c1c468001c150001d544a55044d41c42c15a103a03014850300d406445103c4100051074841c0c00307001a0310724024094009a607401c400d000440480745280400c10002d40c031880e03101442c0d40303e844187c4002c1020100124244038014090704440e041480510501000030000340e9107400403281554510381d4016114107008010440c6102a0000c08604110705102c1112541d400507003544240340c0aa010b100340f81d5580030319500c0b00740d207904090000b1004d10051000c10035503080a03410a2051515500d006000e48141c40081e14400d00ca40001e42c00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 156888282 1250 156887032 156887039
    0xf030801080d0807030e010906090303021c202b09120c0c14031609020a180303050307030b0a091404121812020a0b03040f0516051e030106050a0906 65
    0x680414094240c41d0000c14000c400418058032003c801481c50b0308054444014146012080d004480c80f00d910100502a00c5002d24000d07002c0e4011100315180034040c03a1080311001068040e602851082c030082c0400c100c0c16421100041d40042c8c00440c4604029555040843c00186c07042c044484811000540110710b1501940c469200f0040300108280e4625a00100d1042d86907042110044001c0d40d072001240b6020a040810346c5032141c4d000e09048000060700c40c025001803418102540d6000d00131003c134401c200c045821800081c00290b800e00000d0b02c418020351058022640084c84101042d5440c081003050307400c050b044000a00b011824002040b48241c06240030402a0500000c00445e0f031386007080e84bc0f000e00c100c501401c10b02c081d0a05640351600c1c101c3c050025585002d9903480c16040039030280c203440034220384030304c90041c90f5a0034140c0108614103031540140b21043d0350b40784010300580c0c0c020104190741e042d5138540740000e180d0f0315004060001c140c0c061000c59685d14 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 156889532 1250 156888282 156888287
    0x120303010f05041e090201021207030207090506060c030715020906070503090315070f080c040f0e0115030207020f0105070c0f090e16060c0f05010605090106050919050108190906090f03 81
    0x865406140103a041030a041044ea40078843c01109200710381d0b000614440e2800103e250011460350700070384140c0026540f007415404200f210941d012108284525200d0f00184802485900c0103208990070601960000803041d004e4800071190310280541402554000141c15a001c01c4044409520004030103025090a2110500c501c0d8050f042d40c59916040101501024001c10b051b410001140001084030005400f07031005051401c0301c06944907211041071142080a01800d03404041800b600000f41e0312a00803600f041c1da000d00b141128149650055409804c81503003129083c1400c00e0104005d40d824107e0b0000305498040885c448211091345400d1218400b02080d069103044014001d035500169000b41c20ba40c420b280c2d0f402d41d0003d0a0240c014a03142d0019035200c0c0d502c400018180b03a01501804e4120340890b00309412450004484113142c1452060320301042130701780083d0003e400340c081400c81d40702d059030100e40c0301216640d1900b1135042400c01c40c0c4410015200324103056 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 156890782 1250 156889532 156889559
    0x108010c0e0310020904090c06030b0a0906140f180403050a120203060f100c0b010b19050901021e0f0114010e01050a1a030709050d06050103060e0723010e12030301 72
    0x85460500080001c0650042a1100140050b003481c484d00010320070000e0321141d2043c00115040111804c400d40c4403071008002d880c0305a05280316a0724004041800c2c03100d48030307900455010b00d036041c462906013418045110002071003070b6480b5040140007028281d04901062040d403107541e40656403c1c50301009441900901c881c00c000e10b10600410030b0326210080040d1007000f04480391140b43c0340d0120304403049814018003c140a20103000002c010b91080c01418103010b840b64180c0341d4500849044406001c0d8a91581c016840742440c04040c142030308124144803508026900c00994500420b400d4400b00c210210b401100040104082131a14800d02d000d0300040740c540380b65910340040e003c00026a05080c28100e940040410401d9000c0c2010384020f120160442005540c9800d1070b00040000b4131007602c41d682881d082c1542031002040d4001a140700300700c4442d100440310354010104940001032414001c01030400105070b6030380754980603010a400000e561329818107843c2031804 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 156892032 1250 156890782 156890801
    0xb060901120201140f07050a03030c03142205070801021b010605090f0c0f070f031d0111030714030d05010807080d02010b06040302061606050a0903111207080a0903120305010801 78
    0x107020003414000142e81c4000c50720744c52a05032010585405402c441c1400b030b480b0b1904010841d10074a0700e113108154064019010070710032620104010311a002800c0c83c140304c111440e14951030b000c10b44080a024618900014501401c100c922207a100d02e015422030740000b2041861000603c00300700a0802401850081c00381507802c0d030103030305200c0412648c0d0007000e0b103911010440802c40d0181e038203f80060340d0400f0f401001600221100e0300700682646c00700d2603c480d19036600301d001c042170f50003480951420900b1100442c6003c0c07035605c0303c07401640640c030148150300080120709802220760103001e020706681c90242110a1829001615009210b03c1000c15641802c00c840815a41e10b01514112031b015038040342e130785001c040321030001c100d100c41c000e10003450300040c00f048e400e50b54401300000c5d20035240c08030340c040e40d495219507421400c0c3d11036540540c2001108002142e04001e0400c8200e24100180d00a490b551500440302c03c8165220000b60b64100402c4107160900455101 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 156893282 1250 156892032 156892049
    0x20603160e06030916090207030503010b18040c09030317010308030a0c090905040b0106020d11030306010e03010207020301060303051b01060e0705070201090e070305070e041a040b060702131406060f0711120a0b060901 95
    0x20803008c0d68020740710b400305116810003440c010070007000084c94148800740c00a0000c0080049050421014100c08070360300054001414a0080c06141c0702c150125034140c0742c00054580c11070351030b6030b114000f50103101040c10070001940ea0005500d00107000380c0e0f004e944a0b4110200c05d6040280091170800081120020030625004900d20764002004403074011303e003842c081e507030145540e011074003901c01c18200035010f41c42c10000000341741e030190180c2004141d00303c00407170203400f2a001a080e918540039120b181c0203040c000c522540e0117240104462031040c14a1413031241c0c1c4030305e1558800c0044600b100841d44407020000782d15440010303032800c071070100e800300591a010082240c005c254006d14900456131402c940304d45a54a4082e40c42e4181d0061400c00d981000705080f10103440d104200304402c0300c2c198042503152510070183c40040f07810189090400809403912280301d5048084d15820884064100051520a0109525140c015a024861814202c040c4021010141d001551 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 156894532 1250 156893282 156893287
    0x20d15050f011e081008030a080109060504090818030a0506180d08010321020c0406181505130504060b060a0e0a590403020613020603160e060309160902 67
    0x30706840400f51884070011841d00340300c1e40d92660030390150010b00e500716030700500c00410038105296008025a041e108050b0042c00000da4610a110a44400384001040d440c018000d811800412045000680d10018100e50f20200ca07030701d442e41407038020b50b80a48500748058443d120220108174201802a8ad441c00380d40300c3d803642e1602d05180041c0b20107030f10960541080076802da0b1003080b44107240710300200100082644c500d03c00c1001211420b100501a003090350400402c00002102011920054100d4940c50501841080100802403040f107069035120148410303625088003038204403081c0c0d00d560701c5604141b0704221100360b407544207103141e29101c0400000c080000700e0000781ca991140328005015a03011184e62030a03c0c0f81e0007a80c0e020050f207240300c1e04201c100d044500030b078001c0e025240c00361907101c149464182103101c0030f50040f1307040010807200340303ca640842c10304004e03282010140380c0d850002038066105680c480003c0d070003030502e0750401d2a1900d41c074001f020444021072 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 156895782 1250 156894532 156894557
    0x9050609040c090207110307060905191203050724140a09030e0d060b030f010204030b07020105070e010e030a0c0e150405040507031e060603030801090501050d17090103020d15050f01 80
    0x49040300d05010b01001e29401181c514100842c0c2c40401b404040010700b901c007201d8039000014110086031040303d1140240241c444c0f0440b00392480b480507240605441c0301014000d4130265401d50080c801229260341c41600d0210f042c1032002d800450080e00d81011900c010407401c0c0710114000036000b0b00c600c620300b000340c60009030040030303a005100e01501c0d0740a4034a82820400010285185002c0e0580140d00e03051465080660081080e2442006d0107007107a00c1e4008202c1c00c0714001c4680d0f00108803110014241c540c01500c0c006000780d4018226480a203142c1e0307900d040085280d0209515584c00024000300700c3d00540c0d50400610300360303000c001d030f840c040c0c46035960f80700c152202402c00007000303070079001d1254400e44600c082c2e03402c60f005200d90703943c928000b05084800d01c248140707645040300104091800b2460700703084982005419034003400d10f03a80d0300c01c5d5502c40e1030028181030b4200a90810345031136001707174074443c04c3c02e050b8500c569140c0014000c0000700780fa1007a0402c0808501d03103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 156897032 1250 156895782 156895793
    0x90307060f0509101109060f070605010f03080a20010e0a05010b01020a0c120302120a02070e0c070503120910060b130b03010803030a09020102010207080c0a0c05010f020c010c06140708010905060904 87
    0x18110744603044011421403070780180385c021441501010794004400140031714002c0456401001258814001089180c0c1e0710200441e0304202e0b800010191501040070100c00c511035401034420100c0070b66120030310240101e500782143c20300001403406800031300c504802d001080c890304095040c20300280c40215120758481400c04e6550140107a0f5032030b00c118800515100300f041580b002c480954055865901201c065541c03110384c420444246600000140102c0d502820303605001da000b03008509004196190032885c040082c11821070348552981c3c94503141c0c20303011708002401d81e07005299031064510180421a4041d400050b013449041004100d4004000102ca0f404091f80c034000804011700e2004070b001e4440c41501611500000c0b9000c0d00071103000c5821600c0e9441001c5d04054141d03500c0040d00c409044540a401681100290f071240c3d5005940c8036030341d18402e4800003030001c40d2110b03c009420058841c1000520100014070650701c0c18820990402011110707600340e480c059450 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 156898282 1250 156897032 156897043
    0x190521040506041a040e0c0c16180f0b060a120605060403050a080d0207021801080136020a030b041211010e031602040b0307170d030e0606061c0203090307060f0509 72
    0x346550300480c0c00720894140518416203025020300070002200307040041c0806901d400c00e15a08d02c950040311200300e00c801c1413a409104840030380071041ca6007030706850340358020418880c4401c5203d0700c031a03c1810680e1144000d0401c0000381c0c888180c0802500910811a012070704402d02a0b02c00b00000d1002c41d00000740424501c2d40a41c0d1555030f101d10180d288041e010f5188003e4215500882031130900041d403460b0380c16180c9600007004840310303103401802589a215070041c1c2c03544540300000d00d002c4000d4174070305106e40040c0015040300d03526a2104c00c0c8a90456040d58000c2e803000307040c4002c55000e005506101060402400940004041280c8a107d942c491000c800e403003102040c2191134076001042e0700d500c020255140665601c07443e04100b0000202c929441c01510b84407000c560180c86085540da008074010101a5100014050709038400301c0701104050203a20910711060305030005520a2800c00061a11034a103442d220060310792000209a4890410003002129400000c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 156899532 1250 156898282 156898289
    0xe090606030718030c031703150915030a05030d05070809121b0a06090201021204030c03081e0c0109051c0f0c1b06080117060708011719052104050604 66
    0x1401580c9440c0d035101030f1402c03d030300580f860b603000c51a000042403000c02c01007081228061020a819004401d24400d00e43c4411907800904c64180c1d08902c06a060200600350f100303500b004491804006440020b140c207612801c215207940c000101c0301c060282038022150030441600700840581010914103403075028647d841e070b0b442403020450610208084c01c2d400100510001a251810543c1c1410000780c10022400e0f0301600c40c0341880d10300148110308680071242c008100e1600700e402c5951703802d107545c099078040d42c086080300d00007080342d2004002401c03407900c00e400000e880c046600c0d15070f04000c00700000b848a448c42c4010107903105e4002d9264020100b145c1f030b0030303030f9081a0b6240980c15000420242100d10310380190100f0301035000384002d41a540c40564803102100305c054003941c0c0c0c13102154080c001544010041110b0902c5480b0ba6030a6420304040d42d1000c0c0b2800328071001c2a03610700c0141c40a500003082e441c000000c003840f00d95a6100d140100b45003a0808000c15a240f04034030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 156900782 1250 156899532 156899539
    0x61110020a020a02090f1005090c0912030d110a120b010903020f030703060e0d02010b0303070807020904030509060f0306010e030601030b19200c0d0e090a0b120f0609010c0e0906 78
    0x50007401e00344240304503400f8a50003494213241c1d051410600c0d080b15030403a681e030248841200e021034545014180e00e44240c0d0b800981c0c616091403107060102411814170902d44c148001c1c440191950f8460003542c09e243c440a101a4452030300404c010003901103084d0b000d00740361a007176400c01281d034409940c400380e90b01643c2c05800031360024040f0b41751a8047d8030242030940b600d0715401103402c000c41e6256000803240d00a104500c0024100754032807050035030081800100304036100060a091004961140c02402c00c01d060110070303030210313609a11819800c180c02c80000101f203515070b04491a0700540c2c400790010720f002d6040d0fa60f040b8050801a184403804a01c0e404451115a01c1d500507205510080c030308609a8020186070702440d402c40d8000c088240200400d45c520544205100c20794000018070072009619680c01c0c02c8003c2c02d0741102281c01c4038000400800580c1e041142a1802e00c18070010506440e04000140c2142d031401c07000000c100c202c0c812a803441c2d03a142c80080d0001000c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 156902032 1250 156900782 156900787
    0x2802130c080f0c090d06050601030b1f0f02070b070f200a030303020c0f03040305010501050f180703020d111909092a091205060402010305070305280b13051006111002 73
    0x280003032150f501655401585c40502d90706a0380803c0201c0e0800c074020042030b28148034a4050600300180c3c00c41c60703014a031000da5004210030000c2e1080c00d90030401c00c614019104542c0d01c23490743c0703152a44141c6055480174102045801040301560000e060841940c0d0528460024080000c0020389280720240c205074011482c0d42101d0000d00240450024000072030366940d550f403a003940681801d01c56140f04964480b0b21207601d0074101c800203042020400034804076900d00f60300750029000b0520246580742d5400c0b000503010103141c002d095000038420600fa070201203003402022095503030414050a400c000000700c10580a08071040300c1c0c0d00d4001c40c41c15283c1c8510040362001010f501c0310800800d0090362400b80000499030070f015034001c0c1d90500860355100816803d641060b0f0300307400d00f4800c0540c4551030740440d456030b40031044002000b00780c0071500d01c0094401d43740f01303405020032540c0b2410301c074020386810300000c02080e640c10301041842e006110700d0345030001181c9504540303800 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 156903282 1250 156902032 156902041
    0x6090f1b030b0a0219081b04030c03060c050306100305070507080315030c0303130603051503060708091603020a0302090417040602030904060509060906061b01091227172802130c080f 80
    0x8000315983c1540d01f9000158640e652030404641005851000395941e07132030028680d58441c865022030784622400f400903850101603d404800a0100400103c00c01206010b00f4001449490046010320a200488484000b40c0380c00c250500301951185482a8401c1114061240788403090130f08032441402c00062075902c250040103405454490190b15008840800c0041900001014012180c0408030390034012068140300800302c0343d0102941c02061000e00b00018a0054040b590042c07203619000e80031703080034280d103503203401039000f00d00560004609811f2a092a100d9400200000c42d8160701d41d041640100341480d40c0030b42414054500095220500317540c2000401c0c1410103440200aa00d001e400c024050010041c3c044000407010000b40f80301d000c1101c28814107000d14003481c00181d00c1c0c5454224481d45492003101d9a01452400c3e52201e0b5144800c0c3c424940944510401401d49104100c00c14005101c40c500b05454490044001580a04100d078000140c006400b20b5846 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 156904532 1250 156903282 156903301
    0x9071e030b0f0102150a2d02040f09090b01050904060e0f07140301270f0c0b040e010b0702011215050909060f090f030703031d101a0103090f06090f1b030b0a021908 72
    0x140c0001c8444501d980b01f10010810f0720581c01082100d03000c0521102564442c0114815a140882c01800030103641005000500d0500c6a050300544100e100240e41008144100c3c10400c00313503140307051a002200100240c2c0842d101000034602d00720002c110300052201c056102d0b141d08030703209810700d5120180b4400c200400d40959441a00002501042580d5481c0800c00c0c0d80726028012000000d400002140714001054800550381610f80d81e402906484642c0300501c1040a007440b1f03c940444001402d445035040c66001341107034405041a450400c1505035010005000c481c2c10b45c0c006a20000c01c12000700a07a4401c1d40d051402048405003007100501c04002240400b2a5008071001107030880cac030581c81200141c03214515134000ba42c5248c01542180c400700303c054890040c000c0b6520020307800e0361090342c503107100e000d100500c524585c40e2034000103400b0120b071401c08000b15043c020710025201d1503511a50031502545450080108008920140640d104c1800040d0012601d2100c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 156905782 1250 156904532 156904571
    0x1e050402061c02030712020c151506120402040b030307020102060103080903070f1202030c040e0d0c0212030a02030c011b0f0c030e0613050a0803041409071e030b0f0102150a 76
    0x41c0148401c2d10241c4a0548402584141c612201048101c0542120b940d06c5000752421840e600c1c01511030903440380b01d5203102800c0186003001728445080110042d03034528001c0e00344850344486990300c82c40c15105110172034181400d4180301c1d50003400724070700513070780000d006042d40d0f40b041c007041c0c40741c4bc442c010030310f005a40e405c82503444010490105001d20401010036aa50003241100c00c005404014403040f0f030202e54200c951a0000c1480c1c0441600400140301e005102030040f41610000040240c11900a01d8290f801a0400942c0407211142409450003546100ea10349407030048505014140d420705140c50801d2014030341601c1c0500d40a03280801342c2d04000360180e60b60710f00c0c45900320004104c1c3e0041d140310766848a404640d81e4000001e85058603200508610300120002c108504510020510000c0040d60300d4180c0030394032058108440f40219440101d0001003420412980320940203505046611496020385407400700c0b818503410002a540000e02212007203040e80d04030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 156907032 1250 156905782 156905797
    0x6050c010e0a1109060901081e070b030906100e06030705040b01030f050c1b03090d060b130f27230a0b0c030103030305060d0312150302130510091e05040206 69
    0x140101011501030000f032405025251070116200c900ca6076602c401c20480714000c0c015020030f0f500c807440b045040d6001240441511031054219040c03180d50b1402c185d0b8580c011103503d582d030b420400521050b000500c020300054000c1961120b514540075021039507034401c074421a407040c1c0d112030004803a640258002c0f41403000c040c0c024401442c2400042083d5882100d4131030301c6507003a4065540c00785010007507c2c0c040c24010000248a0b002d5201c0310089e1000700c0c0c029038011001025500c511100c1d1007013071101021601e011907001100100076440c50404040f842900030001c640000061040d160f44041501c00d9400320b1030096240d040070700c0c0400d070324002003501500300140f100000a45014504a9219075030a12040c3c2d610001d201100fa0345d10001400f044503002c2c680303841902c40d00440c0205c90f008600b003402c650360f9000110304140384003410000720740d03400c1807120004036440c00e500035002c402c805000c0c0c0700c42d01c8040911100d140002403549c503a1000800c0c00c565a4004aa049 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 156908282 1250 156907032 156907061
    0x9030a2a050109060c0809030c070302091f06020106030201030c0804031b0c08031c180203060f04050309090a020d0507081909170a17100b04060e0d020316080c0904080406050c01 78
    0x41e400f4034a0700034000c1040d26046000b08002c100011901e20300002100ea0b0824980c1c003801d00340d85140d00b88140e0400242400c6c004aa841e041070031801c030b0207900c800081140b83d002040a91940c0005000c9416603102c5104003c440420023002ca9004070304120941454110282d074220b840c104020821860b4000d4801d902000441450701c5140640b06c283d0140d80780f0701000200032225200c00e031070700361440c02501a00f007000000c004440940d801c55115000c6c1007500c0c54018111300003990190211020b02d2070a07408601488000d0081c428964424100d040c18051340c141503000403c54850714105591080c0c07a030012600f04440b580c040c200100442500703644400c640b140141240c1c4010144071300310070300c0b00c000035110403010448030204c403601c444041c503080c201201100c500510070700494101c1141c200000040e1001c111805003100301400103c00281005015400c11045d107800714860311205d4284800300754900100e90480302203051099462002380300c1c81d8007410031985010003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 156909532 1250 156908282 156908291
    0x21e071b0f090b0301020c0d050c16030803010303110c060306130204050607060b090a0903050304110315180c010903080f07030c200f060304030905040b01020f0a0c060809030a2a0501 80
    0xe0309074004034040240c4035500400d1005401420a050803030280d03200509069010250100c0c405008100500100da950825140ea103041e07a03940b603488411aa1085912150000c0100280342e0b0242124020802a00250071074812201c0011450302004e091184280b42c8900141c840c2041035045500070003014002c1070311a032441c02c041000f40000000c041c003940d041c0001401c7d690707080c4180030300550b060712601e0844e00c554403942c05220300c1d0400180c0510514018052090340b0800b1284101101e6600c1120712800085032410603000400e4a414000340315014400203025070103031182e181010603c1034a4007820304044a11070b481030005815030580b124003c02040d034038040125000400d54018085100c00c00078402144411100640090417543e024061454603810134072001034144100c07590950b2a40c40d090403d40d02c4501128452541c00080001c9600214100d62203030660024504200c150300001d4080307441c0c6451408110b2580c00700c000302c900280190000c0f03e0b0484000c11 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 156910782 1250 156909532 156909539
    0x409050c070309080a0512030a020705031603020d02120f0705190507050312090d0605071103120405160803040e061306060206060108010e0112030804060b0d0c140301021e071b 77
    0x5401d81c0408001d500107800038101184440d40010001a040e80c0300000b0000303021020551203854001401a4201c00e07001c0040c2c401054003000a090042401c032402044032806190207450948004250001c0d07411401310640201d52110641d07102504400e8410380c3c4100c0d07460a24103000d26840c2c003000f41c02d00b084032241031240024003682075034826001c84003004841c285002e030b240550001c05074414819440100010355a4001c036402c142241072050218101440301e50131074005c0c099410254103000304020a12908200400350f6003001c1006c030f0419170920301d005403244540d0280d900800f0021020400d6500d4030403200c2d206c806820800c004150b11883e000303450302c4c0156106800201600300204100140c4083c00b81202c03400e00c81c20b070320000e50f40d038243c0d5041001441612050b0b5551400b80207515201d010794461486203e800344904d040142031121040080c0309203020b40e00c11f100d400c114040b00c1d4514035010400d17000706900c5e0001ea250095040700f150100101c600ca2642000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 156912032 1250 156910782 156910801
    0xe040f090812010e10060c05010b1302072904021e06040e0403020d020706120c02100213050a0b030f040b0603100609060f2304110403050102032503150e070203040905 73
    0x500035803600c02010741c00e603613803440c070340c1d00035281590300c0c00281e4141c2c801040307607034050512010140d108200100e1000c05080000d10103000605a40200b40d4000640380700b003080c1c00c0c808103521031203003803061103a001c01c00c00007188e20760051001380102003468054501010341c50f900300c12582c2c020b00e1385a4071034503501260a91513041d2421000362180c1030040e80d485001040c44070a84649a9811020051816121000c0c00648901c1400c0d405110000c2c403011009000401004c091380c83d080180b10324050074001c07081d4160f401a101d40c2024401d0141c480000c2c021030b41c2264110101c100d458854100003410f11403a5a00100e1851900c0070000c2e40ca010b5410950456034803405e0300c110036907a007544007003074690b41201a10410702d900512401d850729622054a884031a0a0f0f903040580301d0741d86508a030b000740d412000742d08000d240c44900c54a03600c1d8058139045185424000600000d4000040140300c0c01b078a840d0890340400100110b2003001035038001d200c1960140040d06010150 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 156913282 1250 156912032 156912037
    0x1020c010b0405130f060c050d0e07060912030804171b06010801240b180a06020f01051023011101021219140f040f0f051b0f030d0e040f0908 62
    0x1c0c54040c900b0800001c4810b00002c0d550060540c000980f140050b85950380d040c01800048001414083d061251510004582c030409405d802c01c10001e1401a04011300070f4001c2c02c00b0351040c90407118804034480020b5110040680240d44008000d0b4050400e861070800c0b4081d0b031402e441c401c01114001080f160380054414101c4240000802024440c0e124204c4e19501c031072108428007140c144208404071a04004080c00e40c406d080d1905001001000141c5120041d40403200503804007040070036451080c0b08080d04220400f0441020618101c40c00303145c0c0d600640c80850040d0301c1c01d54420f032030b40030300c00342881d121800c402190f540c40466041034610b00705844580c404040700004210000440c0b0480c0d242c01c050003034009096451101d080722640c2c0080c42201c20303000c4041540001001071500c50360991090000c0e05c0e804401941c01d41002ca610360100f0310801100313100c1080c60f10041006178060400307141000403076441c600801c000e000c0c0c0c1d40da0500702c0303460310001c1c4003441810b202 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 156914532 1250 156913282 156913301
    0xb030c0a0f0e10050d1b1d030118030c030f0e0a0905040312021b060a0527070503030d05011401021f0b0f18010614030105011725030203060102010605060c0c061b01020c01 75
    0x14100f040c4e5000a0244e000318202c443c3c0f01c00883d4508444e6481140b26416003111520002c0001c5002082d441c0d803042c00ac1d000000841c0072401c0303c0d107510105904a650010700c2ca0b038502e0329800000300c1000160504006109002007035648002003824180302e140500c81ca230401d85030a643c0c0d2141d00c038018555040d281d820110138061200840c1961840340620b6020f8800c0a0309809410050626118150709448980100e8841c44000180a8900f072014006101c0310b00c1c03000603d98034024103001100d0b03100412038115001030340001c60740b001241781590040b01c40740c3c00241450f900380c041400c4403e502071807a03001c41554910095001c4058805042c0d070480d6540020302e51140036201520f000030300801c1c0c041a071028418100010200c001548883c06040b0068100c12161590b08011401810440040d4000003040b0032035809004282c01003400742d4429107403004592449848003107500c5482c0c402d11000818080c010a0181511a1450018021582c4049035440d09000300a01d80 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 156915782 1250 156914532 156914557
    0x2060409020a170c1c020711040c021e0c01031803020d120902040e0c0a060801080c0d15020705010506030d1107090513050616080606121803040f08160b030c0a0f0e1005 74
    0x72010042507171030700130b0340c004a40c40000500e00001c00010000588180e0b0b10200c218450815264a11000380803241275040c0010040c004044010000400b50b540312858070030302c00c410100d40000030354005219020f980d854503101d040040c0001e4688083d0416500c065400b5003030400e0000740f4100480ca81c482c144080720040d1065589800035101d00e031091107403c80c82d811015610800d8240245010317042813082c1061103020780c4a6608800301d81040c54140d84582d5254100506400d040028110b00c0004d8100540d00006201c035280d590301090159a000d10303283c0e004600844005940700712519402400e071135080ca81100b008190f0001400c4440008900f1400308036141004001ca0390505c600e5840311045d50359014914401d4101c0000d1005944002c002c0000c0c1043c40246560103012001c000d40340c11001c12078102403107030180d040200089010824007002c0035581088408460302c80c14080102d929103c400c1d20b1100a18106c19006140c05d130502581035448802030035003c40302c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 156917032 1250 156915782 156915817
    0x302070f0e090d080601050d020f0304051011090409050a170d0f11030a021810050a12060609060c17030c0417010903020304090b04022106090a050402060409020a170c 73
    0x49185070390901040d10062001d4110740b05580110b4450000c0c1c80d8000418140280b07451aa00b1009040342c0c004208040c0c0da00c00442031200f0400c00b803225221200002070248002030038001808007034420b03407503106e2003030b607541000808001c030070300c46504030726000054044152002801e044040d8407419607070900360b00e0103100100000716881840701955400d04c50038110303034a400c10f10b402907210078400c0f1285040220003416a41e907806480000042a0380d900d0f444000070380300509200320410901c0d000500303100c0288902540031910204940030784c5040e618500590400301c503400c0009050002c8c030200001040a050903850090044481035060500ca44084005013400c07a849420000c00603001040108a9019160096040300500520051418a503a01a41c1400f440b07100c04922108401080040d20f01d00000d400350304c6a45c00b141881589010b0340000c1d42803103940520004640d0108a07512007920400c554500c405040711019450b081c00c0c81c0701c550b00e410490354248401000c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 156918282 1250 156917032 156917039
    0x6030b01060c2120070807060801032d0f23030c06060402030c0f070c030201170903070803040c1e0f1e0b0a030e060103030921050a0213060b070302070f 67
    0x400c01c01c09881d800c0112800e05610550000c000d080e410700c001d1013002042d1803840c14500e02034011003040e040e1403000705402490714070814100000ca81c898410f1103082001080030811032044140c4808985001640c0d0036500b0024100c00841c00c0d002803d580c24001aa00420001a641d0414001c0d048242a9240a09040c0d0342d5a407181c00030300011500950081107403418141c02441d04825050000c609014014002420541059600f601e290404140400a550f001042c2d80c500301c8004550030800d2401503140c55580c8140040148401d00010001e01800381010301200549000e0fa6504a400035441415058030494000e0100f0030120300350000c0c212201b50115503400d0042103400c0d00e4507150031386c11a40b9802c9043c030403080c1612a07006400c0400c0c103024090227940b217038886504803410180c4000d0900f420306510902c07828205011008241c00150040c1387c658111350100040c000382107000003418450f884013038074250103d80c2101305900441d0702030a44006055665141d80e0303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 156919532 1250 156918282 156918287
    0x106030312110d0c0905040e0102030604060b190c020105130e0a0c021b09060a0e180d0c020603060d0c050301050a1d0606010503071101020405190602240a0e01110304050106030b0106 80
    0x5078000a03804580410403403810400d2038000c010b0f01c244c607080000b6040d98410210b420394101000305402c0f65800000c104592800380304a01c05012110012800d25868100c1240390f04803140d081402d019001221504580c032503800c480d0392203140100e1590381a074909800d0040c94042e6603c1d00801c0c10035032504c40b050300c00600d19a01c3c540c000d54600480c1011024400d1021000c1c08044d088140c808005c2219030100070b4160003004010000d8500c01841d502950400951100c03940400c081d0300f4410b005a640c035420307203402c444220b4040740d00700454a00308104608680c050782d0954203080030060004140d40c05a25510b0b88807085184c3c01041c1e607507081d190700049030814007049051011030101442080101004119900010b00d440d8031200040c2e80c4104840b80300c81c66652000050240560502521051030075505c03100d284d64205150615031250000c14031694559a00488a007400003500004440280e805000b42d481c246401c3c500e0180c441030109640005050000080561 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 156920782 1250 156919532 156919541
    0x305011401150c1e150507080708130308150612100f080303010b0d02090a030c1401140a0c1707020405010902071101140d0203100315050703060b0903070306050a0207140106030312 79
    0x3980490759003042601e2403a13041c0a0504500203542c0518003802d40c51008415108071030281c501d0348c943d01501d00e010b040003401900018003005180c1c000c080081300098021300b40c1600320043c3c40e45052112001404100c450044c02d8032204003c4480041c0300c2007040000103541962914020700c0405904ca000c600d540340300a100b40c02103440704110388107000383e0781e0703014060114000b88040c21107036481d158807a0250694002d00d02440d032100c10424691b0300440804040b080444106042112248001d400c1c00401000a000740100b1000340c186041d41004480700d083d401802003249586401e174040082d003004400b1181c1c0030145250b41400d60107561134501c08001c9801540ca0301c8180d109520203504040c02c142918882c0300c81c0440001c3e0220300d183c240b60b505000c00034141c03500000040075140240d004002da484200107a0440d520085100d405581e0002e401013100d840702160b01c0f009204a05010740051441d030030520800c113064100c070b0704407802641d840c8c0b801c188094440c401c84 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 156922032 1250 156920782 156920807
    0x807050901020a02040b0d14060a0f05040b18030c16090f06050306070e0609040908030f011a0f0708120903040807050303090616020d05061611030a0206041407030501140115 76
    0x103a0000c9040c0340140307402d4014955130840030340304804070b50082d5140181d40231850410459600100108280a80244144500840307a080c2c1480581810703200c07040c4e1300b000501116480e031980b21843c0303846502042100c060131458000c80300341607543c020b000c0c0301c14072500503101e6060829140585204143c046c420580b10010098002c4e03444403241510103002d000501d6800c0002400351000715955172149200e5140941c120540d00d1038446103114034010160030400416140200258181d80d0040032344a41b03500346c1034903c1d03580c041c5048c000740d54091608211500b04d40c0300c0810512540100c080d100321048002212100790b02c4004040d282d000b070340e649035005081446049560003030095495003d07030001d0000d9407400042d1319094142070003100c0c51050716078200c0b41e0000c41544a40d01c402484542c001943c2004081d0fa0000c0d00c6403009072000d8000c190300d6400c424542400d01421004590040003049114541034800e0800c03a0248141451584004c8050041e68000d20041048 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 156923282 1250 156922032 156922037
    0x6090313050603070201060e040804030218010f090209010903060e0c090a0203060904150207050a030302041505040b0901050a110f010510090b13022d03040606120c21050a11010807050901 82
    0x103034109018070215400c001c041314215901c0c3c031400200c030072000232850700407402075042d640c0d00d50960040c0001c0442501880d014000d0200040100705a80c030b4030310b02650243c030005139580c891200102d0300061a50170140200d0310b001d466403180700d00019603c0c41301405070b520601d01c0c0e82e0034140104a000480b145904100307d5000130b800229017040e2400d15080201c0c006013440c44603100c45242503554401180800d071300003424040a084a841454400494903003a0b1406040140d040e03418040c0081d20742c1805804107141160728024140704c0610840c0100b22140740300c4403901c040c0a0b0a0a03101c0461050400c440814080700601444e44a580081d051510b0040004818402503119207460758203408184a5001701155180c1c0107001501d1004c0c51646038101403c0c40d904448040e4002d0000340c2d80790042100286203085c11000f1216100038020303043c1d4800d00442c007916090440181a40281b02d1048200304007006172003d42042a0394031505940d0314903003a0303038500c90105250b01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 156924532 1250 156923282 156923317
    0x203011112070c0303060801050f06030c04020412020909031603052104030c03110c0406270c1b05120f030708070203040b0d0e100c0c05060f13060b0d23060903 70
    0xd42a02a1041800c2d01c0c4c80ba14001850666400d296802c40c4c0017a0798a22501c0b2185080c030400707103020030580c00240021182146018034090341c40010700140c140083c000c41c0c0001c0000d04822050080c1c13a1080c0600e100480044440d11700245a54003000d19040305006000b81e80740a020b03000343c4c00e4030072685074079540310240d080d4405550001c07210244074058418120b40102c0c0340c4072801401c0003810851421000704c1080360405001d40790b0450b4000c025494404003080351544580400c588031004121400300101034208035003850040ae001c0c880d400f0000804141000c1c3c4c090003144945102e9a6804041d19100c6003241c0ba4819403180800b000000d0040f400102160f60020b10025a104103c0703d604c00c0840882040e5400004000701143c1000848000d100d414130240381c2c0103402c0c01160a50b440c1c94100910114442203000c0d0a45641b000c0545454550044c10031806401582c0002c00000107207520b81e801244118200442c0545c001084022800209a620080300b181c58181d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 156925782 1250 156924532 156924541
    0x1030b0105281206050a0c0212180306010e011d04050c060c1c03060810020a0914010e120d1d030a030e0604171b10090e070306031505040203011112 65
    0x100e0000000c1e890701c1c0d5280b064030403164001414224002415483d01e4600c2560950900d81c0c00c4680003401102c0c200d0130312008114181e0b01042145440401801c0d1f19140e055004d081c220181c0807101840d01441420000b151044003030110303604a411b00ca14080e00c042c802850310381480b070155401070455000c180c2003201c1e0725040014001e01140704045541640300d214400d00c0e249000e0b50a000403e0380c3e030b101030102080c01d1094106a40a0301019490310b400701600601074200f40c840c800c00c01d1428500000b207070303120354683d2805c000300070031100541410142081d00d42d04420152004100d47e41e084050034035130320740702805481005001e41981001c0c0d890035540100c5903a000b9600580030400815026411202c2c030001c0c0307490348010011a0880080d00190030f800100c05032142c2c927a9170260714415070103007595041c1c500064800350070382c840c000154003601990304010240a602a003410502002742d200e184114002c074020b100070f6400015040007440f529960b0000e44c201c110024 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 156927032 1250 156925782 156925789
    0x150c0d140706090b070305090a05070519080307031715060304060c0201091502041e05090a0c030b0409050f01050708010807143006100f0e0411060703080a1401030b0105 74
    0x44030291051050149031962541d2a901210362015040381d0b2030200b0307800c1c041003a5161081941c000c000d2001801f50020544030715540d90384610a40c0e10405a0701901c110030324644100f00f0003408203900b10b944401051601030441e80740c1c0403605014554102c000703110034013088820380400358083d001c03a25503291500d03900702405190202101350b40d29140300c140040c05403182c106000f21400070068440e8105084001603e0354543c1d11505202c191034144000d5840c04100c58000603032100002d1078242141e001e5029200c0341d4485a03009283c2414181882404514400c48a81084c000c008a642d2008265000c8800b03000d02c030610b502220050000381c045019160f101c0c24001d140300202ca9045000c00c039480742c04501d52201018182441101364000c002d81ba4010241e80c0d0942403841c20b00c51800a840e540f4403030728603c0034410010901340702810b2031140a502c0c3c058600e554628040c14091b000101c191400421a07181150f0142e1408806008a05a0ba070084120442d81d1814041 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 156928282 1250 156927032 156927047
    0x30b1e090903030c0d021b070303120e011b03090201031407031d0d050405010c030203090a0f03051902030613020613060201320609270d02010c0302070507060c030527150c0d 76
    0xb41340c2491040c1c4040140c04104001840c000d6102c0d9582c0f0314bc4540c4000c100c02a00c2c0d104221201c540c2c1801584411071900e000d280c10300b03070943c4ca80013820144a00049002d0901c20010800c026400000d0040d00780d416007001408040034045a24603039860414541c2d9000000c1c455400150140f20078010780d8421403030b03045003d000e441220b04000300b5000003400b400c2154025500c0d642c800e0b4040042090500c071400840b115003c000e60300200d00d8010030b81f1000c2c01042c1c80c10380b000410070b4100315542c801c19212244c8100852042654644001074001c111004e010706480d564010200303601c0410743c018166201d100890144c9e00d81302e02041c88a070102c043c10040d01101d5020003922114182e090300014601c0c0703c2c0040000d01d2580c06c1c080d003190148101c0300200340c0100480000f240001445004a4066280c4104000d5941c201250940103142c44108151034144411658403450994100c544500715a6882e01c80d090b604c1c1c1011600ca00311340b50149800041c51000594000c1c100b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 156929532 1250 156928282 156928297
    0x304062309070603060b0901200f0a08030402090f0412050f070618020a0b0c07180e070f030c060306081f020405270105030102030c0d0c030b1e090903030c0d02 70
    0x3218000880c510100d64000642103a40740c10962003220208203095140c098003009118880d1094602080040000d00d1001c1421042602942141d400744286034100840c02815040509a44507241146044c04003136006860030f074440c00c044404540561039124101d405958805546003190440301020345440d0403600c00c080050006108140c0440d006000300c40d545d640581e03421194541c00c1c4100981144135401007122500b05006032261103034001490000d41d444000141c640c070341101c0d00da070050040441180540c1c0140e1200140101c50300c90803405481c8100d03130417400240c84207000c504680f401e103c0ca651562003900500b2207074610f03201100001c44440c1c2d002d8602070700e0394040341ca03042540c1101810941c2040c4d0b03a0039074142e825080c90140ac0304500a51450428020780c4034607026404a010806a032500300300c142034025403003031b0b442e05c0340540340b00440c003528001004101c84805030075025010b4a030014107410000300460307104002d0103035480c0c00c101d02c40c0781c074000a420914 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 156930782 1250 156929532 156929561
    0x20408060f071704050109030206100b1c09020406120c0b0f03041112030a05221401080709030b01030c081504020a15020304080304090b0a0906030506070809161e080c06030406 77
    0x410f85a1041d0303000d84441c41140208000b01d0300308501e01e4003d152080052030f8400c4404401002d00071640004100c03020350b4a010b07550301841d00c0e0360109000500c005131000b94013030f00e8548000750304c0004c41a40c030700150103034604000007550f035414015544581c41210385000c1c0d0810004000a8080c4020148100040c1030b10b10411300c2420001d1459000a1565003c603e0220308a030b4841c14201820305024801340c000c080c090b1421078040c840040d1000044c0c1448882400501d10a106090400c001d5410544200865035039080020010300c071401040d0242c01f50012007103100d50032155060041e41d024200148861a201c1401d0070701c3c0c81e0704000002c50004100004000e08200042d0001d0700e10b14500040409041c8208140900e050b808040710a050241c200045440859050784c40340f80c0781081e03d100e0780c03024680d40c148110341241072544072240d1000300310b1301c40d0030310401c0881702c001c841800990749070700c0c200d542c8000351a01254810390400004000074180c0d001282c1440e03507030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 156932032 1250 156930782 156930797
    0x61c0503070f0c09060617270a0b060a090b030d0305090109020603150f09090c01030b0a0b0d092d080a0c020a06020a1b12060c050409021318020408060f07 68
    0x7079403040590164120309a07103d645404050001c03204d01d11801000b04000c3c10500201c2800031070240781100c00070075081402d1f140c481e034140041c2c038041c0051104010328081c0c1d120000c0a141603111450705580b4540200286100800c0c90417441c0702d04075503a980180208480c20300b8120480140000400d04003665480c2d01c14500103803600805140640305c15035031004681109028800e1000140521780c2c4280c45000500046031408210300c01e07203003004c2c40c002c00c00a9018000c5094040107900c032038400d00b0006070018401d2010340c0210080d6108201210200c642640780015401d207106e049000d90742034025140c0000c450800804120840c0d041a0b10b60710b0703641c1c000030250981c1d60303c07a90158001c41c1d03e5004005c1002601d882884402c0c07888510785041c1615405403000034080100665500c0d644181c00600a4055074010003100c0010344d0f480800d002101070030306991042e03664180c0c09820580c202407650081d10b081e075650070018003240c1d80394050103445480142580e81449020b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 156933282 1250 156932032 156932047
    0xd0203010b0a09020d0507170406050403170a0506010f0905010906050714070e09010e0703113102070312020405090c0d0209040518060601030b061b0f0a0c060206070206061c0503 78
    0x5203082c5500a04110b9401a110210811a1010b45d04001c04802c200911000d400e07044004101065411680140c000145030b541c5180a40b04000010345042040e1192400c104140229400c524070550302070343c0b164a80c9161030020394081695001d40e0b400f0881c100c40911455120300040c0071294010354110358242000c4010904041c03907030b000041156006010041c60007424010980d04810490003803c1ca6840c6441d0544101d0381801c025104d0002e441101c900f12250742c50300202a030b02c881b20007440c5100301d010340000754404481100030501064072804148550b01c20760f400c952000d0006d0341682d4412904c2103060b40000304e522092a401d1100b10841c2c3c6551140d64441e24061141070401c52640c5552403a141000b08420704040c2000d02d1a42191148001c5c0c030041c0c107490600c031401301501b20900d0b00b8920300100c03000c1c40744612100c40060268504007a0201c0c1e810360250f44c0c0c0740c2c4580000320f884200449803160410b151201e5246980e071074110f02c84542d030044003940d02b00000d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 156934532 1250 156933282 156933289
    0x603020406030c08070b190c030c0506091c0504080309010c08191d1905210f07050109240c0206070f0606031b2d080d05041802090f0d0203010b 63
    0x5450b00152030700d480383c0009011020b801c000320000f90400e0008203082030a0b60800c41d40140488002e1410420510708140c1014001c50702d5404080c0d00c4002d40343d8529240c00380c81c2e51000c2c25124522500d00c032032a00700c8064003480403501544ea00001441c581450710006546003c2c000d001210b42e40c80820050303aa840e03400000840a641076600c1d5001940c507001c0c200f0704001c401034814445c0c02121400c542c00c0c01391900c6c42e02281c01c151a0003800505100380703a04404250303a191120b9001c0c100c0b801c040c408001c01c41e50b050703c000b40c0340d00308004e44607201c0d501046a105801000c0d108640b40480d0510b00505240801307510081c91540350401d030f035135190b50700c429141c02200c10903142d4406004100782c0301c800b80380303203620f1005212085107407000505480b040101c04085034800315401e4803900b5860401803018101100450350518845000200320382e020344500342e07552400c4940c100c050f11003070007160451032004103100d1f010a28a4100000410003000c00c036070540d40d03100140284e46 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 156935782 1250 156934532 156934541
    0x9030c0807060e0709020f0703030b0f100201020706051509040308061504090b1f0c080c0102040e0c03040b070905010c020105030a0e0601060c020910030b010e040303020913050a0e16090f06030204 86
    0x1d02c98400400d40900c0b0380c01d03c074540708054021650301c500500c0201c3e1050488016960420b816103404101d0b0485171001c14064451a031006402c00055214110301c2c035015001070070445d2040c9010045030351404000d00c0c8442c0c01c3c000b0a0b61000300e000100d008280f2415000c3d400107801001080150701d100c01e4030325a0790003980100000c9843d030300c000666103804103551240080b024104890a612100001c0582009103c010041c903404a001c402e00442541690090100c0510920700f60403c000d1086440c3c104980c1126040e035044001130f0407510500ca0b140465074186c43c1c00d16075400c1e542c01510240c00080c0001411a0360b1285030400c1041000340c00d00034202d0361207480c034004450040c4900d03c2c400902c1000170240320746040001985185030141152850308a92003e500c8900d400c4011348034941c10a5031040300c03400b60100c04510703544401d014441c561030400c4005150960320303440740119000d980d00d0007030394141008202d056030042c0f20f04031008040084c5860f125030010303007200d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 156937032 1250 156935782 156935797
    0x7080904060f08210417010b03010e030304150603050c09130b010b09010906020c060316090803040f050901080a0b07111608012403080403030e040b0402031614090109030609030c08 79
    0x15140c502c0422200c41c1c01e014400d182006420b0302e08078a590150b0000d514481ca2186800d114414162060481c0c000c0d442402200e00080090208000f4004050b41c0c80d081600c0030f954600da00001300e4100c845500c51207044a40c40b4002d480300c081c0500400480c000000c028982d03c40c50800754078000344910310040c2c042e11090702800c1e200c7c00e60400041c90f0140d1900032009540c81101008420764507038042c1c0c0c1d44000f811200303806d07491f00d440341200e44000580c0584903030301c8042404100045801140d0050794000c0c0c42c8403903141c3e650300c0c01c0c5903125000100a0562080d800c04180d1a510034030782e81c20103120301c40c12503015450003401c505172403600381e000141595445504a003000c549403040002e005651201d40d0500c1e08580328402184102d11009050040b122074085054407207420040c1000d400500854a92610360383e00a00060a1305400d800280f4120180e50140c3d45a000c0c3c920480c4103035154241181159500c00003810b41100607410710042440741d20000c0c16070001407100 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 156938282 1250 156937032 156937049
    0x905030c070602100b010c121e090501170c03060d1b091d06091005090114070c020405090d1d0d060e030406020601080a240f020406020307110d050c060708090406 71
    0x1210b103030010007410001d1503051401c0850a0081300f9006070303400006050026000854118284420401502d081841024901c40c074120301800506080d0001410001c03501d007a201e91480c41144c80050b100307590201c0301e03000301100c10b0003c0f540300c0c28500c2c1b082c40c00a12904081f00500791a800d0002c10401c1b0350311080600740c0b40c030f40c0784201c4190000c445481c0c200c40e00c010075940c2000c0d00740c1500c401030342c410302e80304139624000203181003025000082c4940303090307a50814500307040304000c00c400d400110a0303014608180101311120000500c51400f4120303a518040002c0c181c0f50004da00ba40525900c80c7c1c0f081012803c900840d20358400e010322139006c00e00840d5110724040010703007001c034164070800c3c080c1c101c1c240302c03c08500442d10783d03950b11880c0003607242d584813144c6050000780144000c008103507101107000302d03510390000024455203010f1030f8003445241c0c0c850308024511103e001c0041440c1c01c01c1043c0c19440c1407203c040d1100c18400c10b07a0b141040c0c0030b0f0001c241110740d26807080b0340 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 156939532 1250 156938282 156938293
    0x3170103081c0f15140306040503030708100909080901020d180b070302031207031d010513060507111e011a0d02040203191401090c020d0207030311030c100501050f061c090201030905030c 82
    0x46203280030705d40c0e1244d0744140c5c0540b282d4901526400e40742e00009002e00148695100040e48035501210b104c4043c0044207020030000c9001d082c266080e0f00890303500d0f40035114441d2000c2d8100d000c1c400d0328403c840345038076001070039051075060780180d00109030840a510051150308052024860358920442c440d03540000c11400d4401c000030705030b07591030b00312440703900d007000340104541c40d4144100815002003002c00c09445450f412a0204140c0c0d0b0a0322041c010301002c902c07029a1140500f0140440100a000f0b5050505c10305400140c498101c90b0b00ca914104d1000050500340c01030341d40120b4008851074004084200c04041d0b0b881c40070100c11142442005021001e114400e40c40803e946100410b0080140070029565405d50b000140a02032800310321810701c1020003c4030b042886820a0351401c4101d81a004094030f02030040030300c2207070040c0c401000c1c0e0904000352000400d01c079494020034100410390b00000c005200050b410180c84600c0600132a0301040102000e111800081a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 156940782 1250 156939532 156939539
    0x70b0903010b060c060105060322150609060509040f0507050d050c150f0919090915060b07020307150309290606160228030f03170103081c0f15 63
    0x500b11030340c41407040d01c12003050000550441c0c0c0041d41506407001039428541d40d481b0440741c03021803060980c00c019400d03d4035512504000042c4802d0030440903095040c8012900d4049502c1502d6440c010107801101d003900080c0070801542c17442181c14001c4e81900c40743c3c0c4d141c40100700e40c08903a036803d1341d2581c0200c0d03414819040000c0c400c195a41e200c007a190030400441860380381449048001e9206840c7c02a12958011129600c0c0c0001c0c22401401c0225800620b0070340c010307030b2902010304100ed00e850b00014195200b407088680081e4002c010707000c00c6082084076070b000000c10080400301965070391007030001298461450b00b074940c1c1e0765410402040b0798404807201030780201828040e030020b01c001c6c081141c40305510401070b94101e030760069459000b2058040c85c2550343c0c03100c11440b00d00c00c00000707001e02000900c121034044d949020000c7c0002103401002d100030310004001202c10040c0340416564040340e40c40c1d0703042482000c00c61420300210002501c1104440b00428002c006042 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 156942032 1250 156940782 156940789
    0x1c031701080304121202010e1b0a080a0b180f03041211010c030516050a1a19020304050601060c150e0d120b060403020126010f050907020105280905070b09 68
    0x2900600411005519181c20407078030200040701108000e010b20701c50386913101145d000790032002900025a08540c2a0010001d5003580f912442d80c0a6004801c28680460550404901048966082119039119440b00c4d0482d404130000c2001500450140700e41100070794005200800c02845200c40b400002105410302400b018410710301941800800c945000000e41c00a055616810086540b1207441c68142051404c111a0f290700501258852400000304202140b440f80507001c50070b03140107001d10032242c8004902c01514040d16030740c80a00100f01442c0308043c0038078002d224922228a5000354408002582c5201c0f10030315054001602c000d800b903900490300c10340c81f40c0d01c075002e01040c2c5900020584512650101904000c6003001300306109052002c0d000d91444660016402c3d9a540c0300c003001c02c08010301481d0b04c15000100401c0c251881400b5113401082c1800c80d0114448034000e00014001c81410342c0c881c21511561504007189007400f4180040038080c0f2456552040c26040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 156943282 1250 156942032 156942077
    0x209040507030c03050606090a05070e1504092405030a0f060c05040801050415050907030b0f0a110c0102070b0c0c0318040b060a0905031c050d0c020705040f0207030305010e010510030b1c03 83
    0x20781003279904d44000c00031041e5100c0c54038809007005840808040f84109500b400382d100315000400c4407410306964010703040703181c40010071100703a00154000035a2984205a00c800003c40041c0003100b4060414008c00c1c0321354802c1e001414941481880c1c241da404600e825260125001d84080010449400c01003101c1e02034141d00074000c502400c240d41c11350b0307200b041c800006000c3c0e000711080a8000341e01a039042d8810b10040c04182c0303059480d00e01c080c0d140381c042c0d40803c000b00c4030100281c0100c0c00110184d800d4074002c6000b440070f141880d0812000c00745000074000c40311340c0700c0e03250005480d003911400000d003901580356a401d10203070b0502c418540b03486c25040744074041044511a44480d5a8032106460007944580b17000709000c5030a42040380343c003000c0c0e049198018913000820006100a1303000b8000703244203440a01c456a40d519980c052950248181c640040c241e040803480184250700c1f81c281c0f54001016440c0c0400a4184420f809105900031004216441c1000c0101c5500e40031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 156944532 1250 156943282 156943291
    0xf090f02030f0d14090d0f05030309071401050a05030411060c030904050123011b080a030209040f0b03060a020706020c060906040201020f0307111314090c0109120f0209040507030c0305060609 84
    0xa00e50f6150764000207000900760512400e101c9004070b0080c9003982c410303004141c400d070810040c4400741140c0c04c1407901c0358000c1c0c4808003a41725400300011403118400104140400c1615043d060440090058580ea40700904c21228550030007124812035841e80c0250140d404038800545d1611a00410700044600c181c03c41e070801e2841c41d044c0491501d200983c10a4441c007840c00c100d2003071075000c1d800010035a840340100040404180d60b8030702a070542c0a06440f102c11507040c460500000075079011548000b22003a05030f0072203400a40c0104150300100034443c03046ca40140f40030300c541c1085003000c0085d2560b90300d580240040c0000d56034104034422841032281c0c0914980140c0780e5403440007105811455001c0c02160f0b078041400c030744640c80a03c2642c0c0b0500420254545480707042c3e12010021a45030200e0b06040d004505460540001e00c1ca56601907943c1500c0e610030340800407000c07001002103489110304180800003424a0594100540c03003080201281d0504004110301f500d070051 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 156945782 1250 156944532 156944563
    0x2030d060b1801020c0f1203041a07061116080c0c0a03050c01091a030105040911130605120a0b01210f0b0103021807020a02090603100e0610090c050307050a02010f090f0203 76
    0x807601115907841c078551b4030691200715001c8040000700840d203420340c040d030340c003840880c01114221080190300f0002001083d1003900200b0001c180ea00c685c900b40d0040494414425500340c0881000651903402040d844900320101c4030b01c0d140c4400000c0d592031868008641903000760900007440d58000040c000a4046440310510002d07541c0d502515074041442500c0c811900e401d03d20081c00366082903c1801140509004121021000c10314007400b140c0c850240190040c02806490701d5012409802459000044541c10303480c10000d4007242902000c14070740c40340004d0004c400141d1007040c10703660134420480070082e50702d18010000200c61004025221000503010411102d90106440d0450f540c101d03190f0740380d5110030012904e4110181c0340d254000d40b6140c1d134840349000020b1010302c655441c1c0c5400102c2921044a80c050b5010b98a10350003040c0d0520119190034042c1c4041e24014407640300001d400d40d05401580151000f480c015101447d504c8043c5041d0308003401150b01c998410b0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 156947032 1250 156945782 156945793
    0x30c0a15020307021b010909050a09030f020d0203071b09060608150a030305041806030b070504081b03060610141b1501080613020402040e0906180a050a02060a02030d060b180102 78
    0x40002c5c2d2078140c00340c24482c0d084140301081c0c41980c05041070300301030410706104028070729014065900400c08040d00380c0108008180c0114090b1000810317000c81c0c1d485a0146040036982d681d52a02a80c2011440b030f13000e4005800400c6030b05291145000800c0581d8451186017012000015100045065a07005040784041803001c0f0390842c044404440c22044610060b102c4501c0d4a402004560802001d0b018100180f054083c2e010f0081c2003903900040c240c83c608600c0f0300d000307550a500c100402e60150451000588245050210f210020310b00f428071a9885220b55100700d01a48071105045403040320401c10078101d113080042c07040e8001003691141065041803000b40d0385480060000381500302c216210411900e56806031401000c100c545540c9a007031100005881d0310701141c601010441d500d65100440b031002940e1450a608074000e0501100d0b65000e1060b541d10150700a400d600c07040010081d011780c54400c2a00500d4091501915a82030408018007201d49007480d46c11580b02 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 156948282 1250 156947032 156947041
    0x40e090a02060708030a0219020304050118050f09040201121503150903120e070b1207140310030210090e090c100207060816140310080d080115080a0e030c0a150203 72
    0x242c2d0101c80400d900603400e16182c2d40c074600e000f806841460081d10040e0307001005031203043e800201038401c0d520240c9548820380c07581202c05a1078103240c49040d80c40000000f481c42c05040c9144190b40090040c07621003280d211038100641600d1400d20b00a40c5070000200c1001031010601600081845a41060001c00c440303440c02041925241d04100c1059680d081400360940c0411280300180030b03804a00da115020784e070704103554040464441d004280c0e003140000d181818101140d10a0031040d5004004a04640a008024100075030380014481004404140003000310b40c124860a801ea00070910424643c05000c0d5207030005854806560000b40203200681d00a010030f648451924032000507003040940441d0112030008012881000c004103024500c02d1100101040d1405442200c600c1030000c14111103051003446003800303640310742115803021031081e21025080b00d03040b00041002050000894110b90214030b20446c140e2100e100b0904121211807402c03501001e11000f1800c5160 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 156949532 1250 156948282 156948289
    0x7030209191437140603010b040605030712150603151b140d151e0b0403030e09060301110c03090f04061412031926070e06090a0902030c040e090a02 65
    0x41525000e9a07189451100b41100f032422100040420601400307800300f01d4907040031420041c1c411070b020f5420f0002c08841400c080c0601022520050b0040006901e40803420b044084110003c580d10000c20380d0700040043c3c68085c070030145014880d102800c1c102c2c0c04024044428841d10316003c14141400e10706030356000700c44000602036000300107a540c00c4c8080300d00003d100b40720400c03c400040c1640400c1c01810324181d40c0445c003421824481180d107600095244d070140e07102c000c0021b0f800c107a04200c1400c006892a4005070050004226003080b105842c2c030a0f008503080c096194408030350300c120f6250080400f0355440056034100005410841204442c420010195006060840c607410304030404108558214207203001d010a0881e100744001d05149400003007207807050413450004125020020490702032a9940c444c071400030020300921110750000302ea031542c44190304600144407400c0e4001980720301440442180e540d410001e103482d00b144060030300c0304941d100c800840010388 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 156950782 1250 156949532 156949561
    0xf0f080d1d0103020d0905060709080d0804110f120a0b060a17060103020f03071d1e1302010315030b0c0403050d2a02040908130906060f021c02070302091914 69
    0x200038a8013581d5410310014a8000d040e88100003001803092904210602e0b501c850001c06480c0b800003076510009001d44120345844003a074000e410500c8071a01c580721868012a603000442004d0040350100c24030092540c00c0450811083d21400c03203400c00c00916140201c0c25001402c54401d80c401c40f10803103419140e41d1a01408024082c41c42c0e41a11905c07940c0400012000b4205549098205180340b030094070600307815038080c03000c0044280b002c81e240c00c2d41d4100384e1007225010340c0c42e08031030a075400440150070800d240060003040c0007800f10205401184252044140070000741d03507240f4514000707142c00180354601b4100003042c00801407803004484c0300000c081d03100e087c0301c0da030b0403c50001a004116004008001c84000100002081d035080c1c000e1003100c00840e81005480c3d80c40409403840106c407000c2d04016000021a59007903450783c48135400c08201441243c1c40c1c0b58030396000c160000030942e1700c201c055000304490780407002c060140400e000b211030100f080a044c82c008050020 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 156952032 1250 156950782 156950837
    0x10c0e030a0c1a090a06020709050705070f03080c0f0a02030c100e0607030f020d0509160603110904020d02040b030103080d051f0b0901020c090c07020a0503070b1207090f0f080d 78
    0x4100041c03d035485240d40c6802d440c2214001000598500d598a1000c0d544245511555465905010026218600074020b03192596040b403000070450740b50f941c044401000c01460904412418071800e1241c04000016084610441c1c00440d555244410340c070b850192180345070380c68a418429084241c0101086180e042116818041151000100240040d00030542442551880e0030100321503008006038607601816240c1410070010348881084003a035001e140041002c030403c01071005c41e814140d008261200480c40c006040644982c100103003580283c0c4280c445101c045036096818a10388519038014206d80e06000c00c001c1c0034410012040090310440c00b00c1c0300c0104444441d41d00901c0070b0785081500900401d42445c040b402000c4540020009031b002c0c6001100104003400c000a005043e260b80300036a40c00c040046030041001e1800420103001c000794cd000c0082e83e694011000c00280510101022141d0b090030b0980740b0b041803c11a41e0108140840c20110303003c6c0003400ba0004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 156953282 1250 156952032 156952049
    0xc06040803040b0703110a060b01120b0a140f03070303090f0807081f140109020309190218060d0f12110606010c02010f02010915020702010e010203031006080613050702010c0e030a0c 80
    0x40d590b1a00381507410b486d011440c1c4c0d00a00640800008001c9568060b080080091b00d81c001010040d81032031044421041c1d126030004591030050004205034102045040e4000f05080a88216000440c1c1007250342c3d8003c131301140340d556050004010b444e00050107058024004d1141518040d980c07a50307041140703842140d160510101802012044d081019190041d0051001950b50b074903400000354802c4440d0340c0c89015420020f009030085079448120150010100c60f40505a803442400303804016240582c8911200d203120000781500300316040e090300816060604181290020300a0001c0c4001e0020715000241000b44076a000007141d54400d8080c0303446600d000d22007030709034010302e15550003510080d8502081d2100703005540003404c1d458404e9072034001c10240c5400690b524081034078003402a040d40c1409019440c402c203040b603400310300203142c8944c0d03a46401c000f4003202c0043e500340380142d4440030701900c0f6540040c401c1d41080c0d819001020740c1c0c94030340c840010340132560046524 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 156954532 1250 156953282 156953287
    0x41202030a0c1e081209071502032205030a12030b0f060304060507050d090c05040b01030203060a03060e0703151407020c0a06030e0f162133020406020706020c06040803040b 76
    0x204200b880180042103038016403480d40d03580c0040c82c3c0e07030171003000f184c1c51813651203070660220b82d50000890412582c1c801303170025410100d604c43c410008150030145520110041c60b000035031a9010042e540c0c4c0d2500503a402d05400001d150014155140c0040080c003680e07840559000a49034401101e61154000200007442c0d1940b040460700d500c40c40300d064217040d04140b901c8052112000d510004c581c022181005490490001501a4007080300c1096000320b1400f8104041003641c0c10a0380300c903240d4000c1d16500b646981c4e80103885002114060203165559516040d10b210304105150040c81500061010480580000d1507a070010b01603502010344a00c41c4455040c4200032074120001e02c234069a007440313165140541941c299104107600c1e100113062119840151001a030046c0790007110b0860803030909040480a040c83c1244141d0640b201d036800c603440e807482d1001d8001b07084643c0c0509102403070104000e18000700c5a21b00d40c441c4130100420001590000100c40407501c0050700142c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 156955782 1250 156954532 156954563
    0x30d0509010f020715020f0105090c0a05060f040f0f030615031226090d08070c0507030803070e2206053a080309010618020a080114130212041202030a0c 67
    0xe09041017513203c20020b003030b50108181c480343c001c503c0c5100c10381100005c02140e518410001e40ea108a00322041d001060f0031001d01c15410040c00030000701520914107498166142c0c285203003117a05a000200140c01c1d8041401042034900420916060740d4007181c210b130707041da11a40710110192580000340016a601c3c0300b411944034504480c40204038030340c1856841c00c4105c1c02d4446000d56103560000b400c0e5000568220300403001d200d813a503000002003120508559410030681e00c003900b55414010b424a1620499540e4040c01c0180b00d50710207140c220f05090000c0340d094403000e030861449030041c400d02401140074000c411800c401020f02c6074240f592107a05031000062403c1c3c018040c400300104008840105401490441d041c45d05400301081000d40140100d000d089962800955894010442c2c1c4034219096450620000c0100c0d0640d200303080c0300c6041380d02440c5601e1904074284100020f002c0e44403040510040310380007a528026031400010b081c0350103c0d0000704188035424000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 156957032 1250 156955782 156955787
    0x1140406030b09030904050f0f01030305030a0209030604050106030605060103020708090f180a05090d0c08120711070807030c05010503010305060109020d0b060a11060105031b0427080315030d0509010f 88
    0x1200541d0800442c0840b400c1c10780340f564596100762101e5000300d0500b408115a1400800c6640c8904403c14104c469642140d90480d20b81d440030740b400c150f05030280f2101c0c84959052107641c1c01907102e0000065541c0c81e40c50100141c030740007405241410320501901001c42d041c4e4088a11050040b155210311849900c006801001015115500030604000700a90261198081401030241a08030b0300b0300c0b180c2039411922841400d00080805006000d04d0400244c0c5031a201e8019400c0c0c201014031003041221103140c4841035100e10303c984d01184041051103034002d0041d001c1c01c000c1c6001c030b03d50341c15500c1d942d070703902c03010310841c0840743c1c0c00100c040841e04250b00104060340014681641c1c1c100c80c510044c0ba8942040c100d1503140550000080d051030300240074040405500004a440101c2104210080122086000b01d030100390503040d6081444a0400325020312a08401d0b880c0d0a009000b00044000d4071101030081d40324004a00c0c0c0182c0041c00e452000000340b07090210038800c00c004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 156958282 1250 156957032 156957041
    0x90111070b0a0c0b010f140609010c08220b030603030f1c020403080406020f0c09060f010207030807082503080406111e0a1b0209061207080303130c080c0306011404 72
    0x946046007000c502d03010500e601c0004082020300651100840703036210283d54613240e220380300300b48400b9844a80c8160134100300c405404d510005040403d5500e0303a5485910983c0e200340003129040c3d5480700c41e1064800d48406113809400016101c60440c60b00f07401180e664481c1e00d100342c0d8503000c0810740b00d603c500b1400d030540e003910341c2038025500c1c3e6a0b85c1c41e10242d607801900441001d17000b020300001208c84000f5080420a000811211454950106100c404a0280c00040c114040d120001c00401d400b4030043c0881489841c070155289501a030801c2860b103003080c801140300341e492054011a0744a002141c10503080000064240021401600c4902c80c0340590860102c4140507491307040c0c401c03005080c000600c0d440d4070442c244103000034040c81c0e21249000350b0080365480450100d04060501c180810001c074200e41503940ca8422003860b5800031904090302100703101d1174404005580e1040700c010305400e40103081c03004948002a403502014055080010a02e40d11f60250741d4a1b44c21 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 156959532 1250 156958282 156958289
    0xc08010c0302250b0604050c0909040804050405060303120712020714010e010510080a060f0e07080a02031912030915060f090b09060d030e132a02010b010509011107 72
    0x800c404080c1050140180d00b2070440405444a0105955525184000c004810f141d000c5403868240c0e03640c3c410040148005400c200f07038084180f02d055450340380c032840e8a01581c01848620345036840e0100f00016210001c094038069081400a64803082491145503080f06080c101402c060740c001e0510301c003c0c0035401d00904901a810300144011308190310a011001607400248080c0c1d640301d40c0e9090080042c46200815403108010704082211907000c0000c0700c1c004180030812161301104507240c1400d6800025094024130300703810851070200440c2241a00310014407040440c640c85070031a01049540301e009040d100c0152004100d40720718500003a0189440c1041110b84441c844800751001d40203041075180752116103295840c11148680c45000e0040440c000c041030b6540c1103590007140c0410903000381c81e14100c0007100035a40604449884150102200c14130710040701c00080d6110003141c0c00756403614510131903d903400021500150790030300302032140c640c210381003d24103d119070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 156960782 1250 156959532 156959549
    0x3031a060f070308101802030a15031202010f0c080f0405070f1706060d080702010c0f020a170c01030e0d0c02031609090c080c0310092103020c161508040c 68
    0x5080c0d407040560101030000e0602030790f508041555821034400c5038003018003400d01c18a01240d05454448466001160b111540d4840412007440101c49500300c401e158004807441c135004c02040003070301e9092280d604881d004001c2070181d10700d481c1c07016141c01000ba042020b0a03205c60001410706c90108110001010320610702088195500400c220f0341c07400c080c0c200c10501850000c40e02e0703441c0c403444464102e504407480c3c07458110b540e40107680b8000c60900440b0307400c0b40c6ca0003040261303980449a1000700a0750790000400c045200509040026228040d4145480c104d40c1031130035680090f203880f416030301d400c12100101403400020304e0b0103007001301c03070f80700d00c0958401180507010303504250342070351085c543d4000d416140c0c4107440c0c03030700d1480105581540c403603a00b0307010107481c03a00440c140e40d005450503280a44115644407803605110380c500003182d00020002590342080000c1400c070001c0c4108550744600304407030030788088200000b200403c101600803405010200900d00010f09002 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 156962032 1250 156960782 156960787
    0x10909020f0c0f030c19020603011403160e07032d050c0906180a0b0c06070810030204140f0c040303050304080d020c1b042003061315060804061a010c03031a06 70
    0x143e4402c0d590794000c180c411014051b0782480350380d0007069810484801e41c010300142c110ba0800314911042c0c0301d10480c5036498030074035940da100e00c094003000c040500b9011540071800d02e811213000e019503003061a02c0c0350980b2924035140c000b0703001082c80021a19801400b10392034843c0c00a1000900409980740e070f2100c80060000360716500017601c160703580015500551150303940c015586c054000d0320070b640203e820010000c0c03ca14451105c61b64031080c041d0b5800605c0c1d489402050440e00500f0185401d120100240245a0b9a50407100d500540c0c1094181c5403c0c1180d80092403400003034401060b0b83d60104000840c50300c6c0380c06580c0414910703401c4411484014403034071280c2d0710000c1054003c6190076030030711054000c40f20381d80e5440c131051070107407442d1244000d001c098400f40c0c090030000c5540391100b0407291040001800180007542e100d100c142014100a4112412004d030040c2880341000303144841c0e41c00c0000c11001c0350301410009420b02e40e641401040b240c4403d038580c2c0c400c000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 156963282 1250 156962032 156962053
    0x1020c04060e010801061203080f10030807030324060e011d030f0601150e0f091e010b0c0f0a0c030213061a070317010503030d09060f020d061805010302010909020f0c 73
    0x1c00b039a14101c41070600240102507403050250f8002c20351810240009903c84006010103440c00701503034001008032450349030981d030f90b2a62462a00041401c90019448206850440305070807910810b070f40507501e4640d0980e1601c0c101401943c000b8401c1414010314002c80d0103030402e000154000e1120140a03140150550f41c0c41d2070720769400b4003a03807102084a00084554038423844d4840c00951004d0b221444440c200d0b0200f10078884006e00903000541c00f680060040252510054020045424856140e134010074410381403442800762100d040d40f05800c00700100e880301e035020b0704030303501a1680e040700303030445010703001400c90364006c1c07410000c00c40c0403101000340610060810500070303601c00c03946480e94031100100440038811725038903034010b10404071f9407030a5074000813070544581f0f00000c9100701400680141d8000c0010717103c0703560b500d940400c480b841c002081d013201288984204a150b0441d40084c0151034107000710300030654007103400d8081c480d5510448645024010486251303009 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 156964532 1250 156963282 156963299
    0x140a05031005070f140703030e0c1008061503090c0628020703020901080313060f17091606020f030301090c03061220060c031804110f03040c060f0f0c0201020c0406 72
    0x10035240700b800030b4204c400a13240daa20580380380040032294000b00d40781071501d07241240503011626600700c03e80140b8a20480550f00c26400101d0710304551151600c1e4503104040050800716490404200c600803c204280c001012400c24500c07001100d42c1619903990340018a403140701054031003008440466407100c080d8000a111040700d00c00c0303820071141c1ea201c028039902c0b80280c452042402c03504c04002d02081c2d010348183c0b40b0072041440c010400d1540607500c0b14032400181c0d80d4090360b800802c01d408240c3d40401040e13002d080f803400100007028014130429034a210500c14404040c1e0b86005118100e03120f80c1020008202c17904804002c0444e9041181440409440000104001b050101501d0826400b519400b0782c0010196040c4090410421018100c81450607406075581081c58032003034201014080820440c01090703107074a841e01e04400c04500e00e070001c0c0148402c5005112281e580109120040201d03454a06c025032010320050749849090041d16601a0422038003003450407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 156965782 1250 156964532 156964541
    0x7120606080607050c0a0609020f030d0306080d0503220213020d02180f01051c020c0706020604060b1f0309110306070c03030f050c0f0322060c08060109060504140a050310 75
    0x1035407001a5562034032810703000e4585109540b4481415002861204041501544200c402a0000d010400e00460840003e4286080e0104250101c0c0d981d0000b8815804204070456000d001c1e81800e07842d5042c2501440740850010850482c1814002082000c47d201c0088121056001240c02c0d51945420213240000e034200d41d0818001a2200040764594500403110f00340703010042e15410f00d4020361004020142d042940c0c0014019000c0040b5180c00000f004400c1c0204056805020300d0b0810785014402d4030002450203119030308100d0028014040902c950a84002c1c07800c00113112039403032a0034419050941400d9034503005410421280d40d400420761080c0c43c7c401c0d41d0401c040810200398404480007520b036802d0f10394080c80002d508940036001150440b02c4408000000c01e4015500550040349440481e030070760300c44c9125020759030054059900071200f420101201c9090000060081c0101c0c82590722110301c9400150b580d44843e800030000d480040d09643c3c2d584803140d900e0010b030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 156967032 1250 156965782 156965789
    0xf052203030b0d21020706120f090503120402150304020105090909010b0a080303011a04150f0215010f18020901080a0203060a03021203040f0f1401030c031d0f190b0609040507120606 80
    0xc10030301c00b00044e081c030103e0405c058400c0d44e2507200103050300c010103600905040c000007212036070314100000801d0041018000c0d014007030f08100c2c403030b142a00c140300341c0e500c2d28000c4183d000f40600030700c001070f80c010050750300000003a142c803030242e9101c006142c0984140744034150011258180030034110404801141a01d0300c0e0038207510f1605005141c06410301c1a40310300d01b0302c013011050344000b0503c1901404c4a0000d1881160003440051541100207882030b8400c68440c101030320100007030a81840754080d601d821322002c6040c59a060000303000c50200411000e01507038000002100740e0b441404241c051600a0030400c1400d141d090610340c0c0340e100f4017518901024103540041c0300d03110034007802c0a99280c50064170300603982800641c0078102e03018020b000c0c1070310351070400344404c1c2c91040802c00854850040c00040000e0b04441e00385007038072100c501d100003d10028404201182035a6802174816155050180c0d1281491401c00e207c07604880c00c1d00140486240500c01103400c02e8069 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 156968282 1250 156967032 156967073
    0x70f021f0207050d0f080a030207060c03020306010f030e0f0a05150f01050a0e0403140304030e04140c0f0d020c16170a0b04060c090f060504090f052203030b0d 70
    0x352148040e103282026160202000681c802d000501160501e200c003441c00070710075194420990030550307888003103070402070700d02c4002503000c20104203201040c040c15a620209050441c65410040d0000303260019951341c001c20b00d0384039580e0b200700103020065903120704440d1064810359821460500d0700c0d501d00020524045c4000e80c04108401903400d406e50403504010b2401c07900c5881d10000d00d2000d0f00080080d004d100c900555180c800a020000754800c520030340d01d807140203d00208100440302c40c000311800141c0e001080000d80080c0000319030714100160100c94598506514060191007500016034a601500d0540c0014000000780c0c0340c1942d0781000d00f465507985c1d08140c0b650310aa1010007400300040540031401081ea55030000900300c0b1503107003400c552600d400341070880da40310344d20150003e200028104040c0c51a84208014550007840074841c504104a10810f02490300c4041401141180389020426019034070110400b40f004e042810301082900b0140c46041c2d400e10070403075 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 156969532 1250 156968282 156968299
    0x6031609150906060203030f070912080d15050603010b0702030f01060b0405150c03390d0f050f040506030606040f0801050406061706071d151305030a0807020103180206070f02 77
    0x2c624006015800c01c2d81c1080e0b00450655a82c0040e4948004c0060f00303040900c100c00c180441c4900099891168850090801c2940d89000b41000380840c2c0001d4154180b126070100188200e41d1240c0403079045500e9200c44c2900c4200174000070b8200311140c0d460701241e41c640790b0000382012500001d0400c5441c116550400d0551914810307003d480b6003040c4541c5a0020011140600d181c1c0c0328000840d8001180c0724803104a4089203003040154140c0c26860754042c01c50040841d07801014a412140189081c5040202088200026000f140616441a40e003c000924140c9455003514001c1100c1d0142501e0541d07210800c5000786029641510030904000001c100d41044030782c2c0d0018064548000c045039036400008031801501000c00d00c18114003000e84203610b03540d080e1010000c2500031540c69680246540400101030294481400380e0400000b80c8080b460030000e60710056020300b004618120400c0e400e032050001440000d501c8040450340c03030280030b25440d0b1080668408e652502 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 156970782 1250 156969532 156969539
    0xd060e01091b020307020409110306092b020601030f03020312040f020a090515220f06050306130507090e1c050304020102250311040b0406080f0c0402180402030603160915 75
    0x46052452002c00981e00810403400141420b5000707040c41e2303024602c80c0d00a243c0d5a000a818503900fa00c500f50b00d42d1040300100c1d040b02c11401003036052000f103003080b60040d103103900280d02c1c0ca01c148009400c141c0078030f40a01c145402032088407407055100780d03504170ba850b0078a451164040d40c003100342c3c052941c1c001c01184004182c42680c0c000c0700701039a1103080e076001c01c017000312000a0540000501490401d083c000c881385000b100c50418051501041550909040c140f40c0940200005410011045c0c410003003080407501e002a9519950081807031000020360b6458203004000c0c0e5501c607521200702d1009542e10802450185100364241c804a11503041100051201c003192202c2002c460a010030010303041c0460b000070103401078008544c40f5901c40c0041c00716103060780320900d00d421107254030002c00424000d0030341840d41210b0442c2002c69511611126028070107986000e642d0000214601e42d8007000003910740e80e000f050144259441e4098000541403455003d44188171250012 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 156972032 1250 156970782 156970811
    0xb04153c02011b080a0b0102010e010204180b0301060608060d06140f0f0901050124020a15060807080a1101110a020909030a09050a0803071b0b030406060515070201020d05030702030d060e0109 84
    0x4481c840c40541d6440100d481e005c0001005003040079800b4103540d43c0344100c811850b001c0c00170784020b104230302141d0901c40381c5060030001e40d954003074014480d034540071003440b003103401405840d0408400c0c1c4120040450354601180102503131480d03165a01c040c04200540030440f4040a4400d0b025042000000d40b0707032036203950907074800b809000f15004d03080120850002c0451181c81d22400188100d41482029440c1e04070711148496110f0041500c2c3c5006004203c0704028100040070960004c1682d404140c84000c0e030311400c107403024104003803010f2048c1c10748010441400c240e03030003d1081d600350401215941d900d07880407007220003194007007600041754942070500e0011036901c080a14542105030340e60441d0300d240340d1151140480148000b0070303040c50500145114a00c2a600082e4440c1004100100ba150020503007003440010050000140d901161114004840e41083c58486c1c5070240240d0540c0664040006124070781034000a41d11441c0c00c4c024101e80007410100820103081001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 156973282 1250 156972032 156972071
    0x30b09210a030e0a150e150406020c0d1b060902010903080d0501030506010b0f120c040b0c0114010b0c0309010806011b0516050108040803011206060302040908070c0b04153c0201 78
    0x20b4696880c1e01c0d070041c00280b0907001112615106c0050f83c200c0300c0002046010280c0585081da00316074045070b03980c802502082804800c400c0350819600a0b43c3c07111600301c400340b0301040242202e44440301c84003164080c0c1400d0018503130041c90b50361a1a80c071819200100340900c0300343d800784a4100001044508030084450386021200b916240c00d00001c0380220f141c00181050001c003508000c00a074040c0c00d800945000b03203841f000410340040d41603e400d09140180c2009100110400c2085c9005000004603408401c00b0700303044c00c041c0d0740d110059a1300483d2103104002680301082c510100400855641c03290303070386801207030384031615000111154141240d0051100804000500040d81c003c000480c565105000100e101e039102c2e0301080c240d451f04c4d02e00300d51850021621204120034000c0341c0740945001c0d0400781c18649400d00356220360314081480030901184500d1b00d8009120751100314000c0c01420030384280c40c2d0a441d003a0b042c40030101c0032640107521703201a1540c645d89070801d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 156974532 1250 156973282 156973303
    0x1a0f0a0b060a0c110d0b0103031e0302040b09040b0a17010c141204022206030c140301090201080c0a0e031230180f0d0f0e040213030b09210a030e 64
    0x4558039250f8032a6648801c0b40810030150b0780c00121100c0f200d00007604407141e80d005c0e5100c0d98502042a9513403002103904001c900e45070b824180180030a1100403000010345965081c00c41303010030703100f800070046000003045811080c0c0c849550000011155415000352441400ba41d0780e00c06160030080185440d400f40405071100030802c6004a00580740000f90380802e089000c204c106001e08200c4044112101d03035104483c0300e0a00c440030091402220261005000c0603802400f1070b0075103900007814940010801c001811000c00e502000c1c0d40300b24095000360202900711802d840803000c1c0c1070f051360003130341a03066410a60321100100407a00c04881c00c140301044011b070f006803904881400603440340d500c46035203880b40035201804484200440c0005054a4450403401c01001c980107002d5401c58454500403401080446001c01c1001000c000300c94110200d50480c0d1514440182810034a016205011540d03030304036480d1801040042000000340c1d2803c2000200302c0042d00e4940c2070405 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 156975782 1250 156974532 156974537
    0x1e021b0315131a07020d030c020606030a03030513080d0207060506010c05030711010507080a0306030b01091a0910030209071d0d022202040909050f01050f090d05071a0f0a0b060a 78
    0x404100d0b01802520503091191003041d003805a4240d1500c041c9400d6011188480141e102030010703920343d070301845802c16641c0d140c400351490340782034030103e41d41d90369241d4020209a81d4400190140743d80343c2051081661104985964055074480e802c081d40150314251083c625090110f0102d42c0078000802e01c86500c03030007079424440c4980710001a40301e000ca805050000410003140013a50038002011101d001c3c1c3c500060b01e60450410300c90038107050300710741c2c0c6180c07a1803640c812071161081e10a64001c0111542c1100f40d80b5000f6903100203075544c1c00250440c00980502c4607240d0450b11100f10400011005070003000c4480401440121011020f90046200011003c18120070180404100c004800c0507140c103a44144147c1103461001d01601c5540110080010320602801003580040c500d860701102808c00c2d111283c1c40d0908628000c05000d80002c800b0104111900041e030f41d044840b20300704584c034010030090002c410440302c00c00c90303600c2c01c0303207202084c54000103413000c903030840c4d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 156977032 1250 156975782 156975823
    0x307020d05030402040b06033303250801090804061b080904090606031212050a0501030b0c0703140a1e0809060123030604060209010f0c1a071e021b03 66
    0x202030507903040e032010f04181e030000d880e0a0700c2045900c4100055014031070680c00200341008000b01e40140704840701110004180c4884a520390380c0c0d0008154039071601c04400c8041c0b51000b000700412028996101c0501ca5003480507071011300a044014004507103007034590f000c081c4000301c0c1c00002e9004240e03000746510b00500a8136447d00300b550021000c244a804002031b070549070f440e0800c1d100e0109100b0000504002144e05c48094140a81500b02e030040c9400d105039411991810165800107003070541960700400da50003494412101640300039850030351607607509549500100509000d680c0f5400c0d8080c0101c01d0754650388100c8096101e0f02c8106c02078060740e401d02200ca0120844503000a074011050621103103d03550030b210590145100c0c0e100141d5860100001600b600e1400c0e1420040c06030442004c0e0100b1104d080588140b080d104080340151345140040d01c00c00710141c100b2408007200c4e1052050180c002503000c4001540c0a1031704506403001040513980c000b41080f550b85075004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 156978282 1250 156977032 156977053
    0x9040b03010f1b0207181802130516050702061801050f04120b0f041110020f01020d060603050907060207061202190c1b180e19110a0e01120f140709051506030702 71
    0x603940221910400801f0000118000c0d4002071800301005059540040c5c0c2e8100b8001400d4900c1c038110311440c82810003506040d940d400142040c050b00600c0c8400c40c06410880c9200d030b2007034085604022100c2e6050361691b485040c045402010000e0448082c82074002081c946194411a140b107a03900107590f04040f10a01e00b803042742c0355620071440c10b5200714280b142c0720407000c1c00581070103031b49030800280c1c071450001c0060546001818110b00ca400200060140607408103204041e1104d50a21303d1444a647000101c000f48255a6990364416102030001d03201e0f0392140083c0101c0d80121040014102c5102c04450b1600c4588203d418012401807508502c208540140c81c0d001e48440680b00d00010325071711588030140e041405c40e8070a08805207043c00b460305407090000781c410070b0f41c4402d05604003600310104c6503104070060b04001345540d44804005002da0803c4c2d03040f03060070548101550760b21060002c0c1c0700c00d07110714100c80102031080300315042030425a48a000694014001c84a1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 156979532 1250 156978282 156978329
    0xf0405061b090a0e060a0909171e0f0901020d02010c2102040305060c031902070210180906090c170f010303140904091203050906040b0c09040b03010f1b0207 69
    0x8030300301e103403800031050010700055600c050501c001000f82ca1200307601843c08008016450550340c0040c10b400385010011000304015404c0203000c401042d0701c5a94030000040a0382071207006006c4102c0302000000d10400d8425080b000c0c1824132020380031141c3c050b0705050241d00340c0d00c420000600280400c6604da10948a4404c41e0390183c4c1c2c1081e0051411f904e944603a8244401202c0d1400342007400000e00090044031440780c02e09403840c82045040c00301641c0000d45246000e1001c000f009602007114400e2110700b0100001005118410049a82d4441008020741300704152440850103d044040354400450a0240b0030000c031260340407160300f15501941e05940c02c1d905408031308024402898191902e100d4502aa0301602c40c50210440c9000000d050b80c000030200c040c140c010000b4000050340400c03480c1d13003058074461076548407070000000c54020801224141d0745507092422065100c50194094080c860b80c1d2104840200c1110505a9403510340d0b1040d00c0d28a4020060301c0744141 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 156980782 1250 156979532 156979561
    0x60703110a05010c300b06091e01031505151b0a08030f07030c0c030318080403062012040b15060739030219050a080d03050f040506 58
    0x1446424100103541003840041d141c0000490704940c81d0795280b0102c01d4454002e0100d005540e102070420042035040c0798007200044030079400010042e10740319201c0c4295601010b54a031404054203050f821410b409401804410a8010501080c900141200305c1408141071070140c40d009030034851031040c0750001501c3d0307911440d00611080b030586003d0003200d8007031280c01d80c0d550041e06956160304044082e81c15411010b404e100c14103141480403828260001d1400030040c0d014103000902441d014666000034980c40780041407820b00103008402c005099001d50054041846403c40201401c40c2d0540d0503c1907083c42510000304200080001d41d51002081d400319001c1d094810714290382e0007003411900151030031500700d4858680122107120700048042c014000318000400361602500c11000e44116003c06401009801d04100c08040c20034540b0b4020940580030202d0281d5584015444442d02015500001d040001181100fa008102a802141c004000c0c1c202900c4614141d075019 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 156982032 1250 156980782 156980797
    0x6030402040e19060c260601091508150d0507090b060708040b09011e09030f0822030b0105060913090302010f021603030b0910031b240807090b0906 65
    0x10b61209020100d081003886003d0340380400c1c443c0860b40a02d43c2c074100b010b581644076400b040000240c5400321074400541c2851504034002d18800b80c5441b1b201c0102e81c0613845411003107500102d400310010717103940041c005104240c0351000300a00c0c00d12108022440c80d00c0d01e030252072030348800f005020305015a480740d005290000c01592034484240c0c4c440311590020b03070040540c84004035182007256041540740c0f0301d01e41c59400ca00305103614820b020b4000080780c0000b510180f4120340000821911034110780c036200c0b0301081910301180340007001d6100c0815000484004c1400340001405040c104240d40740240b00601032060380c180c0070b040380000c02071101c0a400315925040c0e01500d404c5548000e000110b07080140040d02501401c028040d1000c0c0382416026560041c100060503c070784100c942580d511514074030b080d8070300401d20400030b18280c101d620384042e07804149075811007025800040350003e444402542d511400c044c0c030034240b64400c00d200828100003804080c07030850018042d4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 156983282 1250 156982032 156982039
    0xe010803121009050106080720060c070614090f0d0e0609130b04050f1501080f0c0304020a0b0c0607030b010e0a03030e0103020403080f070501141302090403090e07020c0f0f060906030402 82
    0x915076a60260700c1134880c281c1c450404256001d090062881d0700640060340384251804c07000385000e250a045a817481c0080c006607282001286000c01c11206400c8000c00058049000383e00c2d04041004c0794448880c0070200f1414822090804580f5004110280f0201001028241030100c80b2003801035043c0701520031010141d0301c1e80010301581e154401d02d4000d144a010281c03813482c0405100000b156404242414407002204010b8842c106c0d6800c075038003030a41c0f1072950f1a0f403a80d202003004040780d0380205c020154080369001510350009500307840355006079810720540c0c01c0140107644014564246a400561a480910110f801600e0005401e2010b07d00140741079600e41340c101082d080f070030b01084d8560340043c6040500500740206881603181402e68004e41c14005c142c080e000e800d5450003070144080c00001020305004000f518014821100c488406242443c0700949480000c9242441440742c440100500e0a0000c0494840360010700603924101e01d0400b04089500001c001326403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 156984532 1250 156983282 156983311
    0x503040309080d02010b04180b1305070807060c0b07090602030306010809030904020d0609060501030c12050603030f160209090d09030b0c070f1407050418080304060f06060905010206010e01080312 86
    0x28010402c010f54026280b0550002507000a07000c2040b064848190441c0311030392002c04a10f0101e040c07220002c2d040b58201500c660b0140d0300e45080d60519110b940720100038010700b40c00141c50384e00500b01c15900e610070000c4138129600c40c8419a1a541d160151400507801030000444a50203410385503000b90b1580100ca041c1100b0b9000507041c2e034410b0881d140c40c10749800c0b041280b400e031400b44001030402420140040000c4200050508081415040c8025200e00105040d500c040c4101c401c0c01e52000782d865500c5910801001d200c44404030104e000e100d41c403000441c00c00c2c0c04200910800b85a87d03a0500311807850b02c9141341c122014080c903003442c00402400001940d0171042003841841100814400c40b5190301142c01e12001e0340c070503070040d410000030745c0110000c900b0184140e0361201c681500d907101c074100710000b0015919a00101b038907040c0d0204e029500a808401110002d03400c0314696a00e41c400e0180e044402e12910460364028801400e07070341a800e02c0c1651290420240c01c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 156985782 1250 156984532 156984539
    0x30b060907022d1b030d1b02030106060918050105062212121106130f05010b0a0e090706030b0616031b080904060803070c03032303010e010501030e1c0503040309 71
    0x29440d103030600d0000058911800ca00e1450242801410942280c46054041c26414130020070784603040130380050104248010524403100481c10012111034001d03008000103034a0701c00203800300c2c8030303070148003414007140c829040d0320250740c015103040e55000341105040510a050489800c41c5035998142e11500358a03001c501180c1f064054900030f809407d0703500d46100360b0390000d0104080c22400c8001501716a04002407009600c030b80f4451203501107008020f08400d424000d00425032460010780c00f00300c1000000302c20fa640310000d40600d40d1142075440180e90396605500725101c031020301d80c2240041c41410b00b1180315044510700140241400c261880f24400d0900030340000c90f000b19407800f0049a0280f1343e0500f0312400000d4075401005503d0075040d83c94500111010344801402c101100304a0700c030402c0c02d058079240e2a00110510b540705c0d44c407900200220542401030600091030f2441c840c056000000f011884062580544008400e01030401c0b107079039000600c26400c0c40311122000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 156987032 1250 156985782 156985813
    0x60a030206120609070c030509090a061203030f0b01030c08150a03020d0c15170a0e030904020f04050f24070302010b0909060f0609070e0105090d0506090d18030b06090702 75
    0x2021503900e030001110b92864900e04100540c4406800d03041003046145180000035004412103000f400b0850303d010070355071044402c1d000b5081b1a0440381218402031005c03010541c041d00110325400407101c0034040c0504a02c0110101da812085e2100010441000b142e44001c10440e4000c0d2a000035000210762a1070346c01181801e80300f01400c4965440590301007080c4d01c121444039008940350b1528851002e81e01402c0da032003601c05080300f41c4150755000380180540081003100c1c0e40000c040c0081d9203558106180210981240c41860700070314280c1007543d0a0729109001c421910028a506401d003281e06001c00020b42200504406566071040d8074011540e54940c2e41d4400c00f140c10080044d0f281c43c800c50f849854018003c01d0044070020306100c0400c1c1c015152800440c020700c4e1007911244600c00140c06140c0d8139401030400d000355030a10451440c08a03640b9900d04a58484403d00c3e41041d554000c04030051102803c00000c510110341585130030002c454000341c40780b0444486040d0140107 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 156988282 1250 156987032 156987037
    0xe15040308010f090b101b02031f150f060c0302030d060f05040e0c06090d0f08040b03061912080a030e0d050306030f01050f04110114030705071505100608060a030206 73
    0x90300410103240040011030030030707640d0001900400320144003400c00800810b20111071b02c0c404000b4002101404068500c5004258200540060445000621600400c1c1864603400020b078285402d013000d501011800c14541011a03158403003990300c080c60030303504541440c60840d00702d0441c0000c1201a2106240b40612400780000c020740b0030380c3d24a41402c00c02190002103629000e078102c000080c4503540c1d0641502c40120003500c04c04003000103464108080c84c3d010301c0007800c0440c0481d010980c0500940550f10500080ea0303031411541e00013510020a030312030300c580021046808800d400003041c61018040d0b158243c14003080c00c40c14a0340c035600f0920303070002d20000603401200308000361400f0407110310001d14141c001c010500f80081c0d41c8218010060004d409500c143c0c12a00e03040e440f1380c4140c0701d00c00c0d1030708900d512414151001030040e840050f0980d24403130032001d40100ca802c14810640900050b0381500380c0c0c945488030503101440010841544541c80382400405a00ca1500 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 156989532 1250 156988282 156988291
    0x7080d030212011e090b01050d1407080f1b1308010c030f0c2d0c151506030203090607030b0402091c0606080f0d0503040c050a0321021f0e15 62
    0x5015807512014000e075000b00034140d01800700b95252412245010041a10810503a014003401013220050000140c6042c8902d00d5030700610742ca0014500c2d0392140070384001e800f820403a6600e00d000e0b1500c50641095401c151100502c805101100d0680038088500400c04410ba134014810025541c074090307170844441c2c4c0300d94030200307031590807440580c506440b50b10350710080390500c488503a4a800c423032403202500d44150300320600078040c1d9081c2c450203883d03203c01c010741c03006442c094002e070300030144050440b0050f003811410340781c80003080e010300070700039603106640c00c100030404d694507118100c003c3c0003800500303074200fa03081002040701e40b5442000003140c60794408040740102141303010422181258131a1415130010260000a254081003c12504105260040c0c0325103d03401e101600c080700d0f501c040d62088561000208120310000d800c4000c01c45400002c50006910400f80c6c1c5600145407540d540c2c411804281148080a5000d29040200c003411201a4120841d100326110002c0c0e6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 156990782 1250 156989532 156989537
    0x30303090615060903030309020f060f0c0d08060607020108100506030108030a0212040501050f0319050411190305070501180f060207030215040b030402040b0310091b08061603020a0207080d 83
    0x240c0c10820320819006000e01c01c0618442c1040c1070f440c107000203100d0748060100404040d00c2c0c0d8034a000750b64400b06c01041044005040654480151500c42040e07408886686910300481c1c14502c14a0701070032801e845028040c100394a0300b6207550046030f0900d001442007558400e0010082011f0700d611010f58040e081d424010b55a61043c0c21010745803840140e0000c2d41b01808200900040e68480c00343c80910040680d80e076280c1d25510299500c0032280040401032505c1c1ca001c10050012518801d0300c41001130300e0300000c1c2da4001c0c0401103610b111340005403050303020340d8080151354414101c40d0307920441d210034261f5003901d03400a1814140690f11150041c1d000020900c10b600c1c00e50010390b00c02e00c801c40c0c041d02d000d02d0205444014000100041e100e1a5510000040d507141400050b902c48400001005500400d2902d90312003104034a8a80e00c26400d031801041c5404001076050103030110200d11002150f05d24001c801075030003803002d541140102107000908040410509400c0b54054 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 156992032 1250 156990782 156990791
    0x1a0405030a091e090b130903050d06050d020d0b0916080105011707030506070e0105070b070c1e11040e030717030f221401021c050f250513050901030303 67
    0x107004245000c140c01603c01125003581d07a0b40001c2c00404401d04444400e500031072070b528080c0001d840b40900010803d240c50404030504101640300713006200e418030088041001c00c0d143e40520140c2c0c803c007400203400c24403034090b80f00800c842021482e44101c5840448554140712041d40400300c209500c40c41540e03450380b00600080c0481c900c040ca89440c02c6008009603450358407401d83c1e07840c4c05480c0409000b55281c034020715034410401c6400c80e40e00003401c0380103820041c00c000d018a105c410241c40303a1044da06448151400d05001551042e000031900001c6005041040300419441090800302d1004000f50701c0003411490300700402c401004241a16841d0020032407100800042540d00b000c0c00c1e10345018480c18520507540103458012440b41c40c0340202440907030091045420203141804485101141d10003203400c982c1c803e50601d20350784ea054a90039040703021404c00c1c2003441000c000403e8a028064450303005000b500010702c00020f845581c400c0804d207400c800703802c283d001a494 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 156993282 1250 156992032 156992047
    0x40516030503070b0604020f0a0309020a050a0b030a05160210180f050601031713030b06030a1509050c060a0206010b0304051507031a010f0e012003030a020c0f160e041a040503 77
    0x7080c130300d039512940c01c1d901540381030444c0c810400148690a80a01071554500c40541035445102c000400341030044c24a110003074135507200524a8008488003004030741001c002952440003010303c03505512031070b0024032200c4000c0500c040607050190b80f854480310f800390624007080181940020281c0100041c080300d5055041c00d440d03030807002c1481d40c610401001064401d545400907101141d0300a20362600325140d060000b82031030001030010308000c9903a1081081064182d018022192180048800310701d258018009607000b400403030000368208400400600140900966000344584142c0702180040c8000c2543d05100b912804006640c510301254800c20038400b9000c4000c0074244092a0809841e000344200c0d51480300354100a1403d03014694074045c241c24200402800c0c080d2900d03490490700d0741000790000482c0804038070074000031041081d0041072540d5807481a0b11541c0a40c0c0c100340b805944208064421a5000520707940d4461a003010341072640160310600145a59048 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 156994532 1250 156993282 156993293
    0x120f02060714030103061a030109051609050c090904140f060601030f020702030c060d09140f01050708010e01030f0f0503070b150307050112092a080607052104051603050307 76
    0x500401075014080c0e0001c60150022403481503e045990214006c0341026426164000150080508580660a150460040110100b40080c1b843c003111501c015055a401020061b03510607640d100c101c032002c105000341801c0428006a00501490008030074011001410f450012030311000c010301c0c0c00c03200500c480c56034103004080e07205a043c1e20039410320106400090700d6460b901203207803040800180d0420400c0e82ca4110640b0300341c00c110f24070740c102e04000c405c1da107034214051149607951810f000180100d006490f014180c51010015000b03e80c02c40e620010001c00020382614000403510131940054010401014030078458006d1861310b0810200000b11016021013440c03082e040000140942d99025540c440d410824100110302a0040e00305009841c00000e41e1700d010b00590200305c00c0d0014908610030466041c24200c403000c3d40c840d4003c490301e004040180703919070f641c1140c1e80c0611181c0c600e07940e0072502450507583c0d40e1603204500310b00342c80c071035004035029000070480009019 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 156995782 1250 156994532 156994543
    0x909040c0f0b0c030904051503150a051e0c031306050a09050c09010b070303050a020d06080d08090109030c02090717070309110603010f05060f070f0c0503160e0106120207120f02 78
    0x422020340074105110b040b0f900791240a1100b4580c021540d52002648240400d8081070b00441c1c040c1c2600c08441d8aa5000b65810104648130085541402c01003020024045a5a10740103100549003140e40c0380e00584040b15480600300c038100c2d40c2c000300040007181d418421f450044c03040749000103050115241240c00d0400709031505201c0c00368000104060582c4c20219075160340c0c186000140b075915001c481000f4010404405d040a10f8081c0224451500054100001c442615942e9490b83c40f032116509803200748000600040c00030318410300500340009601e070002d007641461600840c035407201c41d10001c0112150b0002136102c01d005014000c90801403100c815044e6030340752030756041c10501181c811407417194070b029000000e04280000751602c103446005d90700c80a0407195921909146400343c0030340c0034041c8280241111a40c071003004888a100b00c03882c860010f045680303061410341c0e44001c0408500390603602000300d10300040c882600b25191941030744605410610b605c60003490321 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 156997032 1250 156995782 156995789
    0xe06011401021c02061303090e04060c080109050c0904020f09040e070f0b040e060f0a0e0705070c140d02040203090703050303040602041a040612090627050d020a02011d0102030909040c0f 82
    0x40c0c43e105104540280d000c1050b40c3d010030b0741280c1d0100b1a5051070211448141644461161003001061104004180c0c024003203209556440f8504c590b207030a40e0b40201c0c0d0056481c006075071000c108840c03503810309401900e110b02551b134000e400c0003600c41c04941a94903c5504440603000a17000388400303070307510142c40e0103803118602d03190519040c924100c4464a010300564032602c2900e10301501a561341a440000e4416191700b490b240c07c0490014086400900c2c1c111001345507070320080b031845805002d100020a0040c0143d60500c1c9640900001b588003a12825983c0141000403010410030001940150320505005986038038148840300103001e43c0e0310020300e82c0d5040004001c45030b8403141009500903d0710000170101d025250100040c09014011800100052030140c464440d030b18000d403040d0701541c144c528820010800300c4e22243e112800a02003018900840548408020000290201801103916140b5a600040c44511089804a41d2a130304480c0600952201860b0340004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 156998282 1250 156997032 156997063
    0xa0c020304050306010b03062b020a091802090a180305031006080601050d020f040512030c06150d0813030816050c0312070624060507022409060c010e0601140102 71
    0x1c1c03500300310011343c0f04c04041c82010302c010004400310781950b80d020250f4100c40100100510240c02c2140c3d0b00c050181e00800c280d00c2000f000400051a050a0154104698089850b001c0141d0550300f0448100b002500001606584440c0102d05401c0304060609050007a1034807622440e100101492610683e002001007000001c10700810340d0b0040d0507100c6564481e400561900d0310b107221418103001c2c6074001a401028000429841000800205034121000080d11103d80d110380b01c1c9030b48070300900401d0360483c425028039000310351203c010307000100c24400d2140225659440d101c1503a041102ca0500310440035840f4802c02404000c90f103100541038014200700421042c41100502035440b01400e0a9191603c071103040c50790400344040180380c44a0802d40c1340d01c85400034000d40103200304074069002c0c512042d84100d080e0402140c0111000390452601c402c5d04240a116000000203141e40d40d00c50b0701c01e000b000c2d03060191601a103c070b110089864982d0800082c03420303600642e081c00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 156999532 1250 156998282 156998287
    0xc060314011d01030201050a020f071214010b03120a170f06030d0804030c0f0302010b0306011806050a14010e0a03060906050f1f090507020a05070b030109050606130302010c020409060c080a0c0203 86
    0xc0c09102c00301107411030f502403e00c00c0d100c8601100c00d07170034100d000010b4140c81c010701c280880d4180c440c9103800c488a01510301c507001c802c0813145041c00c0710301e90360115501d0b80c01041d84072074014200f00140b88505480c54915003030907494003080c1420390103595810208110204100081c10308100245102201e490403c0341c41c200341d1805003944004040190901141c00821002d041c001d400000e542c0c03501800700e500c2503135640100032031302b004030b0850300406041c26400101850140070b40002d507408402989501c452800040d1580302803043c1d01c1750000e924103c004003042c424450800160f01403980441c0d41e181c105032031000c00c1c0004005c0f02191030a00c800250900080086c68140c0b101241c0000c0c1315200e419050740381a00483d8010114480e40302e001c5441c0048030050350494480c9030043c000e50322148200034050248805048000c03100355800c01c0550b10402050300d80341d0014200050807603c0d904d44400f42c4003002301c90404900a10184540981540b0400d544030715984040c2d030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 157000782 1250 156999532 156999569
    0x10c0203041505071e2001110319020118110405010e01180902041d1501050604050603071202070807050a0c05040b0604090506060f1911010c1e09030c06031401 70
    0x1111502c04030a108204020940600b04000c40e6008038066a051610400d1041c5a1034100203030942034800d00d065449440b002031440d400780700e050700b580ea8403c01850030440c0201101d504440d40001c0da40840d034803801c101036000200c251034002140103002c0300311f075800100240000e030b0700181d01c0300d85004e0b000300041114100c0341c0300a4004407031910380415901214000140070384003210500c80862a0700444040c0d510001401500b08001210202001e0b80c0e214100aa41e00492180350341043c0104000380080d4855821a958070704091801800d044140e103480003ea049400c1c1120254021a101c00511441494400041c4030444040c4840e0320307006c1c00301d03086000b03500c28410300035291404500c180d5255410740c0c4180d088900c00d1600c840c0d419115882c01403103001c10402244049601401403034042c000c4258000850325800d60359560203003290000a0781c4c064210811400311004000a42070a40d46001444a580c0c04290340282d5070b0000a0080e0692254010034104400c04 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 157002032 1250 157000782 157000799
    0xd0503070c02130f0203010b0909010506090d0b0709080a03050406020c0301050402010207061d090c030f010e0c03010e0402010c060c020601090e03041410300f140412050f040f0602010c020304 84
    0x185031031903060755070240300007800c681ea80190184041305032410340040008605181c102000d482500401c54020708166601c5052007018070446c4121500518844410800f02d021040001c1c1c009010345820342119688040441c01c098071410304800146d400074003005a1541081291106d10084000700300340d080560020b565284544600018412030601e28021003030900e4040850701c10107131040030503140c00058011a64401c4640780f41c0000c3ea10b00126230304840701100c0d48920340c814402841c2d039003448203031004100010001c07410040582841000a0310a0180505200850b001051954103202f000b005840d0302258120242e4810700040000282d11900d010701d20406848142c040c10b90a1703404c45540c5a0060f0f1072000a8070012100980d142d0980700103140d01e14100100800030f2028880c0c001d1781c40f403074484000b507020200030601260500c0d105001410f100e003031071451300382902c000003403681281e88a819074005012041207440e40a0103401480c90162000d98589404c2081c40d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 157003282 1250 157002032 157002047
    0x905031914070b04030606050301110313110f101106091f0c0e030f0a030206070504030b06010f02012705070807030b010b070203121606060503010e100209210a03020d050307 76
    0x901180c41848540241d1203060201e0070150070380041e1540d9841e1039003029005000c86200f024001e40c64800001d48034440b00d4203480c060441101c41e2040500c41b6180c2104140c9004905540504c0c8a000c130b6150ba41ea51031345121009103500e46d80b040382e030f080220b2810044000c00d00d01d425044032148055528403050300103404450800300040052156504560b08621051810b4040c4240310740f400300c0910005070b001400f84a03034202c540070703942ca95080300d11380a40d11006000003030003c041609903004070390100d900e070110b1000007112014507001480c040c2140b81d103240000104030403601403000034820500a042c412000303007103180c6076940741c0d0040d1005206842108501107a47c44c21590140b101181106820080c3e644405a1407188402440e0382178085404a2a10b00c0005880c201030240840d84100305025218060300c291040020307600c40b07403040d580040b6220310b11005615003003200302c24144503c0240b0b040f144600e00a80381003000c4000e502400386c18001c005009611904 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 157004532 1250 157003282 157003333
    0xc070905011e05120316260c010c031b05030a0b060f0406080a18031107030c0f090b030d0f140903060a060e09070806060d0503072406050603060904020d0f050304060f090503 76
    0x510080b41b41c2d00d041015040e440c1d40c420b01c2c00c200000f548003142401c01000b404815444000810a0b0488a8001e800b1100001d0f0300302940700c112000c142e88280142c0c059a8421007040021580e5400900003c0c103950095034000c8210f04041002c4c0f01003541310b03030403a900c0145004100031a20307400c0d642c0b210204503681c00400f004686001c500074400c0911010008541c00301200010584404a11110305000c1c041d041c0190720307151952815240c0002c0c0c1d01d240c14103640f0b0740280300208007011500000308501320307080000108102d0819807010000b851140b0b64450300041c0140c1041803090039440003600842255003c0142840032690114545400c050112086500e0f8404c078a010750540c042c0640140c8500401600f400c0c81103001104502c2416a04408200a64498003004441c2c0002c4c0d803031a40094091002400504120003402401802031540c4000d0840c6903544e0780c038550058100c1c000048800e5014105e90b608281c0c040003800c1d04a01070007000d00340c001c401c0203104c01400d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 157005782 1250 157004532 157004557
    0x90402030403051e12070f08071b0f0c03120c0c2c0405060f090115090903030213290309030717091e09010605030f010b0c070905011e051203 62
    0x40440c0425000c3c40803902c06043c8000000001303144d80700c802079560001c2c8450920340107100000340c00d0318812041e844000c101510364141580780c0060031a1940041c0c602110640700c0e5407180d1003c20007028140e050395204984094080e42103117441e000080400f00110107005601c00c441000494000080d81a10065104c0c2c1403e000122201d80885038966a404108070401042c440bd200010039103920a05e0511811210b07038940741d040a00322210103e2004250800b503605000701d001a400c5202481e010745009410118140108000b680c01940148610400c40024549072521401c42ca00c0c02c80001c2c481d5800c6141c8440050740341c2c0f1170f10100420a101c40120242280c40440030b44031060405000d180d030049400c101c0104400794440c00c98462100980001038851195040320302ca0100005208001c2e403030a0202400f42e0000704845419001d50007011800107580d1007401e000b4811a8002d51801c6280108003034481500d0304140c0c06200141900c154440c0008201c0302c0025445 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 157007032 1250 157005782 157005787
    0x608042303040306050411120c0109031e021f0e0d0809061b010501121407060c03081008030d0b040c0e0307180b0301020a080609150a060c261e040308090402 69
    0x12480c0d81c114440c2d500010b0806151000f4402032000f145020f29514409542c01050141074110341c50f40d80c0560510240060740d051014400203d64642a000c40c0750002950142c60380e155000070403106c500c0052554011280e005160800d501c020f040e460400c041d205080818030710380300d0682d5442183e0303000d0b02940c0000340002640c3c24004644400b5141c04d4002c00c19540c44070007418041c01c00744420750b6091800142c2d25107010001c0340340801c541c55502c2d21220941c40d9070301940c840b6002400040b511080240c0000d40c00d40a00c01081e095880900010700420303003900300170803600031040440030400102401c1002c0c2e00c0020b03003002910802c0c040800f100c50315840708400b40420340030164155002245d04100f0f5034000b04014007415088801c170303945035034242c074040115a80035002135001810070b030104a000d00401d00c0c01802ca006000c141c102c00880e4109070940038040c1d0050503510800107103186410507000e41409050000441c103441c00d40303140c9650205015190440303110304d600 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 157008282 1250 157007032 157007093
    0x30403050315030d030209010f080f0114130504230a030e130f090503130e040b0609070504050d1101090f050a1403010b0a09061e06020d0806210109050106060804 71
    0xc0c2d030b48409205006040740c1501200d441c00170003079000700704102d0108030ba11030b4110074180900c01c4075100f4100102c105065a20b8400c83e000f09603000c2c942140c004074040d016401290b02c0e07005031841980102882c0d0300121402e4003000c000d2000c0e810581c0180c0080085500080d408100b00754002c00448041000441440c0130800414601305003040d0170345001e000c0f90030403030007001800411150a40080a8541c0c41907942d4580a088070010b05001c0ca89001414a150003090107802220601e4920305003900e13403010800490428200307485007940481103408640e48101c1001c09022410754111881e8900b60106038611454000d0a0003480c04421a04907600c00754403503408008010480d40003295600c400000504080c05401300c45103402400d102d81e40042480c501c121036440d4010701c20035141800841d03500301d000c0e047c6603200c060400030080f101280800203a6610b254000051140760741c0c506242150302a900001c2404025010000412595620700c4d10192580380b0003d8042e80d03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 157009532 1250 157008282 157008301
    0x140615041a040e1903110c0102070605030f070e040608010e06150a06111212090d1701060e190b090307080a0b1f0b040321140318030d05041a011a0304030503 69
    0x8201c04c040007031031a1244020b080c10340c0042590861130305041030340c5010f04038100482e1140264000e0700d010400030000706000306c211003900d5522024a14001020829030000075060f11942d51201082d03079111001051440c60034019160004074040e003e14003101200c010a0074000b59101c0c00c000c0c44102ca600c00b88042c8103100c0d14244072004440d440d541d00b00d4038155001000300b510000f032244a020006510b071801000c09100095015652040c168600113013102c0c4500721300101ca4100c0d810385080059103a0300c50301d040150104803580c80e252800c00051504d419119840100315611520201010406603400c050300211003012002c1d440c5940000204000040d600001e0840c0c0009000424800408600249440c420080d24407090307101508451000010004060403041080410745103142d0000400f41d201c5507030b050741d0034a10322903142d900f120011607040e40e401c104100201c1c50740440c10082d40c050142c85003240229106408142800c0c00b0050000f03062142c00400f080d5002ca = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 157010782 1250 157009532 157009543
    0x100c0209070206090618060a02070203010b0a2c0f040f0503070b010f0302010f08070207060e040608191101050307021c03141003050601050a05011b0f140615041a040e 73
    0x1600502660181d00300220029a103200854024049005520100d1100f100b80f4055600c0804040d00a190645400351944000e40c1b211800b2070b419942c2c3c065002031501d41140c1c11009200710004001c05107906802e00da01400600801b030389500c4120100f0408510321403500c1d170000c0d0440c070903040c0c40b031703c9240a9183d88910400900402402c1c000050200d50001c0c40740281d0340700703980c1c00310500c640b02025540410300b42c0f070000150b01316283c00c0c0000c41c80f17045101442c0f10024004a400c03541e540c0014141030f07049a0a110701c4000c0c900c000c0500252203174400d820315007803a20f07a1452910810094590321070210041035030360b08603201540c0d0b80c442e4029440035403d4800e03000683c14021028101c03907605100032a421300847e000010140b070040002c03001c555043c2c50b044184103c2807103080f912101d142003183c05061104410011603e000300d20000b81d08680c00400150030400d010310819102803000701d00c600d003024140102c00c201c504180021003800d441c08158a503507034000a0a01 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 157012032 1250 157010782 157010807
    0xb0406020726040801111204120212040803090a0602060705040b030c0f0c060a0e01050c0a050c010e0717150c0d0c092102010e0a0806041403130e09010506091510 71
    0x39054501641c1c20301e10b040001c0086604001c0208180c0345410114126401000c24032201100311400040125902036070b041c002e440c0030310503942d254010000c5880c1c0c0342c0064000c01ca59500124800c012418100241000b9007070a0004041d02c3c41d00100040092040e4064000351480110128331a070810809440116414001050721400e504600682c0c070b41c021a82c001140c0c1c00d102c0980101c1300180305003402581021840c510381158458169201c2d8440100c10803503660f20048010344000900804010304091501a14102000702d10a80b61860408800407155422030502aa000f0703110110f649001240f40040303480500c01e542a0303045c8002d9801000521403013408203410707644111165000314402d0320b4030818103d141061111765401070240319000ea00000202d00801c1b0b00d503039070442580700380044a01d002034a5425441c48481c6500c40070220f0206d0042c07120000c0280511a40000140c0d0351881602d018040070400a1840c42068004c240c202001c0b440c0600c644214440f5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 157013282 1250 157012032 157012073
    0x3060c250311060a33140105042102090702010c05030402010c1b0b0309010c0201180318030c09050106080106020318010503070306030c0308090a05030a030c0b0c19020c0306060604030b04060207 85
    0x4901d001c240404c050403020049005d15207080b0018910519490100c00c200c8660100c04156141020f180801080001090350705010042c003000852013810840f4210401c03035950a840d1074075407803051120400001d805081564107040c12001e22560110a490744107409203400c1c00040b501e401d0209200c681c4400701b410341900d019001c240101d03600c0003940902c02c035030004c125150741084101c0c2241c003c4844102803204402180c8082403044040540c1030040f1090030030520b83d603940d0b494000b003055100041c15616040108100d541015107503005000a00240d1b10704040b0004610310840c3c00401c0505102c40440400c1f113061081d81b044019503405140300f245180c0303030b0a141c4a144c02c2030941d240300e4001c3c000f010405042c0030a07c1d1280507415190039078078000595590301648001000a81c03085d0052041104030750070075682030181d150640240000b01c01c1e0406040c24039600400d580d0280008100400018425641e4181c0c015005800180c0300d000d50718244507009080840d0051 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 157014388 1106 157013282 157013293
    0xf050a060c172106030d030608033c0d0605040b0105070b060d0b1501020607080c0d020306041107080a02070e061503060111010f0b03060c250311 64
    0x101c03080c2050095040c40e443c101000707043c100c000700d140d0202e801c40041c00b106083c103201c603101011007480d0920089007040f00c0241c0c0da2040701803c43c04c0645011a0304180c00c0003c60500004424007001006204804140ba40b1500140070f250105440c0102c002014501445a1b003c101c0042c1c40d01400e0024544981e172449a00808064001071030481e80000210160001880340301212111125032000e0310009262060050000f418441e1110070710141b44548400e48280848030080540d4036038aa00c04600036112070f0010302d0900b440415090f04006420001d829070f0145a801c4503005070307403091112480d181c25201680c119007180301840e41c0d00340b107000565000b0018180009080d03980c0c101142110b111030300018085903664001c119628060114582000d0f888a00b00c4c1060400030714140000500329002314080e5488011000701070003140c0387e01c5410254426070300d = true := by decide +kernel

theorem cover : BRFrame.Cov 156834532 157014388 := by
  have h0 := BRFrame.cov_init 156834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 156834532 ≤ n) (h2 : n < 157014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
