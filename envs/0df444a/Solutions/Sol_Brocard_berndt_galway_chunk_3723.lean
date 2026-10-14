-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3723
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:29:58.367254+00:00
-- url     : https://prove2.me/submissions/a313ea99-c948-478d-a271-5295d2948850

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 669424460 ≤ n < 669604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 669425710 1250 669424460 669424463
    0x3064101030f0c0905040b010e0c09090c070c05060c01150f05180703180609050d02010c0503070827010e0c2b0204110403050609060f04030903081e030c090315091207 73
    0x1482e204001c285200540035a034011b0340706900b0402c0b40e5040c40c110070b00d00d20f401407494000c40b01c01d00c40b20005603103000b0001c0e0450100140740d0390b564002d013840b80f03401c80c994001d07503004100043e440c912400f055202c02410941a001c1e124183d864002c000e035007985034424140c1c81605c0c1400c01c15446c4c4110000c40e000b00050600245207c41118511118000c8040580e2b195036142e030290700f404001c0c03146078840c0c0110b10081107840c01c00d01014042d80009065081008002c100103452040c0d481403004c40c003542c403500c00b225506018800c07070181001c0600201c0c14040d0182115032810501c80c0c000c241d9400712101c103412a180411406000380311a400e82e8059100d880180c03114100c1401400034501440240c0410310b020302e01d20740340141c0030700030103d6200035a08000120307030300c05910f00a8940c4404000e980b4400da0b4441c184400420070a4030342c4510000901c844440c0a10080030861015000c2d5503c000b204200303000c003080e040300c43c2082608003000351981900784200034861a07 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 669426960 1250 669425710 669425723
    0xa0302030a060e07022b1b0f05031b0c0339040c0801030201020d0e030c010305060f0306011502070e01030b010e220501020a031a0a1401020703064101030f 68
    0x696503c190b01210081616040b015801100b002e80c0c621040040e5400c0301304082905400158030748000405c0f11694100030b5950030414281c0302c0800c1254a200e5402d203402500b240d0700c1e00b44840741031400b61200703e018091031250320350a1415007408111003980004d81400030441509060201400c8000c1d200c0402114412200a80d0b05507185d10035590f5a041640e55214590704610000e440d02c001001e400341801b41c40d02d01002503550003c0c007241d0008081c03801007080d072102030104801c41e003040c8131035505016190010a1100c0c0e00c0b240c00c01e041c0030581c01c550f0103560303501081e012104213010103003895140b240180f0241c540c0b18462900400c4250600c948110360615480dd08420006c00301c81b982d40000b690740d0034a84c9800340f0000a9102200c0c0c00018510700e0000d1400461403280c1081d1400d8401d403001705a00a005030710080d500b02c2c0302400130303241c80345001130503c200d0501440d039004a0501500500c11080ba400009030b20f45d068408a079085440b840c0030a41030104c100c5d2203 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 669428210 1250 669426960 669426971
    0x180b010806091f2322021e2b0207020108060d0c0b0304030e091005010509010f050d020c03030105100507030f0c0609120201020a020c0f0a05040509030904020c060412140a0302030a 79
    0x4500c90303c0c41e010007420040d040900d12001c0d0181c2c45455003030454514802d400780d8840d1400c01c070500c11103103414540c401c0b0050752070344ca041010181c0464076003115403039103010613645c0c3e01d04107a40c816502d49001c00ca0444c2c0c0c480503c400c00d402c030f010380d090190003e0003090003c0c40b1410410b07400a5040d0040c3d986d0244603030b41d10003042030b0381e104803011000107881d55000c065506094802c1500203844c10140e00d07800c0c1c14140001d00c030b03025034548141045481c1e088c3c1c032203003800b0b041100c0b003840307112005550f10804c54059640d298401e21400340180e103000d91815200e8826000d0b1558a50b050f524a03080790241c01b4110313a1130f4001e4100340d07506559016000006503011844400840e000d8001503110030070550702070706024111104030f000d8808286020362039a10701400c04141c0d0f10844000030310380c0b1402111491402070140356900140700141c0f1050350500043c94a109a03c18403094000207105602121404240031150b03407010802c1c041c0c54407040c000d0f00a144c1c4500b0b400b600080 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 669429460 1250 669428210 669428251
    0x16021504140904020a08031b0f0d4d0c0a050928060e060102100e120a1205010306090c090e1b0402090a03030e0301060e010b070807170d0501180b01080609 68
    0x11644401055000e104d806c0c2124208c0c2030040c003d5000a03c50040645020904014054102108144000c0242c0104460410b124a0154914019090850710207a261001483c800110035001802203c1407081e8120038940d0f03d411003940e41503540103030468400d51600300c08104a1040c3d907800312074403200c1c0c01545a00d04c41c3c074440c00c802420701408580040c2085070000e4100b4040c04011442d5500b0942c040700200030015103d0501202da0725a41e80d12841d50a0840b0030f04800b400f03041c0300600b400000020300c6400d0b0401d6100e20300840207820020b503200703100801c54100c10b40740d80c243e800045950a00210107032070603021010150001d841c2045180020f11008010341045001c24084418058282406d00c55100603008282c03a4018550603c0540241800380c060005c0480000052003001c0282645185a80070100d803801601d44032080d4034003000e030409000d0301c595608034401034003001d201e178011003002b00300685801c640d0340c43e900c0500c007080c0801031084d030380c8030b942b050b074800c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 669430710 1250 669429460 669429463
    0x30c0e2d060d15031401051e09030f03090c030c010203130b0904090206070b0405010b0f1f051c05060f011d0111010b1c021e13020c010f0216021504140904020a08 71
    0x151005101c8260b40c90303d8110301d80b2103c07402c0d2200b214512a0314200c10002101021184500e0780d41403000c1c0c2402681c1d8004e5070500e58802c0921043d02d514002c01884020400007036101444041142559890000310004a0392801105a49450301001c00300400c4001240802040e07080c10150020962481a13001321340181d100c00811500341c8603480400003030140a00c112139020100311624214402d141c40003850a50800a12400080034048441507050240d0b0868030040d562881d00c000441c011003c000041c6000c540003801a038199100c002c8a6202e60514080d804802e02040b140316011001122900016041105659030b41c03000d003940e5640e0b04415005d501d010480c40d0034454490b20611104403503002280b5041c90084001d9034081c2e4903c00c0341039045c0c0280b10011f03210300038580c83e240540240031001101520010f003001d443e15070172044001c8503000f9070380314903041e016110580552140340f150104c00c1c82c1152001d81c0c02d240180c1210f4100e40001c0c007850510b525050400e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 669431960 1250 669430710 669430721
    0x705040c08071701080a0212150403021606020327010c060203090106050a050303030906011a071209031a0f0705090301020f0f030f09070b07060e011506030c0e2d060d 73
    0x5404666010708224616500c42c140410444911400c0301c103e51502c0c400c02d98134003a800000f03100700308414401c0c170481810484050540d450120505103400c242c10083e4032108500c0350001010007001000c602c141c000011105245080803400315204513000046403d07203c1604254104000040d808000c40c50a00203540190308400001034464504810082105a9507001c0c40c000c5d0014000c102045802081c102d045802c1c20320490342c0001c01da4004140c40c400e41200800e40380b554001313100306507481f103c001d090301d1055564810b444428442e040a9500403200010041c13441340004071058800e5016058951002c0d002606182c1d05420951058000201c10b0401c200088100042101030164040c1c10000c280c024105540c140268149180300b6038802402c415100d111132112608258800d0620f03c5d5240b2055a05c1911541d000f0050880704c0c4400000480c04656501c09140c035003600c000401da04000107035400c0700012404894a004020030b036100300b05210300102480c150084 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 669433210 1250 669431960 669431981
    0x4050103060e190b01030b07090f0603140c13060f02031c0b0f15030406050c07060c0201050f01080f030304230f0109260d0b0f040e01050a0b01050901080f0603070504 73
    0x2ca940761101103620b1074542203020244001c0207109401020509400c080f0341507a4118620416a9a5500041d528045581e000101d19840c100303000800b04c1e0f140d07002d140005500e40001c034140d110044a0526402207460041000c80308074400c00549011340c54081d2000d02c00e0040e0783c101100d0000910385040301e46001c0c1602074032000d040f20203180080c6041148201103464030340c40901c100001489001c0103000515241d62a004078003d4842c81080e6540b0039800f1000340300341a0301403c0280070f49030aa80ea81c0d40b400c800000071800d640003054010001c0c1c038600c02581103940301c0e121100159456028103030009613003070020b42d54480520019a130b202c0040700220300075621740741c400d1031800154485103042e842c0c15000141000c400342118119441c044001c01c0015103c80001c1c50a50581c05a035406443d00105c0e0301c0c0c01e4810341086112f0003401c0340421211318034900550361441050350310b41c00692804000b4a04010310010a60001005030840b180c0170784a102040442d1b000694 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 669434460 1250 669433210 669433223
    0x115030c02010e1519020c0d0e03120a18140d06110c0a0804080d020c1f03060b0d092d02011107030503310803090d0302010f1b1709060f090a0204050103 67
    0x400800400d154480031505c03250680c00c40c60408621111903c4034030104101d4200428012001c1003035600f040071100761645007250303a5403185c244102810703880350b01061690941c5411000519900080e8030078484903001b61000e11107400640c0e07528020400140d91108c003600510101b0b04c00c18003001208011442500659600c2c3d0400c00d6103460440003450060441d03005003100890f50f10340304118180c1020300c40b4500f04c010741030a002c0c0c0250100d60411800c2040c040b034004800300081d08601b800901892903802503c0322155002c00d9100c0806150410356584440803005521440016501c0c0721100c081da00241d03160f550b100d0440e4420401d2102c0100307969806000901c4c80501c14650f01e440707130b414a100518007400c0d80c1c0c4074010390303009502c6481440606c1003414001e421200350010f601e202000380000d03440c410f4860102c01101c050018401842007203180c61504c5010340604240d200500c2139a803103240c10b14a150008044071440d010f40d440300e80060b2614007540d4060351283e070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 669435710 1250 669434460 669434503
    0x20d0903022a030705091305061614030432030f03070305131119081903090f061b030c0206030403081602070b071704180f0605090115030c02010e 64
    0x12144491981144030302110501050000a0b80d940003541c0c0045a6040d03550301c150f5039456030b500c6100340f669000684140074210812131603921607032a001281d1999200c185c0480b00045108140c0d00003120010300140d0040e50044034413803644241c1c0000500001c40c4440c00c1c240007050b504540110390300e22174564010090109850b014000c0d954440405c0b805039140306000e032205005014540d610700d0066001a00700440d8034680302000c0003070404c200c1210036a40c0014440e06030180c01c0c2c981034000601c2a40d000c07443c290780f0034240080342c0300d55444080404006000c00a0031b1900c1c0c904500744210305c9802c0b001a00c07036001840c407440c001e03100c04c0524a00300c02c1c68489110044808011504005010701450701c03c101a1000710750030265121018491800c01c585921950308070042d040301c0454101000d03186508aa656010318420900820366950140302c400502030260080c00421000f8209403940f10343d00940700c1d980b1500c00401d421350000d01041c10b1103200d030ba401d100216401c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 669436960 1250 669435710 669435733
    0xc1e08030f0904060e1501030e030c011802040f02030c040b09012a020406060f02030a05070203070e09030c0c0609010f0503060301140c0d051e01030212070305060a14071409010e04020d090302 84
    0x113200e042c00410188500324103a03d0a213400d0300041d494046114107150b603610710181d90b0041003043d42c21006444000f0030400c3c03007160340701400f4601c85c24101e10407400c1c034000c0c01980c115802502e00484000ca515801c1504004c0000b04603000000c7d5181005411190544e80c0d0307200c921883e0380e140d0010a0900f0300100c5005000550b01c1507041402408021501c0542c400e0b0b0020813540031030101e02d01162104a640b000a04007000c43d80515401c1707143c04203110700d90b03802000810070032030346c201203524050103441030242d0350040880c014007207800001c0100c09039014034003d41d03001400400029800b841500380404060307069a10b1810321901107100b0001c0030040c0708260f048041503040d82030481401140f81022401400001d011b040c010b0411071a000040001314080c50740f100507074000c4c0c5030000c00c1c0001403c00d2548000c44200d0031300442d8040d4001e50031510010202ca45452a0018041c0151078142c1c42007160741d00140e0801c1141c01c525010303c9240f84103480b03a8013034403119000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 669438210 1250 669436960 669436969
    0x140c0a030b09060102030a05070f05030a02010c0f030e030406031e09060605150f07140a20100e0307150c050304150206330d080a180b04030c1e08030f09 67
    0x6000e01c05019000120511041eaa00002176600352165403401540d103108503d8206450005200024681d20012540c0f041c456010342008012080356910705041a801040031010348034105090241500100002d1040c54465041490f0001508464003054a01904500704403046491300f070b00c1c0b0b00c0c1e650b0301c1400140303040510100003031036000d030007030030120000084280d9207c0c99030020191a03d09218485c0e044090040300c0100ea00f04400f001006654000e2056022100c3d020300d110b0211002440700c0c41d40101c0081c0f001c01350140042503602c2c28280001c09034410f40e05900207102050040d900000c00403c0144082c6c804406200c10704102c0000c0a0b141c01000341c896120311340740d58030004c0502d5664440c804042990403161145801950102d01ca4410483c40641005000940f01c84410f400114808201542d115010f40282d03035110b803032005010b2804001c00b412a50303481044019405000072850114032500c603245203644985040c40c65100138a05103845101054103980d0f40750 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 669439460 1250 669438210 669438221
    0x327060f070915050f0a031401030305030105040f05041505041b06120c0306080a03080703090b1321020307110f0301090b010816050a061d060a0c021f1b0501140c0a03 73
    0xf122180c10781ca0518000003414078010b8011844002034042400d440130f9101e508151000040644020519612410001d20a9001b4040c450040341800b400c0001501d191144c50301c2075400450f980c40c7c0c1e95240100001811010308180c50181a0040741e0303042c15100a4078200501c001e48030351100d03c0d40b0448103000d41d07000000c05002d240c90003404200544c004580f00e21841c0d07140c9044246603513503020650013080c0001c17003e44143e101c41c0810054181c060b01b0042c80b240989002c3e40c940c104805480c40041441003400c00503001400340a000524036452080c840b0801094090000c03100000b1908650711000e0540c4d150f91054010045400184610285509204220f001e11410f01012035082c0c55948200b50801c859640035a004400c820600e010000001b80920b54581d01001e00410000d101c2da0107910038010080e00c500140601c8442e880f0290040d16a20001000c4940592200d0b60706201510300c0d549070025506050303600c1385603d108001c40040c181d00c03010b0100303004040300c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 669440710 1250 669439460 669439469
    0x51c022b0c05090d1e060e06330607080c0309090c0703091701090c03110102280204020a1107090504030e09090c0402090d06020408010603110607080327060f0709 71
    0x80c50001c44445455002046540002050300c1c0501d40c00c625140c0103284803403181100c03072036403c01c5140b2802c104c0c140d042580500030030011214240c03968008205442c420940410441d4070903011700c000e401c541840549040e0000700b0450070100e007601d0b00b4125601c04c03e0450b00740d82002402406e00d1516041180e0405032858406080190b29a0007801c481820301802c07640120103075030041588030075004107541d03950051561040740c4d660300d08026a6901c0b100c0c940e016000344410809001c0d0304518540480408014240b11305a854090100951001c0715440403c0502a41d0007020041007190354000c000780c510010325481c140c00c000b42281001240f1038415090300741880020701c00014810000b040131100140d0321008100021085485c80000910490010400140d42d440c10f51096003140c1c06020a4078113052407008100451240072001000c040050020078015141030001d09002c041c030800c1480142030302c28080346000012607028500440110400101c540e01000c900000c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 669441960 1250 669440710 669440797
    0x706060b03070203090112092109150e0411041703030417070807240905060a050109020c0a08030c040308070f12050306010207062d09090e0a12051c02 66
    0x10b04050030000d440388140d501844c108440244010781141d450b0b4040d500d150350140c0c02030000701205804a0920103c402c2a0f00400d608080000d40d000101210300e04118031170340ca00d400424042d0810005004046107582d06020911021491007198074812480e5850580215141d10b041e29008100e44100300302d000902b0420321140001620001c2030318111503119030108680079505040a0784c0d1401050440d00841c03d05132000c0034071001043d01400b0364945481445503a0300d40f000b10341a0302c90340603000d01e180d100c840d031034010500100c0990b0304459094103661815581e51120010b58102ca0419580f000303481850300200044001801c2c413204890910134214174160b40041e40301c0c0e101c1d216081c24004507211020951901c000280c2c200320341c1854075035510038100300007040c008442c003c5c3c92040380341144450000400151840307225070301c0003001d600702090000884090704044003500340c001100341c080a0b5114140003030040a003065400c000c10801d0040d00341c0c0014107144007549a0b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 669443210 1250 669441960 669441967
    0x50d0c0c05130905032a0a030804200604090204150809070515130305010b10230d0e100f14040507090c0504030c0b03010f06110d0f140403080706060b 66
    0x1401494014211501150030150010364601404080e00090f54010003030301001820301c84000426900e1040c120496044414a0718004403d940c0d6245e9524060701080f407074000680020b2841c4080401c45000c001d01d5062071310b41d080801d090307030402d4000d4012a0b8010809029003041d200035204500030b5441d0414a80c00c150b2603207600d800050040601038003400008840602d0f8200403500035680b00008940034607a2801c0c46802802107901680c810300040d141d9520103031142052200c2d6030140015042240c83c00390302031035141e0040c402c0d841103540700c165298540710248510070f11b1403094031010401d040044210400c40300304455100c6840101c0c0305200c04141d00095120a07101460350000700703190f403210300b40c625000341c2c1e10041106918010101d002030044000d10304881e03010620700009620340d40241c3d44003d0441c0c1e028166801501c1324032405110b02842401001d170390409042480001130300d0b0341c441d0f04c04c0e00f0544041d03c0015042d000c00402c0c0c8501401048400026400d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 669444460 1250 669443210 669443213
    0x110304030c0617071d0420030108010506030a1e020a0518070e060a120f0902030703030e0108060d0b04021504170a26040303031109120109140f031e040b0313050d0c 72
    0x700c001080d00c4c0625180640c425284146c44682c003030700c0c101e901c0c2d25800e003600000e2482e08810754400d010b4000c0950030b26000c1005410002900d43d032880d80100d00d41140e0244032001c40d490741017450140d83c0a0740515000030b00d83c80e8003091f10180180c8280c1c041d03803803808400140080c030b010041f49008a401700100d030002036200440ca12050300d02100412201d00303d203013100c041c1104143c040d42c14001da0000008040e044030120140090a8807104442d54800082045003403081e50080c100224040014005103000365030803006d4040d030302a51703040940303400881094446181c041d10f60380d4400b140590070300021b540c4003403121205106001c0c0d080060080402d84c0d01907032000505064807a0000000d49059000b59440440c02604020452b10150a101d001c4d00b4902c0d01030b6800c6035078046103803800101103118500c81c510781004516188402c3d004000e49412130300482038001c8103205c0403840b54036540c001c6020f00703003c15448902d0600d50400e01e0030b101240e0421818081c03028203c00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 669445710 1250 669444460 669444467
    0x2100503190213030519030201060e0606160212240112120f020109082106030a03050412032a050708011802060a0e090403050c01060b0c031801110304030c061707 71
    0x10380a225000025881d1000c21241d0f200404180c1c10050140c05490003d4940a030207035880900760b400380e402402070315680d200d10000010240c1c2c205400401c20016004c20362500301c0300f0f29071b131803002e0102d00008003510400b60030038070380c2851901002c01000002d2405d48031640e000703006d0062040c81c000109403a0f65400c0c03a111201c00b01405005d05004600340780c41c000c3d4003112030b03a600001420b60351072149001a50341d480c13915004882840030710100d0850b00b000207040c000180d141e01c64500c1d083c141400104016001c0d9421010031a1080140c90842c181031038004000c111441d01c094100c0d810b1801d1424480690850b00e0182c4c03416009500c4603210000c40541070b60140c80d45036603486414401c80e00c0e4205100c0f580c0d0032441c02000d1004165001c801481e682d81c4aa00070070107a6154819519584261100b0b024242d00a00051110109090aa041f040014140803101100a00d48103013190010f030b10a9400f030107400c804200280d0013042222010200500ca1405483d0010001d03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 669446960 1250 669445710 669445741
    0x1081b030309040b0d12030c030606050c0a0803101805042f01200d02060103051b010e040b0307270501060903120c1b1211030c18280902100503 63
    0x1c900c0fa50320b5550428807074841406008216400040f4030a10039244140600602410903400000a181010014030f443c0308a05490700e101e80100904032120713250310351032800c0c1c00141001412905207080090200000d05900e03450480344500458545400e0401a41280800140d400b14525141c24014411080200070150003000d007403401c5008040c107080311080c2800300c4200090b10901002d07001450b00040c009040700d203d10300b103950032450b2080784000c062a0a40c214041b0702411000c00040c0740176080300460381d4001d0126890146e550500051242d00c1e46985910801502c61449000140d0b000d1107014051b14113011201500e940d90b40101e06102000c400300308001803c07001c0800c044000d41003c00100c080040e40004d85580441001e1422440c0c12100d440300d42c058448503060101c0c00e21120040142500c0041e14204016001d040e402041401840450768090403502c0c500c460f09580140d020a0000f50b0b40014414000e081041d5141d010502500703001300004d1201d80200c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 669448210 1250 669446960 669446977
    0x11b031b050a02030712181e0b0f090d080319060f05010c06060509070e0405160801030f1b060503010315090b070f11030a02061f080d1b170301081b0303 67
    0x2080d603901c4071840413419405840c5000702404560328408040961003585441952004001501c030a0358420700c0c0c2900c140164183c14219203168410098202c4203c007815610000001c0985420381280000b0208020140100c4007608048240f1801c5078011089081c1020590750420220b82042c01c01c0705410103034030440381000100400c50f002c2158541014008050280041c130340c0c5e080c0007801038164404a0901e5002d6440c2000183c2a001603040d04e00e040d1665445505440c0d0858494540c0da45400d4820f69020446100e030a211000e180c540000034039a559a054aa50440c505003180e40c6410244689245c01c0090340800704004080442d01300129040c0f50302d008409610a9a44914000e40b0b00f0a0b40000305040c0206600401c2c000d10580c0020402170107948032480001100c00d00f4003c245081d0f0000101c80b514038000e440b05201d07440300d9241c05071840c00e55a5820b0030200300012000f2a410003100411981c01d080040850340d07130200c00702800c1c0c00c0400d40802e41d240103d046 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 669449460 1250 669448210 669448217
    0x210a050f07030c060c03020d0e0c0a170312190e06040b0c0c07090f020909100807032306070906080c0a0c0b0a0e03030702010501060206070c080a080c1308011b031b 72
    0x403801c0425004002181480341c1c0702d8020b0100041444001d0025001940c1036940c16080c14003060700d00401260000040400030840382d0400d0625030001141c4000030603240c010300c800c001d00d0103400030038013000303200307000040c41d04c800c000c04500c401e001e90f60f080c0e400c08859072005040c000001c410403d486c1d4030425074824a515a540c85600ca85000516480b40c6540351a10f0441e0300889000d0300101a0400c042da180304803030300d510851841c1003515105070f11150b00030a105000180340c1c074018100513000003c82c5051200c81c0b000305410000c3c1640c503580820034400003001816007219860b0f5201c0794031500386040c582e030711401420850b00c600e0300501c0c000c40c0c3c5000524002c559449070300105000d00440c0c0d00d0b03103080074000e4002e082c00c0c000e001c0517100b401d00107160390340301e072411504e015804580b0310f080c03550100080e11084006000b003041c06005009141d01d40284a110030f0040c244030001040c8103d41008080440400300b00c0301d81013509040e14903821180202a1445048040c85c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 669450710 1250 669449460 669449467
    0xe010806060d060e06091b0f0d1401080d0f020c0d031103040b0a0809070e0103030c020d060e03030a1a09090a0f06060b03100602060a2a170702210a050f 67
    0x40001d0003849210038403445140b9016000c609054103481007407281d803050725868040e460320000d8400000c40c000100c4c2d400071041103007500244c01c21b40940800f4030b0800022941c0034803060064003000090308011256807041100503061075010380300340c5052080780060300002010b940440c0250116030000786c01e110394010440035100042040318020460203240303a8803503007140300040c4a44410340340c51815109820000c01c04010034011141220f9264030348100240c025428000d0f982010b2505031003881d0340b1000e419080070140015840382c026503030000b9001d82260420b03d0120301003406c103030160181004001c3d96881c002883c400e40c1b900f00c1e007a41440141458404080d003115042010340c1d00c1d01006011040140241c1c0e40b043c1c80e515001d4031702c2503482034240d0048820310051041d0f04400d0000c004082c1c06064420b0100380c402c3c2c90040c96041000311621442002582c0303c0d00180d209802d20000400ca201c04500030f00d42c40b400c800e00e0402c3d000300090403406807040b50400d596000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 669451960 1250 669450710 669450721
    0x1401151b050106080307140d0512041103060103030e1206040b310606030b220204230c04090c020604052107120905090604110f090105070f0501050103051203070e0108 73
    0x40c454005050340c440000e0080e10380700e80001e030720b030741098804403612200b817110402c0b422000310302051090010313543c4508041400c101d54002c1038001d030090b81d0380c0131800005502c1d52000d02046004c1d40c041e480784d00700c5994400921110400d0403000d40f4240d008a0300f07000009140a20381508041202c6080e03049400c031140031009070081051551710b01000c68100000c01c05580c00400407240161107424051741c50410758030701d1a1910b1419000c09080d400c4546c018079043e8000c012030744005d901a030200c64104c0361200166800c0d20354080d800300124003041403c4450060420360641072028090a0034135035503295480e400c09a400b6009209510100b01e004d05031030540390f00c1034000f00798900e9017a6445000c1c1010b0080d000b0103001c4c0406900244042c14540500b44403400703c005210f103090400704001d10903400904050341004020080030000c2860241041c98840c003410001034a9491454034a01e07140014607054009001841088000f54101015252009003800c144c95507a452 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 669453210 1250 669451960 669451997
    0xb0105190f0e07030621061a041d0709020c1002070618141509030901030f0213260a0c14031608011e060305071206140406020304020103140115 63
    0x8940210311000821000080c00b0039000960300d005402580303040000f640c0321140010301030101a4840b415542e18001c0400049503903100944035100315a40699102c5080d000909031a0180d0302403001c10100b40c0030348580b20b403e10100f0010b0845610441c50052440c00290311003407044e12184a4542c049600c60900100b608001d00c58170010031022507040940c500030581080a524004092040d0210f428809140752807060103501e03001d0040d0705102d500b8004402401d01c645040c0c2050381c0034450186e8146040009070068103a440d00203034140f803403107203410407499441408082a84040702030f4002c00c940250540546010030602e64918200c0ca0201c3e1030310103140601740118a080b44004bc5106041d40300304035400c42400c12100f94a80032040b0010760b0824080034010350480e000c2008142e103030044034950113100d104041050405206103403100074084400781c8172035400208102c115a414400c01d02d0b81c05549000d1078080d41011a0004004103081c0381e80103004400d084080c8031b510b0f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 669454460 1250 669453210 669453259
    0x621020405060706050a0e0a0507052e021507140d180210050315180106030b01110f030405130510030204020c030d050103050715230304080705240c070b0105 69
    0x5014210603658890f40c83c010000700300031595080d08a1820b40c1c56000c5001c00314002c110590070100034600b0314101000c0000c01003500f510605050000e0700c062a0780f4a80d07045503010000150058804802c204039603e084d0f0ba40100150100172401400012102081040da42062003040f000544600c0ba90565030b800040d58101a40c401040450322401c1a0f003c4020b40c42030090a0b01030319000c0950040c00503d254000098030408070000041c014203120303034010b090f40c0c40705140980080546040c4a81802d182c10140c58060b000000c3c00d200d64144039800088401c0488400c01540c900540d20a14880850000900c56500040c09038801e2100308207862000c0c000680402003035079a450b11a503928480e100e99807040c0920414650100d00904a560704084801d486502c2e5515404603020307070f82d100510407503c1032014064031020841c20031040ca240321506060f104600041a40050000401404215413802c20000c41d00020740e41d860060440f481680e00c40078020010410f81003081 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 669455710 1250 669454460 669454469
    0x4031704090f0e010f0605061603020a140a0b1501120c030209180603010b010219060c0909063503090d1509120e01050a080103080c010908040803071b06210204 70
    0xb41800c2c00203030100841c3e8000011142c0103402088480030681c5850b05541d0b09202c2d139a8042410b014014215900026490074240700388143d0b00042ca440d9a00c10301c202c400b01e145100c41d400840c01c10100850b428056401108088805402c21202000208400410f030940c070401d507121401c2810b0706000b40c0544406080c000c015500b6038141801103000a0003c0f25524401c0d07007002011402c40d4004101000300240c15100c002010340703039803203100c0504840f082e0103041103080b100001d1180f80602c03546001d440c41130070034134a00807240c07038205040300703c0d01e03d0301e0744080ea070100081101000000c68595440903928501e13003c03100d00300b07076400680d0001ca034415907060126110803c10f240c400800301c10651703280d9061594a001c01101c85000b08020040403400d0b100c0117002103812032000e00400001500085030b1405540e0b10b10700c003604198040381c441d0b840414118100f05801c24060100c0040410000c0c1e401d14004c0700074401107a40569010034220a822201c002560303404484c050b0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 669456960 1250 669455710 669455729
    0x50c0d090312050c120a0204030201050306060a090b07030309060b0f09152706030727020d0f1406010906050705060606030c16050c0f060307082e2c090304031704 71
    0xd140c5000741d04c01c2917005144a5420b85021400900e803419240300381c1d011359070103965290656827084180b04203548012b049805000c4070341e00000d10320f401e0000524006209a802041010541c41d001081d1010030005610803016040d208640f9103401c8202940200780c40c10710005400c0040c0440d00140c003648070140da040c5005404c0002c0208100d81c140502419411906841d5546000030b2088405400071044000038003400c98404015401503c95020015030001b44444101609404c4502c00004051040c8800301041850f6820503894801082d1504101345010120303901c082d02c441c4d0082c02d00d481101d01101044810170b81d02c040e00e02010702c00c500301c800740e000f605000d07550f0803840007040c2c1300d2400b000c52000c139424980c05980c040c0c6050344402e09252211414101c241c2e00781c207800718020481c0c900b1050940400c0e1401c0c1d00074208040f20fa2400104130b212480d000703000c02c02144400f1041c1c802c0c0300c214500002190700701c0342c0100900c00d03010341000641d40702e84615413100d00035 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 669458210 1250 669456960 669456971
    0x31e040c1703070f0609020a05120703020a08161707080f100c3002130b0904050705210a150e060109050307080a1104110f0705060a050c0d090312 64
    0x80054500c031150545100402403034030851a07003919640ca1040c10b200030480300d4008150b000240040d000018110710040662010607100c00c003250071800700d0010380c40a0b910440302041942864450711000d00280300207803044030702c0c00900c000c60140038410380b203004150030160000450140142c4014118020aa03180c0000a21201d07688039101c070202580e0f50b2500d40c120b04018082d485222140c2d0900c4116000422224102d0144507061000034483d503400700040460180460f01c6080508800c00840391140740e0582848115000200b10005221080090303103031030361004100c0c1e00c240c518070403030012942c1c801000c00c01a00020a01a4880c0d22051010400b249902a00c5128100030f07a1144a0340d99107204160740c40a19106100c46500314003070310b0300442c207250522622400050004119000c00100d0b828095124a80d0345481030008075142c41000000e010054000d2400c1c4802d124504088511919a100d02d60303025614070b0f59120700108041c000d00c1440c1000a020340200726 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 669459460 1250 669458210 669458213
    0x2f0a02060a0f030c0507021305090c1009030317010302031c03020708030717360c09010905060909011103150319140706021207021228230a08031e04 65
    0x40011012040b021070309014420b108144500103503444150010300783d001501000070603800800010f0030014043c05485c00c3c010003510b420603a00d4251202d6074600e000c1130301d10708009004410005102d505150740d0801040580e03000a0102e012111034020802d001c150001c00ba4001d200b0680e00420490000c400c000604e078021401c1c609031000e00c01884800e80e2004031900d1050311a082049100383d69925184081d200d0003464901c11000c60f044807100c1e00803200103070441c00309902090403180c03039034104400c608055510030b801000c48402400940700607411071f400e030b0100030716288136044184c047d02c509640802410391240e201c0d195031034071a1900d0400314814840c4910140c883e04c948a40000c0b01880011034035004c00310418698101240d1794200108500040074100d92446480d03101d44804044001d20043d482414070441030010701454030010303843c0900040c0311a6905139154402450000c2000c0848980c46103207107541c1d41c2e0300f070840d406a000003a809035070303042d10004000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 669460710 1250 669459460 669459467
    0x6050a0308090a0f0f0e07081003060b0604050a14190e06060901031107051c050403030207051c0c09020702010f08070e0112150803070506061c0615170a0c05012f0a02060a 75
    0x1e080c0c61021b40020005c0e1382c0e4400c260b07540c1c1c01c243e4007070a0801002c601040420902d503c0161800320041c5101e2804d0354440c00240c848100307405c07240004482a100e84400e1070031359450003c890620600910040c40c1c010300c1c4019a0005141e40d0107690006040f0324968403a5111242042600d07510a440301070740d0519a95071144107650041008644c2c901903403007030084064800700c0e980b50340102080d078204801d12090b469850800c0f00c8886d00d12501200160110700018050170045100603240c844a00005143d0740c8804d4444080c40555070030300403010382c0070320b0000d8144400e003064039085000150304070007041c010107181c105505801000c01c07400c002000404403e4060401c89100d5155a000c1060301c814401c20fa86940b058200c5490000328550090410f075140030344288246951594038542030814540c1e41d0040c1c1c0c00140c00e000c200180d507041100070344801c2c03801c8022600781e854000090301a03507580000841c0325520043d20386208201d1551443e034050103468030b5005510780039 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 669461960 1250 669460710 669460739
    0xf060806060307060915030218030604030f090b1c0b150a0c03030b040e0705120c150301052707030b03070902040b04030b1b180315100f050406050a0308090a0f 70
    0x748a4010404001240b0388182d00780003c1e651b500d010b191141c003070903000768000e6224000191285000e80b081030402e035020b010440c80b840c001d03283c144042e15644070051481da0160000d030b02c115014040851f10320141c0441c041050310500000841941000014000c0008410204050b50000640d404c03196805078007900390300d03c40e40b014008852240c0406c4191084130383d60042c60f9015240c10401c500e40100206007400c0d14070259038680a4a00100d4109002801400c0c2c0051001004120a0030500340004092000100311a040204818000340d442000b800c254200768844144d03907d19903042c00300c0801030120050440d03446607120201c21041c0c20500c000d07211000180001807c0000d240307080c4001d54443c00305980b070700b040e52049128807949481d9003074243c0300303c030000250803520101d241c0c00340c0d003c0f03034900c5400c038a48400003c041030340303411843c0940d003804810001916030001407015a50301c401000e4850114001083d00c02445911001c440068004001044c0703000c5240c8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 669463210 1250 669461960 669461971
    0x1217090c10090e071808060903030f060306150108060a09151e08150a0207020d050f0c1002030d050a0e060a09020103140c16020f030d080f100602030415030f060806 72
    0x19054454551070050b0b0300449a40324000e9000f21000c00a807666115403040d50036001400341ca4084640c035503c00a15100c8101d840d81c03031943c070000502114424400c1250b070b01010031401495107140a000e0300b0000001c03d501e10341403107035902c00b040c442d64503070718504007a00c030351942041100c0c4254008965040c1910a00203200c0c0400302854445102c2603000d815a803c110080c000469001e1061400c6a0700a1014981507404d020100050381c1c0c4885501d8500d006200900f034103a00314411506000051380814442c0c2c82880c01036008540101c2a030b0140d001e00c4200207816901d407885030b00a0094004080c40c02d0103008100715001c40980d02c0012618000c0c1c2e001c11402d2031058400081c100b0641d00f400c41d100041c026414085446c122810050744082c00d2415032034489008a0700c2d11400d483c950000c14010010844c18040403100a60b01c500001c400a030b8161800d10302a4076403107039004a81c180c03000c00010b4080a8044e403c12135056082d0300040120310382c0e80c1e90864550600350381 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 669464460 1250 669463210 669463219
    0x206340b060a080609071203020106090911130614090402030703140303100f0509010506160618050c031908180a0609240203090d15020c03041701050708041217090c 72
    0x1004550401c3c0010307050312601c650001040d01a040c0001090b00c03601c03201e4124215034a40c0000702d41c0c6100e60003410540c5204141054074640500f00300001000f240000d003860500d089802c0002c01c148100c008084003094840c10391907219400440e0a00c00320760009003110b410381840285a01c2c00000175407003800e002c03a100310300b241c841c04440380302e140e244201030b44010048014080c42c40c101d0000c0030840390010381140d58a400d90b403000140d804194010252003040d40b143c170700384002800b68690000701140a00352032030001c4550b6990b070140321005000c8102c0400d1803040b0400350f00c00c80d2262980100004a441e64a0750014254480381c06000142426955586002c080e04800226148025006941000401c02c1408a00801e55400351041c24180c501184040c1d00d5100030504110030b04007079a91f03a820451081880c00700344141141c541c1c5000c0c00c1082c1150701c10f14081e00598001e110703100c40e09006404540c240707801010b550a1041c820b0a010000e00006962001050181c8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 669465710 1250 669464460 669464479
    0x30f0912091e15121b050a030c080103150509031e030703180201090b0f0906041401020d090b0f0a050910030501091a0a14061309060f0b070206340b06 66
    0x840c0e640484160f2060340350034001d030104050003d0280360100001da41c1c0110009140483c0c16441c1d045080031800c030404124009504000154103008480c0002d05274208042503515503600c0b200c2c0c00d10002810442d0383d0382c4501088005d00306108446403042c980e40d14182c10690100d003c14070f588142c5a94000c20716044061803c031451380030040c0220340585030005070030f2409041105642c0814401c003101381080141650b950b072602c0140000e0070002c2d01d0010500410b0707001900c3c20f11020715074814841071041c00c101e081001d03000c54441400081100740c942c00e03400307020b1301c00c2e00400c100c0c41d500140e0301c00700190f0349901d5804141200c083d542c051007210080c01202e210310380c110206542004103010709001c035161358568409140c90240c241441c001d0000e03405444501907411410505031149001c208a4502685120183c41c80e100d983c0e14003862a400145144103480c07035119240308696003c02d061a00d0120179a00d14103181c14251101018908030058030022985c0902c51054035 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 669466960 1250 669465710 669465749
    0xa08181e0306070e010e04060e014401140a140106030b061206031c020601090f0b0a170703170c2b080c0403020d030306090e1b01030f091209 62
    0x51050884680d0054041c04140e01c850724201c0340e083c124614503050140c8080c02074503e403110303c0303604014030b1a6040340c0740a504203880c10071001c01101c80c244401c810826558210a60310000d00d10304a0bd84c0300c42c80c04580052821405030580e54150040b00d12440100803001c0f100390450f90420f42c01d4070012031076a803902c4040c1c00700c5030460300c0150004414000350214510612486812400c003c08440d01503510041040b4148080c201060058204100402c0303803074140d001c1c0c1401e01c1038018061010000e01d2020600e04510f41c4118444000c0c3d01d00f444c5543c46041c4858405950030481c00c510406201d81110542e9000e582c0c40b1215110300c0c0c445c10320718a02806801c400600e40b07103a2910610320342404455140e406000e62100b864200400401640c42c11110645503210752800314556180036013a03401c580110103510f180350803c10240c2e03180c201c225a4206004c1003400c0009440d126800c05c80010030000f178008001840d042c0051f0841500103079003a045412403941284c0400d1708 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 669468210 1250 669466960 669466999
    0x1212001030c02121b070f030f0c0e1513021606270206040b0f19030b040e032109010f0e03030a15080c040207030c0510150603090809040e0a0818 64
    0x3084500d949402c0305000418401496000301e44a000303000017246e0301c0715114a480c0d001c01a06074000c44005501030784403003c10841c2c0201000030240e040031003a03240351121000071921205c0c0925881901001c004210503030441d819100c400381280c56400440c030740e5192550081c424034085c090a48005030203400300c14814030960290b41d5001d0300c11400c0501d824040c103c4c90b00100c0c404417134200c0902c50001c00000401c2d203484440210365020a103070f016402804110b071490817201000d900101702c1c5420b2030183c1c46201e24510300380264806903a5945411600516603000348500650800d011410000000030103940100104181001300c0840d00e070701e03418058810700c180580750308460f0880440d807402d07a01a001c42d81c043d081c0000f203078890366903090403c00c100c0704240a541d590068480c0c11b941d0303c03038000043c0031981010400f0070b40311340f1a071449024003481c1500c0740f87c90704401c20942da814008200515031201d003164803078002c240c07400c035407100300310031103015440e02503510505255 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 669469460 1250 669468210 669468223
    0x60c150f010b13050d0206190306150503010303020a151e02030405070e010302010903031409060309030a0e0306060d0f0c052e0318030305060a0e070509120d0801212001030c02 77
    0x2d40550300b1100c61070013061201c01d00d040c4d070050b6030010003481815500804250341c4a000c021507580005c41a0038000c0310004d549580480c10100602400180002070300050801081500043c0b00c80300820071b1010103019000e046c00c001c2c01c00f241c1080e6015440100c0d0041d6000303a22800c20b95000342c2d100c00c015034101c0c0b800d11000c1e0010306414000c00119009042850340d00b00e921b0308180c0703008081000302d849640140c03118030041d4000030f10300c031905522100941c0d0800c03048010341418103140002074180b81d250b0720040c015449001e0704c1c008104074440200000c00300a8000380c0401502c1d0301d0590014480030040c003580c1602c400415801e4801c2c400c010f4905d203115034034941000c042d00c0c00c800500000301640c3d00711030b80d550040f501061003a49144070b0240755070f80302e0782d03201501c1c10310207100750010b90005c850b030084481288040e041404c441c10746204842c0700e11044044440e000207101c24030000b030411150344c031207490412150122001640820b88003441800d800d03a00413aa00d40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 669470710 1250 669469460 669469477
    0x207030e180c030703110301030812070201063516050111030c0a080a1214010821040603091703150f0316140d06020d02070b06060f0403080702060c150f010b 69
    0x114078000030301c91410a02c082d641011180c5400500d080c440344501050398001e800c1500c180b139000c113600801c03c042d00704940d488195031000380700203850310102e1165a48420300384840b510001107441031203003801940c14141070840088230704120180c0050086100b85000e040e0010b14170206419a400c800011142c0304040c00740240654821621210f86a03004165060204046602c0300610310b52035003e48101d00710240b000c2803070782d4900042ea5241522610304c1c205c0c0c0c41510745003d4540441d5106807400c0398a2405c0200d00e651040c5800c1e500000044070740d020150000c0140b00010600684202031040d0540b910222280d00004040c0c1d41c0300b07a200ca01c60640b08041c01401040545040361100c0e0501510780307020442d96a0b51142684c00003807030f00c1d441d954042041018800c018100755000401690481e181000d40756801426214078080500030200c0010010210345520b0220ba401202903401e407090b01c50096a80e061004045d104104003600e80b170300101d0031000d4041102c1c070b0203 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 669471960 1250 669470710 669470749
    0xd14030606070618030807020f0c0a210b24040b0303090103110c070815010b070312020310180c1101180201180e01060c140606010e090a06050a08010207030e 69
    0x5035190401c00826901a120446080d40c07140a02d000d100d041003501c4c1e016900c280c03684001442c1c08640246003410300341e0304041c181d000c1c941e000030503190110040280d4180c0c0c484000307c80d076440124200d80401d8200109044840020041c0342d002ca12090505000758001141d44082c14104020584190811855164004101c1840c482d07020754414400f54040c212320a0900300381804031b60030419203500554250f0814410101003460390f0034040d0240070410b1649003440016180204081c0d480038000600a5000020612100c852480d040041440000849112034007400382400f40440645141c0841e41e50701c8503420382601806480380d0808090842c060700003080d001100d0343c243e141c0e100454940c141802040c01c0090296460103030016480c0c3c010000710300d1400104550b0703000d902c5c0c0782c103400c14024055607a90204a240c000b240445090100b40c40d40d84409000701902d5001e0399001202001c0003a1130345040d0060320307445000341c90305411421100c0a0003401d844400031850b02 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 669473210 1250 669471960 669471967
    0x92e08060c0a17090111031806010819030807050c030f04050306151e150307020109020907110601060518030a060f14010312110708012f270f0901030b06030d14 70
    0x1c00030f1142103958445201c500100b0742c01030780c0e407600046034001c0c2c50300200411506035000815204000b50f0b030042034000024900000720400c004a83c4050100080410078a240469401d620500c1541c00c1c42051900743c0340d45100c10703e280001e81d4481e10070180680138010024100b8841c001103281b004902410b25050055235230701c4842d19001c0c00079a503901c80400ca20618a000300b65015501c41d600c40d4000183d01c02c01401004000da43c014041400c00c86988030510741c509001c01c49a0440d940c2d03061554030303404081322140300000c0040310242c15110f08140a000d20000b03401a038081c1c941d1000822440a00c0d43c030ba80c0d041c071003d01014004155000307020350480e10400c07151365001181c070309803209607072280c202e50300b0f4403000481c54040200c00c946011814400d851b42985081a0070340e0780d4070f4076408159501a40090007501640203280c01d4606074030703440e10031100c0340350b0500616981d810360b1a40b50a018800050314098002d10038500074112140c01481000b031000c14807481c2504 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 669474460 1250 669473210 669473237
    0xa0b0a03091a090c1c0803180111031005010f090b120709080c03030910030902150910030e19060e010c0201050406060504020a0507111f0807020c01020714092e08060c0a 74
    0x1c0d400c0e45035045a41700c1c000c0d440c4800c0840d5940d80034500a1001c44072156110200c03645190070341d6070110090381d08040406c240401d200100105400715242800c001c840903411036000d40701100c2552207100b5a07400018410400701840340c180e031043c40745488103404980c03200e0140ea5a107074004040c1d50583e20411240565242441c00c003802e03090700c1c0c41c02041c0d0300540c1d030110390850b1503a4400081e000700861240320038540405a41581c680605e820040f8640d282e9065503a862a9112000c1071174402c0d00007070600c00180c03c0b840600501c24001d0204c4542c00c50028024001107505541e51860030401007440e1600740200c4110070741c0d85c0e940324100441610381c01c40601e43d42c01155440b5503107920040c0c000202402511b000c01c20790700d40120b02c0c03424100280c108107000035520f04540018809008440800300c02d9040f034801a11040d00d40da4481c0200314411401c142c100d19102207161112840d004200d030280e040da003603c1d0566031640c40303252034001c10703010f901c12520124030042c04040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 669475710 1250 669474460 669474469
    0xe07170a0809121e0c0d0c03031d0405090703020909030a09170f0703031d09060a0b09120111041d070c0f06150f1a0c0a0209060a0b0a03091a090c 64
    0xb003100340241001121004440340d103140180600d600500d8551861080360030450601c2a8420407509070342d0150281669500e00c034200d00907010050901c10b00711403824482401050134800c0c850064001c10813810403200c51544c542891008902c40c9044030001012480044103540c0410607580f40c4140d071501b015038800f0108500121f59105214155041090980400403003000b0341c042c3c4c50700c9180003341c0b2140132040d03400c4c2e504280590010030502ca5a6120302110b841190340c06111142c6558002e40000c44561185030000316540c01e2083c40401100840c2c024800c56569420454218040400f111030341201225040b01141c1c3e102d1541010030b8036003490254444c483d00c2d000400c2070409480400c0c0c0e04064220403041c4481c0082442210407108072040255460b00209007071400501c2c045985900ea440000e008004900128081d0384446441c07102815420f80055100d0315a900c009005240b024400c4e9140c0c04401c00040c003800d0401121800340342c6540203045521040018803 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 669476960 1250 669475710 669475717
    0x816030b0c0f03040804050a080c240f03010806070206090d0e0f0414070306180204050604090e011107050a1e0b0a0c0e03010c0302070203060f0f011a1c0e07170a08 72
    0xc101070000c01104030324203420300c000e5126a1180b2800d82d103544c02d01c800d110318a80181c004002c294480640c101c85550782e90b804107030301c105a240f4a0582403400b014940715000e138003040b00311000d0110000c01c0c50940419000d1007030a0580c01c56100781d0342c01c014140ea4a030401c0b01c40c800310715025400d0b19203080402107070520180c040c00200e0520043c0408903500354040341c448001aa4584003407150050303c40d181c1040000456040d41040d0805001420a1065101d030404c034a5070703800c400ba03402100b0340286042441205d1042d46039030890410300d0b21419808403c84e2048080038403000403162000220300819001255403640799641c0309900c008040071a034550900110010141d10399600340151542c16440e980c000d40c680c40e181c41494a80f0710090010b001c15805d2004000c42ca49440030300a04413200c103c00c04207070b000d020504140510840a00345120043e80e540085420956046900c0c0703010b01000300d460740c1d540d031601003040300c546400f40e50554011190100c0400c1c101d1018 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 669478210 1250 669476960 669476971
    0xe0c09041b0807020f0609030405041d06090709060902030f0708130219030209160e011b05160e0906191d03040603060612051e040305070f06060f0816030b 68
    0x240030708664142040c1410300d160040c0000380b240d81001074107603042c07241800e203100380d100501070b03030401c400441e44900450040380d0203030b41c0c0d0750b4884031541100c004145c0c6042400040d81d42e142041c000701c0f91134140c6801036071455814034100103002c0c3c2aa00c2241e10400c1200c0080c0c41076110b00da0200d40650014140401e2240f03007405131805666520001d0349080300200c00b45408919600c1070005404006162040c4110305c0a800045160031404c490030f016001d18040a1502c00204070070a4001652005429482900134024804e20055905400c0c1c2e0f030070450651040d0707128150300380c0d034100403213a01c1c0354048003000444c1031400c160081c180010107440501500c40c2001e00c0641756030402e50000c8000380c2c42d0035040106540106014400d010143e00610252800d103824200324150440010018054240005d0a0610400c19a42860b0307000c1401c1003520080e05001014051500a40720106040980051400c0001811041030f4a85506a1014518580340d06d218402d00412 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 669479460 1250 669478210 669478219
    0x60a080408130e0a0f020705060c070302071a040501200709051005120d0f021209062104140606012604050a02061204170405031506030106080109030201140c040e0c09 73
    0x10340c01d8003000c0080b00c000586203007101c09030586800310110302a6a0b41e48003020040388100710b030002140000c90140d61040b264950560340d0704003403604070b10300702442e0311100c2242c1d00e1001a4400304088802802120826a100c0e03178110b440800e20b80000c4031034141030703607554400f550401120072030303820080e8001c941403894803001395a50007042c04041c00c15031556903500002482086140c0100d00f1010302e039030920040407034090305e40c455119489036804452040d44007082020002206100240140214101076456410949001c40c007185181840c1c00c0107003d4000083c0c8954814060b910312100f04c2c002d008411081d4060100c1c00350310240c0140c41c1c40c0a450300103030150303d80384010401214038058014051a15007000090401899421000c4030f20800c8200940c0d46e0006002c01940400e03181185070b40c0301c00c00082d0040289034803400f903550078403009070700f41070701035002200042c148400505203039210b88545080e44a40d0003841031141116012a90000b80240604000c410142 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 669480710 1250 669479460 669479467
    0x309130204051507061404050601030803061309050a0312051021080714010c021f0f06180218150708031f030b06010e030a02010e01031109150a1d060a080408 69
    0x20b010400c2c05502c0280e548070800006a41001c00c103841c0300300c031075150b070404402c5030a0525944254980c0340602c03005e4100300001c4081045c0350707500c0482000d0442003103000c200c7d21515140264550700303d100305601003218041010481c2c6854020148214042c0e1216481e00d418440c00c184500f401040c01064200000000c0c4006000c880041c0000c90040c0004c81c5240d1800113a00e003550740e004000421074103c00341c024811314000554640d90311b84180c012400803040850301009046a070700405050202640318208441c19a00400300c030341200c8031320707a00100c2c46000e0103c22019680b070350b202400308000d08008182940051074004c00e21503900141740d1038844c40e009800c51980c0080e0346050700c0c9000e01c40503680180c00c1e050325100540240c0341415a940001c0c0005030400b914030f0515440b00c400c940420780300012201403101c0209500c0220300100342c000dc03503400c41040c0c00041003d44050b400e20b114102804030350960300801c860b00d0308140003400c03295890080c0c01211910b2003403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 669481960 1250 669480710 669480719
    0x201060b040b1c0212040201110f060c0306010905010e0a05150d02070309090b030a030918091b050307051f030c12090f150e10020711030319020c09090309130204 71
    0x140300800c000c02c0841c102c0350302c5030303003809400c60480340301c1d260220303035a00c10442508030742c02d201c010340d50041e0242070408102074402c1010703044c2041c10603a41c1140c02607031704004032107441c4405140a0704003a07075a0011662a000192240144000e15983c0308005c003100b000f0a02c0d110191002078001024420b081c40c40380350245050345c1100c84118081b4244410501c415210341c8103150785403800710020301406682d6200034007014400c4c00303660b6034103041344982205c0c0002e6801200c0c100d40d01c079000c00321240b41045200b20b040060b000c0e9512900607104002102d141c0f0520442c422015144920900c240660099005103100b000b032005003c2e07881e029540014840c414100228002c22103070381440121f1500305203265494403034200061a041c06941e480d00b000590144a54001d01c00680c0c036445410981940040c080038190716100000f0070704a00c081c3d1440a60344d40c81240c084900042c184400c0060044d4222060599079009000c1045a8505640342c5408902c52131f04c01442c141d01c8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 669483210 1250 669481960 669481979
    0xa02040903020118030207030b0a0b060d09020a150e0a0e0408030c0a0207030b04060e010c0513061215030804150c1518080a17060a050a030b100e101517010510020106 73
    0x110100fa17015800a800c20030906c50140e1803241c0c000c140350002c02c0110134040000380c0380c1c000d90300701840311341d65602030710115107d041f8138a01410050703a05902d8500071201c020728080c4040d01080c003d00c05c4c1c01c00017440c5045910490300440d0720202c07080c1196a11440ca81040e0456481401148100540080410350000ba0140200d000305008070b8070000e01e00d0000c0c2034810a600c0c2408220003000080101c450072400c12054a0b010318080002c420007030014805400303201b41d0170010b40d103950b00c000304009843c0c00400445985200c07400b40c0300a07103501695001d41c8044049c2c181d6100341d04900080345075500039401c0d020224001d00503c81c0719101d244803034128a18000101d44821101d4800c2083c01c520380e680008200c400345c0e052424400403407160f001d40d2100410761019200800c5140c0d645103581800b070040290b60b4082c900d00358003400c00000103032144c0c210101c10024104c5038144a00f24555040790100342000240e4038250a0211206200814000b19540c03018049143c512 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 669484460 1250 669483210 669483251
    0x706050703050a1508060a15080616140909180a060516030b2409011b0326090c010503090c03160f08060106020705090c0c0d0305010f0b0702030a020409030201 70
    0x1040d41c0c00088900d040002d007400c0700e400c500c9044802107200d0042100075070020703010382c0c058104c0c80080f0700c00300d0300000924a02d4050300450a140518400c01400154030302c28158644150303078404100c0d42d041e107114441031240780c10790b0b50410b07004400100000c043c41010103000c1894011202042e4103515801d04484003075908003d00e20301d400c54095480c0c0d05000d00800c1d0b1000702c0c0c0312207200e0b070390b602c854041035129858410001c501056114180e8014040b071156034121600000c00780b035072807a0081100400c07030380d0703d181003055494080301e48909003000e910404000c801808245091001903449410040c90700105201700919007110303032014400108980c80e9403281c080c040b8203002403116048410b4005800f95804400100500c40c1d002440700c003140c0f0142c803455595110716428040f98440c0d2105030030207100b050010b00c002641540030314100d41c42c0300000d80705141c40d855061540e200380d03800654113034000c01e100405460306502030011f01e07101e03000008444a403a04000359540 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 669485710 1250 669484460 669484471
    0x301090609060f020c0303040f0c12080c100b01020312431b061a0d1103010c21020f070b070815030a0f030507020406230a12081e070605 60
    0x107803607852060810040707000b900107041001d041541048544540c0c4c960b68080240f0191140360316500170350a00210b032a4a03800b500e401045500d43c01c01c1800c2030305566000c60b11b0004203110f01403800c00e2902d281e20410b88070b200c050317000c0d62500054941040302854060460900c04d4011100b200c0400651f1034207484405010841c0f140410852031800000890b03014088140407280300d01d18100d205010b54a000198005000500107640c07008041d90100010324880d0400f180c0940323a020b04c03190074000c0240c0b030000c030001e02c284081000115201c0c1881401140395036440c810024040f107158001c5d14000c00056030050501d1450b807510030610340d083e640f18010490560a100b1108410031036031100f944160000c000c000d16640d2448407003c0340c190060200200481d80c0320441d600c40e00100d00411601c81c1240c0c008620ba80700c13001d41101c2944480c405c3c1e80c000c6002403c1071004410009060300f12581c0341c1065102c07820080820702107600d04045810800a0070001081480b4030307400780 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 669486960 1250 669485710 669485723
    0x6050a0801150f120b0a0f051008010b10083d18020c03070201050c0c04050108010c0e040501291c06030308091902280e091e07050d030905030109 64
    0x80c500a482800b904500b0341282891004a40040c4102c040602c0060091680100034102554a41d18608000e11050b0f201003d0b003803c040c2030040c0000703a088001705442491000700001040ca41c2000340b07510340300709000d01140702d180002d40c0b01c6050010f04424060740001c4c0c1da810202240c0001d06102411040d04d4030800034220a1102040b0780b50752004420401d141103140c03c20426000d42c3e28018808001c0c1001310000d4014a500402d200703101010101178402d00c19941c45007130f208d018245000d0404d0000700e500c48060040c2c5405d01507181210041104101b000380405440281900c149610144c160703010480003044144c002030810074040c80200000c0c001e411071030001d244c0740c4050418406907000509a580c42c11a0082c1d40344c2241e0704880310000000d2035030000c4042d140980c206060000c3d22380c800648441d800d4445c82c4156401019186040d140f03082d68015410380b00074680d84e56100a50034043c600b00a80c0500e0303e10b0280c145048250390306d00000c0d003920310006046908 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 669488210 1250 669486960 669486971
    0x9010b090c040e070504080718091401050a180308060d080702120f060a090812250e040c090807150c0c060201090201090803030603030d0213120b040510051905070306050a0801 77
    0x1824240c081c4140c102e0130b42c2c940395150903c2d01113603c0d95007805006000107070703041d03041741e900a4619501c03410030302d584402c0904070b14840419080c02401d04550381ea101034105407441e00003561030310303c030303140694191114000f9490302010300c06e820b444032030704490b061000c10140001d41e07100c07100400680d0300c000007016910303a48654582400400340c1304200035410000c100c0000b0702044291490280c081101003182d40d02c2c0e90000310310200034462070754041c07458400500780b558420250001e0000c10b507014032440480315802c4136503d1303452140d015aa00903000900c074800440c0344d00342c0351122505d0060034004081c0c641d101912155440880940e560349242401c40d40c100d00c11308000d08000d130145081d46000004642c882c49141602c40103181d0005841c00c840e5204c1800b0005044400c0e984942e11510f4070b03182c041d005c4103aa003a5260306c90701030441c54107045402a04d210302c44103000c034000c1c000c0e9980e09074040d103400f03800d8605042e103400c8045102d4562401c540c1c01006e03400c001080 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 669489460 1250 669488210 669488219
    0x10e010e0f070609270914030c06060604080a02131b030c08071e0509030708062a040303300c081603020f03070f0504030c0b1b010207050d050309010b090c04 69
    0x507100c10b40e800401070244282d01048114005031300d0118510000080520070428800824001d0218100083c2000040003990b01404400006003040d525008200c0380e490310354000f040010301592058100e164000c00090005040089103860700c4130790340e13601203a6500366499070b03800401c2d50300480002907514650103065580c04483d490f0046442e007412000c0902c0c0b9840003055442000001d0709000c0006503907083d40d1010040c42d002004504243d89032420685400c06501400d6096040305c9892200200724a106d40400c5504580d171507101c800780840040d01e510501c58420061120001c041010032114030202c0c0203503203440e1708a58960400b850164081070204100c01c1d0401e00701841400402482091b001c00c59420490904101c0c0304420740b0081111203201d01d400040c01040382e00c000140d80c0b05c4c410080d190110341c1d0902013044020500c00d440c200d008062002c2c105a00c00f12103002020701a01c01503410065500021070716200030f07804221400d20540707060f1101c1c64005420407 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 669490710 1250 669489460 669489463
    0x30312010e060a241404050301020f120601020d0918020c0307030c1e020f0607060908040801050103032a03080606162a06080718120f031202040b0714010e010e0f 71
    0x401814010103135010100e1940505050701004207812070501c5440f4111203903594580c0159001800010000c0d552103020002106954202c019a40e614001c0c0070049540d9600215000115400f5641c80c0b201c040c2c50004048a03843c02201c84000b400d03400c100000e81d42805000410b40f140c02901d07003100d0441c4601d000076010701c8021144000c400340084100047e40c070003180401e000b83c00c0f5221f0740c9455044c10704400500030100002c02090000a001030301d5030301034100c14122400f0780c86040204802c0141d408001e444240e260928444500d012000039004551580d00000b010740b44904000c0044050005c2c468035403410754008030000d032010b8039600b00401c091544546100704001103440e00030054030400c3c028002009001107041a8221107031204070309001042a4140d09224854505200f403240b80991410b0f00042e0310b1241e810f505d102d1070700032102120501050289071600644a0784006008006c07441aa0754807240e84c1c107107481d000d010301707039206407103801911218403d6096207 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 669491960 1250 669490710 669490729
    0x170a0905010509060f0306062101030b0907030b01050618030106091a030309210109062c06060307090e030c0a1109070318030e030c090108010c02010e0105040f11030312010e06 77
    0x32410007004100891043d16108143c4114100d841e010b591651a17510002d411401110722083c249140403c00031303d40655011010b040320701400b40700c0e501c0d4840645403a2200480d0102520f00740000004205a0030a480140100da042496001407004507000207400c0d00c5442d40040b24807038031707408054088041118a0481e401d0110021403801c1c2c0d000011885020542d240020340b0050b6a620540079a020f41096668961200041000d505480c4410300700a8111141c030100f0724443c4048102c0c10381c00a8000d02540b4001c0c010442c2a00c1c0542c403001601d00108641018001400040c44401c010460300502c3c80c820303104520f1031400002070024144c1c0c01460501003600b0a11443c0da010224040d10f113440d0f030140741155000700c6600200e407030910003102c129000703102c0d20000105408194011f40070355034503900034803000001d44e80303007401d03518145c60181c081c1c92288201c10018140105680b41c507030b009803c3d242400841c51400c040b0b0b020991060000c006c109042000510f41031624 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 669493210 1250 669491960 669491969
    0x4020d020d2307030b01140d151d0f0601030803060102073c290c0a060506030706230304060b0907020309090a18121407050304050a0f0302030d030f0603170a09 70
    0x28122540b0350303162a8401c0c5c00601c0354642041c0381e40e0142072103803103a101d0303d2005904034180c60030801509103000d00500101111040710311140b60714014551000c11a4410b01104200400721642561a0242c0340e50001d400641984154040011403c1040407182c02a140e01c6401d8021130084003190f4120700607007890b942d030210301c0c2c5d01c0501a800400300c446e85440c0140086800c1c0d10616240c00c0c3d44c07403291030302e17490440c41500040403c0040f1504100c0c455101501540d85580c0d46100c20b480c840c0c140d071091070b032181144100b00360031040300c1c014540c800d02030070700468444464400704c0c801220a440100050304009040c0b1201c0c18042d103c0c517040070508108021809010000010340c80540b0710040c030280c0907544203c1103d200b034280c1d141520803950303404d945440c50b24000341da95000784596801401148030000b0000069421501140e40103800b0b40f4901d807840d60203d004100b455600c222555940c034010020801c4005070303e40c07035441c00072425a03d08154001402e903e0042e0300 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 669494460 1250 669493210 669493213
    0x2913030b010e06060a120c030908070b04031e05070b190507050409050f10050f010c06050112060e030f03040b090a050d0306030302010f0509100908070b0408030417030601090e04020d020d23 83
    0x20b142e00c0e01b40e11052402d5404450900000c07c621202000c0f8050192041c025224203404541c040a11030302000440c0594400d48501c03259500016060640601c03907022000402c2040c0700d101c0101d95070700e0490303500201000c5840a843d143c0351060046420a9844a00280300403c0501965000d80b140d0384e0403042c40c4014000524244603001003030017040c082c0c14001c0300d43c0d52900315964011041501190740c00304047c0610360f12182c0b000028603040304280c4601e03007454a40104148044100d480d02c01100c00050b1842d80e480e140e0310301c82000548a0100c0b0310509040790040f420510001e46080141e95011039824991308000f82580d50020300e403111146408280308481c50005030482e41c00c806560003281d5100c6d103003002440360103207403000b40006232200100800c01c06c905004600c100e114414070700b80a0302f01c0c0602c005500084807001d0100e41081414064042c00200c0c1c0c590084c030040140c180d124803079011880c8030b241450704981041c1004c0311505140070803800106290309680 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 669495710 1250 669494460 669494467
    0x510050610210c0e0310090506070806150d1515080619050a080f060c16021e040f060503011a061b070b0f07020405102913030b010e0606 60
    0x10008194490410420303042c800040c1d10042242041d9810600c0c1c080c0c0c10740104403a030b0000314003505500c4210a018824041d041d01c0c14400f40d40352043c030341c4140d00328004042e5691030b850103460303440c00504041e0b070000d6114001c03200f0980d0b203002403034001c4580340c002c1140340010cc074840786c6602a400030001d402c50f580d4101c191070741c05100d803580902c044601e0031f00114000241c00304d05100b600000d4000c540040d0204070360703800007010107003207590404913219543e030303d9200307c598007030b442a1420500117010a4030152404402a4519a1061074481e0003401c16000183c116481990080005c41d140c0c03100300301e54903007841241c0a00c0502c1d40600070310171a0400041103440b50040c3c0b604041c00f00300400700000d0b42000040d02600300700040542d5120501c002c0c48950b04290000c1b8410360400001070001e608030340c8110100c514020004031841c0c0149141001146d05c070b4142c40f414001403101400c3c10785003100480046001760107540c0254141071280000e940c00400c043d01401040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 669496960 1250 669495710 669495721
    0x20702010810030822152d0f030b0301021303060b0a0602060601020c0603041a01060c0b010b13060e03010908040b0c06150a0620060c0a030b150d02090406090509010603051005 77
    0x4040f200e900e00c0700410074040025076072001070303d598a5082400721461400031b44050b035400a241107028030090711700101090070840e641c0000d080b148098030000d0405800d00e4078030b0b8041e070400208904d00078005401c1080c0d41031654480b442a502c250b44d0340740c031000384c0007da00306800c400010300060b1001c0d000134901400080e607030380250030059002d0000000040d05004030780c0c517581d6001c50894038650070765039920001440e80d00050780544502e0114000000e6006840040321024014800f410708200d150000a842070502810442d405548a510410000300703070900074006402030320461501c070145843d943d8035040000b00581e00105c00c04080c0ea4040e600c002e10342d000c0340d0881c50080c01d040742240d180f041b0000e4501c2842d0b075602c9070074244001c042884000e00403150050350208a152405010000454080701c0c441e02c506504000501c05496603400403c000c2001420110315a43d80f8011041102d90880e250801a50b464070180200882441031040b010701703038641440b66050a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 669498210 1250 669496960 669496973
    0x90b03151906080a120f1106060409060b0a090c020106081f2007061a0609210f1603030e241c02070605090c010507110f01111002070201081003 63
    0x74280380c107400349071158040100701a4100300042c1c500703601a5012581c09103840e844101c0c0c00401c85000c90401c90140328800d00c1043d600a854008000030141515040280b1009042100060314016121a10041c0b152a0a044580101141c4200140c1115000002801c4440c0c6404c6000d03103400c2000c6540038072a0001d200c0700c4003d180480081c1c0c0350000401a0070440c00201c10050307820010507004203002256205401e04054001807030b40101d0903008114843c4110311072035a0010391003036820040322884115951400d8104104c4e4176408850340d07200d04d40a9a5090402e400034400c10600070980d0142d00303100c50321403d80e01d90b00c1c40c0309880101f0856140042c003010862001080400f4165680d0842c10384569044031304559805042c1480006404122511b03005445000800e200d25442401181c40b502d400c074071024031203a40e0b002000040b50468848030704101a0f0b00b0360820340c5806000d1860b80d0341c1104001a0b40313004a20015003402002401c483c08065040350810110b042d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 669499460 1250 669498210 669498253
    0x9010216060b010c05060c130f03030206070804112806080c0f0706110c0a0204060501020607020c010309051006060206071e0e0f04091202010b03120301050a0e0903041e090b03 77
    0x3401070010812078403003001244c606144c0440601281b161001348000000317100020101d0380040700c1c1061810340c8070300002e16a42c03010703c0000c005030300c07031000100300c0e80c40f61080710340061203807541d4403001d4002e9002800703c1e000101d07000c680c06540d00100c09240030340c1e0000c0b00100021304140342c1c285407601084140d03008040d050700c0d07802c03400a010010040180e00943c0d1001c042c01940d078451503500b80c44c69442020b01d200700d0066141c030340d0114456000080403841140e0b030f540104400250100110081c1104100c22541da12442c01642d030005070720b0240300041e1089900500700351601410082100d803c0b0300d4000c042402074591076070460390003c02045c07018026103505084080c00d2000c10700502c0300c80c0001e010140e4000820f4192039040d001b2004a003070440442d0701d14000c0525040d8035100a108050740610592400c01c08001d07225185d0340e0011400b0107590400d996101409100300101e1001d00c4c400b0f00071030040c0729201340b6104003884904240d0040c200b010040d0141d0b0b41924 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 669500710 1250 669499460 669499463
    0x50a1b0b16020f0706030606080a09240b0414060901210602092709071e150203120921030708010e061203130620060114120f0a03020609010216 63
    0x28101000a030242c0c000c0000c0d8420004650484140540e0380710f0007802061540103250002e07248901045452400340500d2a0091704040c891100745002d40004401d540e08185040003507031140e650b0201c0741c1d5144207020441c4400c680ca0103052034000e0400030b400105030420400500601080101618282e02c51440701d0340c03041005964206010021b10400700c0c80c3c1400c10010300803c2040c00303102e9030341e20a50040d8a03180484000d952115001a601081c0c80300324841000c14042c100018506900301d901c0240c064010791346030000240d1f075452644001c945924491384030000c2c145034980104141c0d003603c0180e0b0701c26030841c1401c101c01484000180318000c2d0200048011400580d10107102228507005c04007103c0c0e42d034075580b4000d0802a510b2049002003a4a070b11400b481500c201610311282d80240050090f580c20940e10180520643e4600e0790400c00d05600f01c2c0030008200718034080140d241d40104000340392460020300d0218001d0078071441da40144011905414500300208006 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 669501960 1250 669500710 669500731
    0x16050c0a060504020d2a0b04060c080a0306031a01050f01050702030a020d0c0816050f01020f150a060504020703032a0e060702060d050c04090e0a020d060515060a050a1b0b 75
    0x151039134000240d001d588030102a242144906800c10b10502010030b0041860400c445482e085d0754413140003000b40103034811040812804c0c0c252400080c40c0c000180401010344c100001d041ea100c0d100d10b80700390110b142202401404400500c2207281480040d04429401d1070020319100640e03010a48501321013900034069a81400803604200d44002442c001e0148901290b00300640b10505004110f0a44142e501541e048220b02c8480c0d48041208001103442400410f02109040e0a07010540c10041010410540e10503020032940d07610700040903000d00a40d00400c1000342c0c107012070000414419070901480424200ca00c2c0142c2003940b01544000440e800e503220406800480e08501c1503d80d50000b44c1e241c5010040103e132003e002e0415206210320030010a1285801255141074000001c0e60001c0a40d41e03450000b0f041e50002a4401560f030184808100d07400301049642e0001445403010900100d07070419072a51002e000111000364819014102d01191030309450160003500e40b0403007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 669503210 1250 669501960 669501971
    0x4051e121603032009040501050a121e050d091806030b2404050906010e0703060b090d03020f12030a0e1b06370f110c130b04050f16050c0a06 62
    0x14540664046158501e1048145004c2d007403145100301c542d8050414207100340d181c50008511800c282021400741c80000401c0101565143c581d0349407260600a00010030700c4a0751b05900195091184000144003600c3d01040d0303a003040f488540c881c09020003048224035007142000480c959000c2281c2010015800740a400018200b007001071580843c15a080380c100028003c208134000340e458100d40403090921015100c0c3e1600310f01307036642882040d07203580041c850401c040c03a00c0340444072094442d0040f40c000301110070446040003e084848250401c0c04410414410140c1c000c00c0325080003100a42019644010083e03400e40d1440c0c42c00d4003406012a100280140660070b480260200f910485901c000380c065a014621160342c4440002e20800b200d00c90250203400c210449042c074070003505001050b40c082c01506070a440e01d20101a49814160000c0d8403a481814042c69100240540a01c0c0170061128103480c5840b00e60100b0402700718480c0155800302d40320900591229000c40c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 669504460 1250 669503210 669503213
    0xa1526210703171015091706040b01060c05061f090e100b12102c0109020f0607020904120504150c050d0905010503040620030a0b0910060504030212011404051e1216 72
    0x40007403054010300d850007d40130f035015445000140c2c10340300714841d101c0f2042a17030326118112640c0501c400010b002da8003c4012038405044006481c61900d04a5407412850341d99440c47d40a40c0c000b0b580c58145504065a0651043c19a014200540300d007540c000801080800d0280e80d03441004050718905582c611341c3c8184050381e40c00350b65003040e0406144019114540042d40208580c1000700e1144500d003844410504002c020784030f5040e0010114200c0755034685070014a00f0302140c1c2c2c4000c1180400c400b050034000c2105504100800ba96190403503913651070041c1c80e01d03801a4201c0c05100341c040302002682e901c4021a07500650210001c9051101c4903d40030401c1c01e0044d00b16441c240200401c4000165944102c000440032034640003583c03038420554220038403a01601d00000c4040200b803000d8180220740e0040f02d8808800000c07c010313010100c05101e070003900c0842d0103801042c1c80d00c03012110806100079001c40c80010303101e01d00401032100018451054920711000403000d10301c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 669505710 1250 669504460 669504467
    0x418150801090b070201050604060b0405010f0309140a0201090b1e18060d0b040f1505060a0e090c03070f2a030e0307030b0a1526210703171015 63
    0x1000290020b2181494502d00ba05220b841180e08000641c40d100c0001d00e103103081d00030303c81165007104909107080d040a00448606040b42000c40c217041c1ca41704c240000455240300c05c03c1d02044940a031a902e103440c4001401164907a00c20a60340380c0901220782d441d02c04e00c08a480a500c0001c0495880d4012071b0002e400b041000c0150b680a42c010841200e0300d041904080c01c13070f440442d820081c1c4013050389030320204d0303884034440090321303030080000c0c452401c1c900b0041c80c001d00c15003085144000d4201c006039495204a40e03000c2c241c0340100900000c5504000200c90419036810b0051881c14003a20034117078104180a4104981c041c0100c540908d070161039010542c26004e0150380c004ea44a08011291a600781c601070301491030064401d07c180c7d11941c0303d205440c810810034183da030441820070180c000420f80200700c0d005000030f070454002e08100c1c44040d020501d12041e15500c0da42405842c0718032040039401116041010400030000200080040d02d022204100140c40f407001c045 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 669506960 1250 669505710 669505751
    0x20a0b13140a0504051e01090b10020a0b0f071809091727010c1401090210090503100f060503031818072f01020d0f0506190308090d0206030c0d0b03030418 68
    0x6d4050410010001c0303015203040d003154100c40030540740304080810710401240d6034130410303002600341d0001101242c1ca940190380e6590304054107140400c0641c0130001d2a440c6e002c0c80750f0220515950310300e1001c04001c6594419512540250303c400d0906d0000805000c1c6802e01451040b10880242260b0750281c0c0580c0884c42d5540d005626000c06550560402d4020a4806401d9120321621602e003042d06d84a0840001550f4014000d000204103003c0c50310007408030981940051901d03030070040390f103031000c1018060041c9098400741e0009411410b21030f9080604102c048400d0100081200c7e403074204c524a81e030300881c521070851030420003200103c0c840f1415110307a640c0d40002101110769405800401c4240d480c0e274000c0045407240000c002161094503c1c80c042000074040400118602101900d01e0300c0010700b0b540ba1044207036000485952044460107407a0b8004900030034940c209120312040e201c030a50040d85054100041000d1008050b00494051503c80000788915403010710a03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 669508210 1250 669506960 669507001
    0x1e040b07031409060609010b040b04050607050a050d020307150c171f080a02031b0306070c050709050124170610110307030503040b090607050d0c0309020a0b13140a050405 75
    0x42d107664242004000d0700da82e01a6411845060900c00204400e41c039982210300b1207017840d80c1986800d1410051107042d40100707000751102d028441c0144003041d03040c000c064440c50994051650343c012458100100c1c681034600f1148181b5006921100c1604400150410b00c2d00200f40c05155940e104242c0d41801085408134083d502e124000a00302d1001840880e41c1c0e100b1003d80b1400740c04003058000e292101a056540b6611140110b00540d010788a0700d59101e0080c81a103148940b81c0c51402d05489080c2e10038010320030204410311035030042000e40896001035142085134029101500e40c0b85401c090000b5125a070f0031080320305501e014192601d00400c3c0b10094a8541c061410090056041100d05440b8000c20178001021141c02140301131103015a502d62781d007440410b249802c0140108103800080c140d9564940d00540c1d5003490510080003c111410f0740e840a1038005a4401000c1d808001160003010801040e5510b034541c0c042a82c00070380340058640e403500b4403003c000b120b068030f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 669509460 1250 669508210 669508241
    0x10e0607120f1713170d020a02160e040c0b0306030703020a090906150b04060518060339041406120c040812030c2205130609051e040b0703 61
    0x400301c0141d0308054032000c1d00c0042d85802980707503443d0340050140502203d41d403940120400381100010062070920407404a400743c2c0500f444c03c14000c51040342d00c001900d00169001a0040017001042c925040c0540030440076060700b0f041070343d1507070b40c105224003500c2c20407500400099041e450420040c001182c00500d42c2d03110780d90712005800204007d2a0640300c20742085600d0140301551515001114540c1245526040c606101110641c01500907000d01d00300300b2860514954450005c0e40c05012107107040c2c043c2007150509010198800c0c11400d524801c8400c1203801860301d142500e04031800c0e00d0ac0c07020018800340000d05039114000f00b44003c55200e41c240020840c6402c0a041600e00041c114dc5c2c40125007507621000c0d00084420650070f020801584c00340900605800c013980c0c0d058000b445029450f1000998590382151821503400d41e103180030008031016000c1d40c2c0c0c2107101100c00301c0780c45407900fa1480040d940140701900120054002c248101c0c401d03400390580502c05030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 669510710 1250 669509460 669509483
    0x9150e06190e1302160b07020106030c240207050d03050d09050102120a0f02040b180a05060406020a0318140d0503090901030b0414010e1c0215040506061e0306010302010e0607 77
    0x81d01901d914001c4030740c5401042150000200360005100711207520902c0c080b03400004505558008075500010820001c6540314040000068101000708000d025040d603002040400301401c41d80e10b045c6034103184110342c8801c504012a465882400d0700b840d0701803820b50364510f1001c103001e010b4003100030f00a10303030b61001403a0200381c0703c00740101c0c0c055111907206108840c41222100183d002c3c50041000b0301c5400c02908041e604900010058500042d003001c03003480d50313940086c0c0d4a801550254000d030b00201c82e8203040550010f03100d200b421082e0040041981070454001d001040f11034110f00458005448000740700b010001d440c0701e2403008003681c80300c0d030b1285007281000d070050320100c4142ca41041021180c44040c0601030400540703200410340c020310525a026406102104401903000705408009400300325115144658003a200400607401c002d42030001c884c10301a0b8000050030040c3d903151069501140640c112602407030005c0390f01401c3c0703000422511800d64003c24162103074 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 669511960 1250 669510710 669510757
    0x1202060c07120512030103034d0c0411160c08030d0207060e01020a1d06160b07140301120b2805010f06050408120a110609070509010609150e06 63
    0x782e065003498800c1040d42d24501510700010030301d0200303000003030110b4508040e00c482c0c01c0c080b11100c441c007000e090340800c10710208007903000f0100420000d88006409032520107140401001644a641c400b81e50400520031400f82c82900c0b4010070844480c5803461030040c0c010b101d000c110b00c60280040b14280c030754810001d080d41000f944250012a0b99604240d0b40790080740c0c0620131750320300d10080d4841d580141c103481c0060078003890700c0c02d02c2a4004000d00040341c01180c0c0b144d07080d402d41d215102c400228140890081c00142200c6002410003c0401c0180801d100c108040007240c1e90000c111040350b2111200520052030710105503d10400c80207a070310003178900e904014121240031a0329003400b9183c4d4800c480718415401000e40f940e000c1c621030032010a00100402d00c1611314135000141014074001e0509022041c1c4010b001a44001003e1100d80742c0940c07120b004020350b01b800400c0501c1d160104c6543c07070480400780b0500c00606c22504850701c81d031003207070341c4518051103840004000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 669513210 1250 669511960 669511979
    0x21507021203030a39110115170703120f020c0d030c170301050a050f03010b04153b060a0305060106090e0c0a02191407150e04090c1202060c07 63
    0x1c450500d4400c0c00d0070749601100600c02c403170f01c0161200c4c3c00c0e0399081800c9200141094109034842c01d00b007101440340b0750300066007032140c0b185a95007010015410307490514043d8104550183c80c0b55542c20505007040081c3e205015400d03004503500f80701c1580d43c02c80006900340010030102c00d401c56481504803003015802400780c80c2c82807040c81174820101c10010042e030980402d02407190401c00c55001800076240c095080600000b0081c001709507400c1c071001040a664944100178040404240140044202441c460f105044041c180e00308514500310703107080c91011400c41c40100d80040011400703a4580300088005942c0040c102c07006540c0d1614000c1100b500b0f80300e080c001024541c04035050141c010102d68814160b81c2c01402d1840c0e010751049900c00c410001141c862a001e001503036464010700440000307080c58958021161026000038003244e1042c03199070312852400400c030000511520203041581d004403990602e402c011310200e207991240d04004501440b0340c500c0001d12602 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 669514460 1250 669513210 669513217
    0x6030c091404154502030d03020d060807030c050328060b0112050c0c0d0801030506041b09060b0702041d15150402032412072106050f01030b090d0507021507021203 72
    0x22014070056184032482e01d003425000110096058211460400c0340ca44039401900c1d080c001e0ae100000d42d02da50741c407c28601582c1d5071045407403900c506806c10880c07400b1b1110311030204a03900e10400e00541520312a5074240300c408001c014a98600c40000307282d116010b240b0300341580040811071401c01090034001a081000750031811701c00c5c680c9240b01d25101c2d24595040325848002001240c80700d6464030401081c034841d10b001c000d0f400100040c10802030062070024150052030991b14030307140c01400103940540f0300e0260b0860910040792416000000c007112016024004091241c607074441a10307142990941c1d5a6102d400441841190010440c1051003a1000310200e11030642110034081c407003c0d00340c0d03d00190340244400708a04044c50046000c009124a400260058203070303070b52021a00c0944102081c240e507034005004024044000c0d80c8c014580c40014400e115082c01c0c0201148585078000340100c4420100f000c00510000a844074294000d000c45e081183d004202e595980 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 669515710 1250 669514460 669514541
    0x1003091203200c030f0d0b030616031503121d04110414190303110705060403050d0e03011506030908090a0b1801090e0c03101806030c09140415 63
    0x40c80e000c00d0b500d0400c008085800080c1000e000e5414244410342c05e50f01900702c0065031010741d49540c02c002245ea418007080c1e1086050003d0340701c20780012440201103500850800405a03039400003800442c101c81d035100304d00b9122740340000141100d03c00344403010564494594101d810519070102603203c04001e401035400d50f80b2107111131205e060410040c10401c402084070031401303080500c04a88034422420042145400b110a00f564610100d1141d90003a8001d5940d030f00608907020400b540440007592000c02200203010754601020252140d4025208034010702d6034030a1643d04011128040d41d501203001460312071480e540e1100000a90b010603c0059021542503441c480e560007002d44405039140c8031102c014035600c00454080130380c4060f200c0911034410b0b40d800201c05055101d4560a104009000300f401e80c40c624080c0320f20070043d00302c002074600300f00d4440e0100341c0800780d10740c1c403a07000301c490018a0003400e8410001d0099840d07510005a100c11030110250710285440c00e0340 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 669516960 1250 669515710 669515741
    0xf1d010e0105070804080a14030c07261b0c0a0e09071a03072a060b1017130c03060501090b0f1807053708010b03151003091203 56
    0x101140d0340d01400c81c1c0702100c1c400040f0310808082804103407488094192601e1505007402c0c81c0350481e000301c08940048441d240e030103030001084000c120414200e03c41c04070f6099981030f000c4446142000682c01554201e14800440200c800c43c0d2520070043d01004120160510190342e4131000c41903090707078003250401c08901c00e214001071450f10320440e01c1d4503106044503807825511445411203002d14516101c61181d10404d4240c06050320005800d80100c1c4542c0000955a2180c002c0c0042030f10380000f403005000702140b910f41040e200b01c1d1440d600982066510030201200c0c98043c0e1028440d400140070305142c04000b16401c0e0060b4400818075504a4884845110100c1007101d01c4c111364411460000040c808135401d24002d402603c16a408960302c12194840c621460807441c00c2511011f9154020150030442c0c150018089405060004402c900d54900310403c02c82c2c0ca01804000e600903190038030204036051107584901251075010082c00c169400d940c1d40103010b0800f40c8a00b0812 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 669518210 1250 669516960 669516971
    0x6030c091a0d030207140112020c01060303081b04090509190303061a0906090d1104020a08010914061e010309060509030c0c01110703060b1309080a0e0a05010e060307030f1d01 77
    0xd0710300300c0c2d1482812a45540100b45060070301c200401a0b41d80b001515050064101038040d4058203030000d403261282c10000000d5003491420014130b402c001030014880307290400ba0482101d49030200b224280d4210307240115080d22130403142460689001d034140c48225400382d80e1030400d0b0f41a00b00c04200d43e49142030740d1800480d00e02540f554407801c20b205034061020005140c1a050424074120640c0c082c180c0455091469000b003000e9034001e004410000d02660300500100b01148101100610710344030005451400c01c2c04501103c441540d540c404d004c1c0c00341e0042140e072003900300100659108800707209c24200782c4881d9660750000701d8480c50500840c070802486510a4581003009006074000b0089d103850341d00c585008141c00d003159604000340c28094842a070140c0503600740140319807c0c00d940d80445030f20081850140c000e105108440a02d01081243e81c84101039003403100c122005541e070384071081d05400800190215440c91800c00383c4030040442910700c1c8a0804a07400300a025 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 669519460 1250 669518210 669518261
    0xb032a03060d030e0f03010216021e1c1b0306050f070206041e0302030717040608090604080703050d1805060a060e101208160f0212010903020c010806030106030c09 72
    0x5850204407101500040302c000814042803040a00c0421504041c000d000c0e5050400c0200e4266440150060881c42065000c0800c606000304580c124504107502c08009041c150000307203001644034156541c1a4000300c1c0c02041c414a80018100070300324112201c4140d41c0d80c588080540400c40d001c0010100301070000340d0140c008260380b0311940d4041e15108a451a088003c110b1404e10324007641184810b0000f40c001508042c1c1aa0034400c5540b117003030f2140d217801c20081c40305000518091254020409100018050704151040303d580b50030302988480e04040309034000c1c8101c03a00c20004030b298102d140e0038010b02241c55400307011031600c00d20021b80c50b00c0b5100c9400304162892441000c10074020407070490a0110000958070a240c101d03e420150b5030706c5140c146044e40195103c0d2074030b0f2591002c42c58080d01c20b000500c00d03900284401e05450300e02a40b24449a611681881036071703c0082c840d50780a41c814409140e000000403005501c9032a40300050184203451500303250f12584188 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 669520710 1250 669519460 669519541
    0x1e0307200601060e0910170f010e0c03010c0c03080406050c07020402070b07030c0302040e06190f08010204150c150e100908120a0618021e030703020c1506060d050408040b03 76
    0x41c8510100c41d4007246e00b0f403610010691102071010a10028024410311900440d02030240480c03400b041001400002100e034101421113054066030340c2407000040b035610001e070300204010390094100d0000513142e6650650301d18103115543c0c000354020710002e1010700700444600914040c103001c1e40c1c100041003800009808030301c80e5008980c050ba0554002801d503260a940200c81a003002c604002042d03503454042e03000c404290411100c5035008a0140030380c3d458207803003000303c205510780880c00c00c1090716032155a4602d0b00e90301ea031540e142d01e03980c40080c200300f05859007411101c1003000303e4200b5040c2104241c201e040c1800c020480e88001c01c901618900880040d1502c1d41c20100b05100e400e500d29000b58000e68004144040e103610ba8101240b00c10080c500c50005501e015039034031100c3c103c0504007100444048141d001b04018400303d0340726a0142c0b030900b9140ca00008054885040590350350182d030b800319a80c92000000c01800000e00c410310082c0000c25a8110001e929544001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 669521960 1250 669520710 669520729
    0xa0e1f0206070e1e031219140a080c0904062c060415050111070f0b0403150608030319060503030a03021306020105090a02011d0306010b1e1e0307200601060e 69
    0x1c1d0300c0391341d0390150301c446440104000d528500c01030840d5103420b030030451403000740c008a583c043c0c55001036001f080000e0300110b00001d8208100c1605e407412002c0c11000c0d0043c00040c041c51000f40303000ca031240c81500c40303601a401910440d54000e8419070399480400080c541106040c6900c07802c0c00200358141803038010300f6030030100000c506044d681880c00440e0300000c2402641154400c1c440001500700034460a8030103040141d55031907989003141030609070210425003450a080c41d2000c10481c2c0c40011045c3c0743c02010590f03040e082c00240c500618050002504050341c1030100256000500750558010020000c100d8076020b40107680d00c5059081701d40c03c84000450b0313048010300c60010b601c01d0821603645988034811412990080021074a0604240c101405a1100062441c000c0c05141d02115030b4240b104281454000105075188099602e4200304440d1500480803c0c00603024080488039160391a0b80c9442441294061a51b642800e00c03401010451a440d10b03183c0c0e00700760000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 669523210 1250 669521960 669521987
    0x21804060f031b0b03071706090402090610170c071a090c0103050a110c0f0616090308030405030f030702031305151206010201060b0a1e0503010810020a0e1f020607 72
    0x1681c1e1851458a400b1803030390650000b05503142c00e40d900800c40401c1c030f03070141d40140c1182d80c88116440c01d495000c0040da5014111b03d1040d20b0b10410000143e844001443e40a9015240082030308800902522909401c500d4008038000720707010402d0b200c1c2010b0140c080c060007131030b003240b0440c0b18042d58902e07070710160f905503c650000c04001070694000e402c080c0c0c10071a00c0038000345110403540e240215401c110190b020581100c402544051003c00800c3c1d04038082c9409450401814400030b0031010305d1b07120007131036818007000150074040c003401550a00c1008010031550f9182200340291a80d2044051115900007070b1808503003030030540e003800400c5504110941c900850f01058102d522401803005045641b10f04012804e10401005400414000d40b00c61240c110461540d010040031004030408016080c0010072111900182481c034100c01e071840140da80001d20421203a02184241d07075500074807210703582c02c8032150809152040c80942d500395001c6407128001104ca031036081d00d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 669524460 1250 669523210 669523229
    0x60b06040914011502300d1e050108031e0c06011205010c0509010503060105130515070212030a050901120e061305160302030d0e0f330304080421060f02180406 70
    0x43c081e03460003070103800c40b4060340100c0c0ca181c01441014041c0d1b07298460014044c03070b00d071a06000300d4054511807a103003a09654483c284100d6041440d807a959001d81044405288100354610103400d034428121200700c101c0205032100c0d0740c1c541c9000b450119001104480b50340c82e117040508110300c60302c107032a0441c80c143e442900d1034941e10011140ca801c4a04410700d0b42407a403400054540e1030a03080200419140d203000d03111000c500400030340101142000b020b0b82c004000300f1403016802001c4608030402400c1400c111510042020004c0610300580381c1c040c810b120520000a144955803c20b00b885503084400b00d070303880e480001060280e0f00c4000d40613808100800c1e0158000c000030421580c01800c003210803820b2500244015003c00444a081c00d60400941c00388005251584240c2c043c80580c0c0d03145040591741c1d01721521840c40f0790703a090b2040007040400105252440c50001d604450f0520221080c0c941c801c0c001c0d40300d07a010030801c4964203403204c407030305190281d80100c611200c1c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 669525710 1250 669524460 669524473
    0xf131d070806102c010f080f01050103110d021804050106030b0f04020c030c010609020901020c030706091809022806170f1003021023040b0313060b06040914011502 72
    0x2410b01140d052411580c40a04c6040b025004080344841c600901480c108000040845203400015004c4001c5110a1080010000422004140482e011030440c8c40c2032034001440b81140c0081866030066220920b2103e00005041c003103020402440011000121010040d80e642c4440c19011581000d50403900035a90712200540d070303c0c0a44c068400c0c1700c10841500e141000003000d080c2101c4113030b0004500b05038049150515964100031078011004103800030194030741446030117402c0d00858400e800c035518220744105a090882d0b0400101c40d603024121000112503580d03801c001c54050000e50328036102045000a0161140ca0394402440c13600c4c0c400c03200d540700c0083c108940d8200030b000d00d80d5131030801d50000c0183c81e4600d41d5141d0109070340c0c90000b8201c800c4d50303184200104401000402809200a210041c2400101d903001b0b000d503c2c4a1240e0700c0b083c40c0a801410344110601d60040d0003180010b10107165030403044490040107449203331030f0f881c1d002842e11049007a1103900143d2100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 669526960 1250 669525710 669525721
    0xf27030807030e040506060304110f0415180615120908120a0902100206070c020d020f0613140103050c09010e031015061403090606100c06060f0e060a05060a0e04020f131d0708 77
    0x28100d0484100c0180021400f441510f00d03107103072370751645d20040440303020a040080c002c031284541c601a01d200604007011303003c910001056018038944044210f075440302a00d04211070002150b80850900e8540220b0b441c0140040c4021314a001003039000308045506000d00034404a009841394100d51107114149209030207020101943c01c00c1240c1007840241a41490b40c1e851001e003c03d0118014014440c505010340e443d101d0016500302c0341454100414450054140810345040403820318107a0500f81d1003100007490418141c90040c0004c0c58812110101154021400f043d00d4081e241d08205024844628030188000c0f1503130040da03000700c000b00d85246080040501c00d1845854010303031446054503044100c0c0c41a80c082030201365022400c01c4442d085401d2694802400c5400d00025071511012841a1151040041c104820704401c0065a66a5030598081e00c40001075551100c0d01e40e88202c80c0c40340f00d8001c003440d040d0610140c00c00c2c004405d84040c49036503a079540e0451900c0d030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 669528210 1250 669526960 669526969
    0x606051611030604120f090b0f0d021c020d151a031305060f0f090c0120030d020f0409060e04240207080a170105010f27030807030e04050606030411 65
    0x308042220070058441500072141d8040000038000e50042c1c902c0a0840c50341c0c2005040d510000341400b007800880e403c208110f083e01c42c2625010480b81d0704182e030385c2e001c19001c80000e104046c0d41079941c1c0803090701005100c1e501d5018101c4134500705010000e107450419a6802010701c3d1096001241c2d40180b280c06000c0000c0c040c54016100c1c0403041d48641c0103682d028101201180c04440308410641003205c0d80d100100656042031070305018180d101100d8000820a11095000b421009050304444000000820456140c5901c1080442d04c0311504650114160b00c079100d9424010b06207400812020a10728450380560382c410351b200c3e078008211040340d0741c2103500d40104c4c00d02c0d41c2c01e01180011808a44c01810f983c3c045645408803102000040d8140b80700603006941000400c070300014400b43c020242c45107080b015034096582c0c1b80700182d05548203581d5040140300c10008540a020160800c440306908e25049070280035958032002844454041154007412510112504400c1401c1c0f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 669529460 1250 669528210 669528247
    0x32505040c0207080307030c020a0b03040b040609030216170d050c1509160315050a02090a091503120203043204091a090f0c061801050a260106030f060605 68
    0x8079801911611640c40d00e4460860b0441c0304141c001c1042c40707c15900314500300542c18007518203800d18034158149034440c20f8110034004d1000381600d91350300c1502c007418000c001d2403040c941481c0d00151026203681c0d5a800d00d00d541c1c44c040c2180c1c461480a03d41c2c540c01013041e244240d00f0540248503999045c0c401e8101c82d0b030007400382c0e0303035500030662560303201c1c1045000138014500448a01903500c07a22603503d001c0b0350b0300508031003000d84103003e0607450b80d540b402060211098000c1c00f1412260750f507900003440078258802410b4580442049040c0d503008801fa00c01c507503500c02901001000320f0f040c016058000300300084a2240780b2010607140c43d040c3c1c421b418023805490310031400c00152500e42603104080d500e042480c0d2082c02568140601080b0604001c03900b0384540341071141d404050b0f18403400601c9000c4c14030a001c105a06c60300d215121100c1c04e42410a120206000400307016002c9080030f0141000203800c0c016a140d40000601440741200c1c2c0c656226480d044010003403010040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 669530710 1250 669529460 669529481
    0x50c011202040504020307170907030c1203110d020a0b090c033403111e031b2205040b010608040510020306041508010203010f050a1203050702010c020d0b0603250504 73
    0x20303400d10020030184c0f1644003540c42090310f48c0f100710b4941c407042c1c004200b1100c001e02218060f48883c0c03041c400078000714480d13400c50301d106803003240c20354491905503004910901082e04502c00c1d0703103907020070319400251080c1e000d014400c810b02c940c840404458844c40c5582c00e05805a100f078081c1c44805000c0c054400c0482110580e1041d1111584400c040c42d0629510984809440324040030031407400c201106040324560103140d680f8000a800300c2e4456000c1071400600c50b200003204055621000039000490041805400304a5118890000204015181130310741e20046800450703c80e0044101d9130003160040300410540030b07450f002d00301a620040240c1d82050301c400c10074078900c0c0d84140400290002000240c0c496042c46000542803095500951080d10f21000403c802500408216245c41d051321340541d41e907002d4001030f10b401e0031701c8000940100302000c001d000d01c142444041d000e05011003e0784d00240b0342e902d11021102040d03c002c0c200320204c2000300505c0c5042d0b4005603155 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 669531960 1250 669530710 669530747
    0x3120e010c0b0f1f030f1209030212150703020f030a05060f030703080c100606170c0f0703020a02010f0327052e1103010b030a0b0a030206030903070302010605030604050c01 76
    0x2481035036880300d12280030f6036444180c0b0480414042d41900e8408100c1182c515900c0501d905459619018442c808124000e03255004401910000c180725120b210701842d0041c001040306001010655078889a881c07601c1028540d16000c2090b0500c03c0c0219042c010340030784c8690a6486010444004290181241c0e6205005291603006034a060003004025401590025199180d090409042620301040100802e00e440c200303108843e04401c80c95060041c2008411090f0b44007500780c100c038859401c00490719003003c0382000806500182c1d81c48110f06c00c3c0e0764115400781019058080c1d5000b5550032184030380c040d084180c107000c034076910504180a00b044454110340a0081855032401003000800c003c80251110221a060f00a282580c210b02083c141345d5858040400e400b0300010341499000c03510340c2c071303140090b5841ca1114805180c0080086035a4205800b486a8990081c4402ca003d0350038030740c1c00a1180b5000c03503850320554221014141e9107401800441c1c41c4210303040141c084 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 669533210 1250 669531960 669531977
    0x501090e010323011505030708061e0a020904020d061809080315130c0206040318031e0503090910050a090b030304030809060705060f01030b0f09120d0608011a100903120e01 76
    0x705a03090265005c403100200200740a58240424103050110030340041d0320340d5205000780414500000400f1000102071002c080e41034075000e1180c0b0292007812410b9901c180049402c8084a2680c0d00940850f5a0000035140c01c0ca808215601038494400f03026100031014000a00c4554602001c101c068600032709614040002052500880d600300c03000c1c40059020104000406810103600000c104900c55840006855035841801ca1041d140701d112140c0e18614000042220420543d0004600208840d80c02c0c07600c681c6120201003984540791289a0303600000078000c1c10703840307211030302c68001d0086c5142c0703815070715046902d42c00300310340700d411040c100100d0300442c1043c000e0711f00420818465982c1540b550802c010712420107022000403280302018428103182c00680010740584074a0000d407540c0c4e0346010743d00284029030111030716508100310080840c000354080304e01081d040b10307244400700c11201c084402c0f204500005104507c9a914030b44218000c60310300d0505032051500000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 669534460 1250 669533210 669533273
    0x31903050d1d0105270304031b0503060f070806040207050304030f030c0506010801060e06011b0f0501020f0406030f0f0b150721050315040b01050f130e100905010501090e0103 77
    0x4550359052101080ea559801032103482101783d5103080c803140078014150162103655460585912691200808643e101103040c002c2e064030000302c10040c00b0003011785a0720319180015405440d011517101c40011441000a110392034140300b941c0b80603402c8002541014116907521400058100c429014018482c8150300060410007016018044510000c07402d1890100400c4003142c02400742c5040c03100c8120302d8a9000c0b090081220002d802c28415281e10204e420114024414007421001c6403600003408103003c0d4240d00503050441c5005070030000086071800f15407ca88511003410ba000440100001d1070440d1a0302905c0c1640c040c1e108180d085c0740d2440c030848810034005108001c104040108040c1d540500760b001c44c0321005403818010214880e000810600c12142402e5002c0d01c042424440301003850407620240002d81a40035a40c00c001e100028514018422140d03044e00340303c0007151652041c903041048507802018811180d080d0350700d03104220f421410b0b143c480c150300e01440c071 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 669535710 1250 669534460 669534491
    0x4090b0a180b09160f1d090a02120f0607050319020d0e06160909060311100e09070f0e0306010b0306130902090103051e0708030f1803061f090501050907030905120423031903050d 78
    0x140700301b000c0040ca803d181072222f45080030002484c0d007080c48000c0c01082003c03120080d0f8504004050000107aa0300d07030185107000104640b008a44c554403135030040003ca10014000e10030201400e0302c4500c9001d80d10b107000380503504140401000c0890914a00c001c03030610301000178600c150307070626170401017240c0c0204200c0442100c00100081d00445078003141c43d041125103020880550140103d5810102c0c00340071844050402800b890b400901c00007645c144c0d07401600c86c2c9900502e40c4500e943e49040040e5204030103d004194270911003440038010340c000445a01319150035001e14103048031080000165042510202c00e12803020b440c102c0c0907942030008500c104106d9a000c101140c1c9410f0002c501207081d000514202c3c075000045c08155503503407665601c000d9928022440700418a85582403003403625000300140e201040116400c03407081c2ca1524034051b0407a4500821202e001050b07070701d490903e12170520034407990802d40401d101d44000c2004040460010440d00b50b880c0175003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 669536960 1250 669535710 669535729
    0xf0415080d181d0408090607050a080c010510030b06010f031b0c0606060c17071a01080a0b07030501051014091905040b04090b0a180b09160f1d090a02 66
    0x4000007044002e401c09140e0078464844040c0c1010b956182010545100328034076040701610151040750085200155a91108100d440d0030758040191680c9000038544480b40d500b110940880c10b50034140010f0b0300e40e42079680041269008a400d02c0d1680325403006684100c0b43c86600c200305522500139540c2c01c08628500c05c0c0c420025661515070f03124500308082102c603503030010f008104e511801c86020540c004c0c5041d1640c810480ca00f40d03070701068581101100d94000c0d8108541040000000d800751020540445040c0540040d00c075030b580d01034048007140c909000d00c079807000c440e01d15806014880d044240c40c00382c8446d1010b15110340b04001494880e4503280300a603e0061800038842402e01d40170b8030200c0c00b81560140034529942e035a0880d040f000070f0292210540c0c03404828601c22080c2070b0724002030b0300840310108505048185513140e040c40c1d2000500005465400111546203102c0d500c02c480a51500c1c05001c031003401c00008945015100c038500c0e2150760400005aa20403924 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 669538210 1250 669536960 669536983
    0x42303100f093002010204062705150d0b0306010f031b1e08120f071b0e0a0b100908060703090303110a021501120f0f1e080d06080c0f041508 62
    0x11054160f1000b1074202010090368644000c590050108120701500300762a81804440100032140c81192271a5003a0b805084e5841642e001c41c21442d002c0c2040d0300c4034024007410924000910403100c0368014560345000a11902d5100308401c2c10801c02b00b00040130301103440100a1030f240980342d4805c1682d2402c2000c10041b1241c1101c400100700c0310380200403039401854401c80d400d00740102243d04a54078000d50380d024024501c2141000940031401c41b0718000751072a41c00222043c20016080f000421001040902414074000508005030149540390112401c0400070a001d40c0d41020480107052061421028103440b80b021180544101c806001e0b00c441d150f0080503000040000c200c083c40e81a40003c40304e1514424542c04076003194020411187c103c0b54141d6102c410346842000e0103d004260141040402070810030000c0000080c207400002c0807052001e81e032200256a15030341c1070b0004a5101500e140a40701d141019080a42c5c4003504495200c503042c0d4564000d41071a01c11201c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 669539460 1250 669538210 669538253
    0x501080c12010b0a0e041b0e03030712020105100e3105060a0507081b16030e04051302010207060e01080a0906021e030105010311031612060f0605042303100f09 70
    0xc01d04800e170317404503c0c00341c9003400311030501068207140003074810300c08008001d100704488490304202079103041045502e92076210202c10902c01584400034000c100980d5039890380c08091400186110640b040e80d4052911030340e03442601d002013501c030b40c5103500103000c2d03c00289440f40c51802050303040c441d040c40f4111104002c14645403511004007200ca0003032408031010700d032111081906240d842610003c40c01118020351085560400b611000a040c0750a0741c443d041c8001c100c110780441f42c445a095200317800b11680705803a6802510381d00120079216002a041e074002500b08081508102a00c078080c01c4010b1a06001c01380c0103500c2c2d000c010000d81c00801c008010806943d0502c40d0700740310600d01802c1420b6060880d03106403c0d1134000ca0132410800450314146100460307510040080032002024030f5155a920005040d9070814032a50200c46c1940010014001d440c00c1c05524102c4020080c00c0c0314800c88403488001d03d1030403c81c4400c242e0b5610754074001008401344220080c41c104 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 669540710 1250 669539460 669539467
    0x2070911070b160504090c02030405090702030a3902060904110403050f010c051602042c011b0e01140706090812061914030c0603010e09060a060602070501080c12010b 73
    0x2000060354401038043c1e036100310f504001010712540041541c1c20b40320710900c04035408580c010100d2450040350085944403041800340480580c00000038524480d903511540c9141001e00341c03a50b4205901001a502440440890042810200b03036500100384003c09036404d2203c4040810210345440240c00307500c0c040083d0a0080c41410802c4806285400c0024007560003c504020264010303c001005500340b0028a0011544c80e9000365000341c0510307400c0c080c3c14402e099541c2039918a03407501c1c012946042249401140101c941101c103450f00d449840003030f2101710044440601c04201d07000b24440504c05900010242c2c0a14000b4500411030b282e00c40225a861010420300a05040d11484200c030900910351910180c800481e4100c43c0405200985d00c6e02090500712030201059005100000100711442180708050003101c6e541d003200c1d000d540d000e501508540d002e010300ca015a100d003508119540c881c400380b0b0b43c00b00c0000c0b0b14900b806155040b1001c0d04400303800030741079041c021 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 669541960 1250 669540710 669540713
    0x181c08191b0f1d100819050f060117010f1215050c0403060c08060108040210050d021201030b012909040605130c2a0f14061810020c06070f0207091107 66
    0x800c3c9107841c901e41d0084901c21003030000740240c42c00c031440c882480310520010b0b0036076440c9210901e100e09140001d21007407908004c0170001d0380017102d07054049000151280c007000a0148418142d030041078542c01440d0a242154130719079100d0750708403181c180440d424910110079005040c028041907400300d480386d0640c5020300c20341e48011010b0f01003043d039004002690b0fa12003400b54100f9011b0b1041e0082d80c804c8c1c0701c221014401c1c44907042040d0300000e04020010750365104c43e4100c0c1e000d480c0061460f41c80310a21690501d40d002800040d80c0004520070301400c00800501454400030710000d40c0b2075440021600040c14150b0680748075035500400110150404090724402c91030030075090704851560250501c6010f4800042c3c41e1802e044a40002c20201d54105001001290119000c0f4035020031384040110301e80024140300d0160000ea02c180d40b0705030085d20b800c400ca20014007295038444008035900e802c114011360444c82490400115080070344681002014440d4083d0340d5440345 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 669543210 1250 669541960 669541967
    0x70f0f0c06050a02100c1e0c0506070206010509070e0103090c18060e161b06020c1e280201140408010b030c06040b070b07030b0306181c08191b0f 64
    0x11688450306000b07007048100d01c0d0a601003203031552074801c0030002a007a40c4907502103604020f110a003244600f40951260388040e04100252500351041c012103105641d5404101e0315002c0a114264000807a0300200e20424040d11046500748418900002c00c9421030b100c1e10b900c0e0301c459104119400d211005101100f1b1a4024030015140041d0b04401c10304190f01d40c1b0450741550880c7e1303001c10406408001c0d400881000e49003c4036002071065450f2984445c5041c0c843c0c021044007244c060202e481c0c1300d500c0101142e24600d0601784150340c42c08000302c4400954900c02d000d0700702e0420003d410f07180143c00600300a00003400d111030001070090310203010304d031609140b0302e011840f42038248001c002501c035600441d00034591151881441e92121103056000c0c0a000c0c5165a1501941e4100320503043d6090b0000003441800c0111145844007000a140e03800b03000355030000140c00c840015002000445519200340000d640028840005c0c002e0311070302c00480035001d00003503441120318a90390750 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 669544460 1250 669543210 669543233
    0x10e0d0305040b150306010b1305060a0e031603082a06040602040501030c09051e01110a03050a0e0f0a0302010e13020414030d090b0a0c11030d02010b0103110a05040509090102070f0f 80
    0x2080c913201e503107400c040000a661a001440b401030301100004e500e060000304022000000d100180003140c858120800c0513080c502100790080c082e1180c1c03140000100031803010380080302d0b00840e003289806004d070070390f0741030303442d4090804110480f040845004d0300e800c000c5684100c2c080d60340140c8942c2428001803d45020b5403070b00007002039071070080c0400c0e0f883d030201c0c5251803540c0001110740c002d50001a514020306044150f1103004d104a00007d158200d00182a061074669030242c0914540c0d0400c10301a02442c412a00075200c643e084c801075003d203180300c00300d403402400242e81e19042210300c0140e9010382c2244802016200d090411030a042194803000030090402680c1c10b810416030400328050342c45041d0810004178914403c2c405141c146031503400014040c0c43d4041d2148501034060001d0561180c0068604605a1168242003040e2540d074840b65592070304d4103151104000f9000006014107041d075500b0442c0c03000082141c0b90318407110b4483d8480005101d1035081902c81c0c0302 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 669545710 1250 669544460 669544471
    0x5060f040c060f0512090a080307020303100906080312090709290103050403021b010e210f0d020c040b0a080604242705070806010f03060f0e030318010e0d0305040b 72
    0x1a605101c3c003290450305a070401d14003145044280c0c1d035945a018689103c41a0141ca0041c0000a2081c01d40e404801507101d1000d06c0210090302d80d0b180b07040412144144204441038005100e08a000c400d4020555080206032044560258681c6411402c440300e03994020641c0700d003640c00707000c1302c02420401076034550709007010401840c03d6200a920342c4101c600300c040c0f49860ba00300480d41da0080341a030803041806043c0c14403903441c4121184000700c01015032030082c07003030940c2040f6120001a2502c5404113a9003e0007807410301c2c109100c050464004815440003520401041c500020080c40b80314900454214003003500518040c0c003200640d054210b06d86080074400c00e03090b22a05a440340d45010080c54443e0b600082c1009403c00415401c10712160103600c1c000100c0c05408040c8a0aaa00a250800c02c00041c030b03003c10201c904d00c120031442c0303410902c00505070b85003070311300159006c04010000c40c200e050540120704009810401d400031940c1c1e0b009010a005143c111203a000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 669546960 1250 669545710 669545717
    0x103020714060c0d0f0203041a0a060e0c0702030105090a080f160f0804050a0e0c09101e08160914100c05010203040c0611191e1e060c020625030905060f040c06 70
    0x141859252581c0110044001c1c0d40c0341c904549c00b0a422403281d81c885e00080004943c0c1042030304058032219065441140305074429070034000861220b0343e003c17400380720840d8002c1005281002115034400550003590312a4010525480541c0c0801d242d410400451845513841c0369449052034208044100b0b0394210100210400c410400710380e07000403c44440d80c01c100c0e036009882040883c12540f080076403482040b0011414110752003541c0282c00d103809114842c0080350045001e400483d80e103a0580315190711059000b2880da010700b450100303038088a04038901003140c039140340c4440342a6442aa012581030f0305010040195a80c01035150754409015005012880005486000350f41112103024046d51510400c100d05003100300c1032054510340c0316132005e200406c00d90714103844085005040e02e826003080800c0869902c08030ba802d1040d110304e4014400321089035050605403440303050b140d081c507a98180c40004a401048403500c1041c3d61a04001c0c1071030240350000c2071504070790080e07052 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 669548210 1250 669546960 669546967
    0xa0f060906140f13030230121b03040302030607080709090209011d010e03010f1a01020d020a140109061b180f06080c070606060203030703050f0f04020103020714060c0d0f02 76
    0x10b82e0600d0845140d1500c20146507100c1c1408103495220341307000e50000394070040d0b00007a013019030031a0321080b031600042241468191031000101e0f843d550300d5000540f1000d001c004660b890202169505912800103007280d003865100d030301191921070182c1e030490100740340b6001c110003560301010503005050b0180c01542410900300000c0c150340035000941440c54803402110040c0d03403142c0310b14644c0480082c02880480340e00b4603420014060000b41610b41d000550340e50000b03500004810021041581c01444084642e88840d0303400c5268940c540780554880032040045504c81c02008000181e0203001c00346e020741080d000d0031414410358108041c050709013042001488018800d02240d28a0a1207041aa20803078810307068410980c00911030342c40c000011a2180e4008082e5214001315101002291030b144201840040215a10700006490000080c015403194004c1c0c080c041c49070030511400503090204a0405008840d0040203000202e0740300b00e00c01c824090303d900d9042d0300408619 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 669549460 1250 669548210 669548237
    0xb031f060504030206070b0a111b300a180f05030c03070e060609010512010b030103020a080102120403140721030609060807050f15030a09110301021c0b0f0a0f060906 73
    0xf0070700424002030047c070815400500e0491040d0031a117034108480e61038a668900380360124400300c001c0007440301140320b601c0d40e20001d0130301d500c8200b40f81004a101c10003d503082580000166101c0756481007044821240305e0388245460200700c01901e102e00040312403d04010134076123003d60b1072009500c04c0d03006000c100100e92551a07155000101070310f8244d0703625146401610f075445a0781281d4201c28140c00001140240800590705891003122000102d83d902c1000c0c4d402c0c0e01464004030142e85443e8040307400207001d88040070a85003001d849905101480e110100006030800c100b030804501c0310403980c14581e061150700c0240021900811001e400c0400665545441e0f00a4a00035042501c5940580d0784070b00b686240c400e0b82020041d924503203001d208008d000803000c12210780b584100b60200501c1c060003542c281c0743c0a0145c02159041c140381100151000200c000c2d0499070300c40603242d05489440340394014200c41141030145502e8114010100c07406d0b0b0388210f0401806050070740 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 669550710 1250 669549460 669549469
    0x9180b060409231f050a15030b071b0803040b0a0b0102010e0a110127050f091603050a151205070501090510030509010f0504050c01030e01050714070c0b031f0605040302 74
    0x3e040b1001014841e008010101c0b245041445000000c00c019080000e007650300454022030320030214010705002240000700080358490b400d020041042100703000040c141441503000c0f03849440300c3c0f401c4291a00154495442907801a5025201036185008100c0750003030300d000c0c40301d1804082c40208880200d040140e51103080d0454002c2c06400740180c4003110f80e1285880c108010241c040c240b02e998181400700c001612103103d02ca00800f100c1071000090b20301000194841e94100c0b050f1080b104c0041c100320020b180c000d11034007070340d072390b88020740c0c0c4100340c0c2c2d190f0302301a182c01810f0300307840002814030342e2800c80030307905c281e04000912800b4003103a1101410380050200c141000304241c0c540300d0990b40136041004d130103000d61380340800300310511000080301c005200c0c081e00c007080b032148128412420307500111820800310381303400b40410b0f58001034402001d00b0b50082100f040e11549036524007080754003d4900041c100703c042c840200c2040003041030001008142011032030315255a0205 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 669551960 1250 669550710 669550733
    0x10080c04020c0c04051806010623030402040608070801062103051b070305010903050405011d1c060209130207021f0f0507210302041e030c03020d020a09180b060409 72
    0x480c000c50300850701c900401e0080040301000c40d0000c00900042c0b411040d240c1c81c030910014802c003507104040000807258010a088491128010481141c0c0d20621085c0700307091340040d0040b40c010366207a00000d086401417161070040d02140c8000314010f8a000001c7d1044000c0b000c5203510071a4a00d003c0300041d8000048810924023400300703064442d40a00b0850038501c0d00d50001d80306508080000e020141e01c00002c00c00c0e10407d80300c8032100182d5000b03000803883c401e0409500710602490714030ba104480c00c8109a072500c00c1c2c030050702c1d1407141000304100c001e40b00c1c190100030b60040382d20b400710b00c0c3ca40070090320040c0e11404805002200c0b070780280300c980c004903944188200051900c051001b10034205030244004c0d500500d20f0b0320f41100c001d000f5401845400d207400414000c070801c00710302080300011640c2101015499900715000c000300c01011000c100e0b03000c00c9030040000d1034041e80c011201d8410131015021810309003800c01d520501c2c0001e01c8a88a03d150100da14009002100c90 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 669553210 1250 669551960 669551983
    0x3030907080f06041b03060e011b0f080c030a0e011802040b180f0408040302031504140a020f042f0a17240103020c010e01290102030d0b01022103040204051008 70
    0x100c002140305c6800c10843c600c0a6000501172605000080361008015080300e9002c00c400001d48061500004e400c54000400481e18400182c02001042c010b1031403201071600010b218000040d01000460b16508507444420032004000310041490300350300e4240b00c0c409115406840824a01400401045104000502200b045103485010906010104060760051a4040c084030504100d19400044114086604031001020000300349465107002c15030070319140e40038041070140c800800800003d00600c052045d001960648080d1081c4250300200c0710742421401416a580101480101001008219405940c2c035410901c000000e40000104082c11120150820040d070a00120003a104a50745a001c81d0300b00794503506440019800120141004469001180b20030329078186485800b02085000da041030020078101c80040e0002030030410148180c1d00c0800308204442006142400890b10080c400320401c01113050611a054122014200140c0450301c0d002c0002d90f605c2d40040c0b03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 669554460 1250 669553210 669553223
    0x6030803011203120f0902284202060f0f0406021c150e060f01170a0e030703111b0a0b0a020a0b18070e06030616020a0c0803030907080f0604 62
    0x200c80b041c140700709000c61a800b0119400c3c0f00c0341c2650710149003d00380040c0142d03c00c42204d910f544040282c4046402070f6117030308203e240c14900e8050341c003850403030b08603101c003c04d5002c0104107484181c20000c140006100300c1c500340c0d59044008001c1ca0240005c01000d140d003803840a100c035511401581c2c2e540107a20000151751100c1507414058010500d82d9101c01440c14607400b101b1400020203800166480c0020000c02ca5541404001a200c0001c442c140810b848110301d41c2c001418002883e40941c07440c1c00401c110140100092441c2c1c0030513800d500140001c0c22040c06103d041c03010f80c00002d800004001e2146000e80051559416403080c418041000210100e4841c001c0c040c00407859088005c201e8a4a0440080e4001035000340040d4803500401e04042034034071050000d03d014020250040800ba62210035a000b40c2e566001020294030031800150001550345510b0009021164051503c07414540007040c508000c5400040f0150883c00c00f07003e0318280040c0c1c0d01d911540209 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 669555710 1250 669554460 669554489
    0x8070929011b08120709051e06090108040f080c1c17070f110601080705090603030a050412140a0f05010e0a2103021e0c0c0a080c0409050c1c0c05040603080301 70
    0x3e0003140700c0c85840140c1c1041e000c2c03003040003400c9803c41203100450380b040d075100300780400404661402800340c0203a10351200e001c0c0000300e00c95104496640d4028070414500b1080d41302505c45030f42c00c1d00300518000650340304c0c0c014001106c2051032044102034403800c00c2e020f81e000c81c0b4100c0d404460010105000c200c100d10800d5415031042e07071001d80c0d08080800341e8869503120201d0548440341da02405020309000004209030381030020450f49101020b0351504c0c100350030410f83c0d018155030340c203098550066401076401d01100511501c102d2500c580c01d1902d40100d18035102c0d0a4403103041d0b03a01d041e034019698074008948541c0011f91400e91401d007040180e00c410000303400a01900e500090014111300b506403564040500401c203940c404011201c28030420f60400c181a41c00d8010380600380c0007441a151282041d07040380ca56144a2000c1d1403850b0100004079010080500f01c00c2c1c41c40340c05a40080900400b00958409040262070512040b800c54030340040b41d103c184180f440c090401c2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 669556960 1250 669555710 669555713
    0xd060b180621010f060608090714100c030c2a050901181d1509010b031b0d03030b062101080105040b0619050301020d050f0601030b01120b0a08070929011b 68
    0xa5200c1408407074800300410551b9200c00300204494800c80340d248561140031004222460a5408100d580000600c0000941e0203502c00300c0c0e2644c18044107c0c00e02c16068449000103202d0440754600000341881c901c8a0141c201d80701c1c0c1070088940c811801152040c00510480c000c02c03030924040c40c03009a003c51000317503100ca240d5003280455407488260195031844405c3c3d43d00d01e816a4040c20100000317000039425542015218400c82c076801c00101d40700154812a03040c1340794032018540c0a810000b60018291021505960040d0960055201158685401107044981c11800740401c40300801051409981d0290451809084944101c0d00b82030a0302d100585120000050440540203540b41c80300b50004202a00301603c110301c69903140030004816510a2040303240405050791000441c2001d46140801002d0b03100c01e10f07801522001000c2100c000401c501401402040c500242200d0340a4440c0d40e8885c10041c8100b1802c038200c0c01100980c1d1110310038155006000441d200c01506 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 669558210 1250 669556960 669556963
    0x140a11010c0908100e030d1a180c040312030e0708160f1809081c0b01030b060c30071202071712090d050a030f0f020f100c020c0d060b180621 62
    0x601000024240c00c1230f859818009040c079010000340c1c4203803080301c1515640c080341040300c001203d00d070744404428001003022409a040909030980541000640000840d203024148100c60f0855030565101c5035803001c0f10102044910010000041c02000b4a4100a40402e20118008060b002a07880310289410702468078119000c2c9a4061043c0750042d01140c0f803c0040c01041c49014046480c04400d800c144c2454000c940ea810046400f9000302c008481910500c1480c0310030f0000030300d00b20030b44402c01d00240002008103900511000c0c0c000d07040207400a180c000b0907042710080d1300c010a0a000000070000344c6011850b030198619807214480c2000c14130f105510480030b0f140d44208016002415080442031002c510f02c0e035580340b0100da01403410380e0380b44160702200702c05606c08000d00905082c00c0d801000241680c0c41528020168100041c1c0d011040741d40c10350302d2903640e80b00300100b464245e80d4880101c2601007895624a0301d140000c00310881844c684101c41801d411100c0705100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 669559460 1250 669558210 669558217
    0x803180411041d0c040305030909150d0614150d1e0b13060f11041e03080307081006031a060a1715011b0c0b0703140a11010c0908100e03 60
    0x79440d04464440ea41c40c4076076444001880754612403405684045603e980c006001c031000d8a40050003907144c2030b102810300c694020014036040950170b1120510003240e5400000b00041401407001240091901c5030107041c009000c0c0c0040040c02c2c4880d6100e00c96222210108021038004005130008003003805c50440c0c3d20610310000f0000312007041005a030401c003192a42c5c8603030080008206207003841e43c1800c11500701c0b5007255640b9034140420840b0110000c442102c00400d01c21900d08281d032642c401c412508240d030000082000c2d6001c010316050703407040390030042c503480c076003844480e240a2400100b40345075496540030700c00000e4990401401001c4048880071143c208100600e0030894102d000b00c95802000d000448025410701001014140440e9568000d8080100300d4900ba6180c403103644025000c400740900310300310849a060920140044920948a00c2c0c070300321500400908441c0c04010301e5062100c0310405004880c070004501c0980c0c0c0800d0f01c0060200c802e00c00e43e40c0b4500 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 669560710 1250 669559460 669559481
    0x70510142503050705061b0d02180d0819050a0c0b06010c050f0c03070b03060a0b0a0c0b04060c0e1009090f0b040519060f030b0a0203100314071e08031804 68
    0x1c2150500c001003540c030100400b40c00d4080c0b000c0d01d4403038403412484004107440107010398501e40306120443d041c4040d64000c00f1080344c144651901e66210f440070402084d01c081c8203079181e01010402200d210217021510030124614a001c92030408881c101404090459102a054040102c00140300e42d005490307641404d50840d04541d40040035120195842c928044518002c5c010a1030010700f81048005481c0030742c6000380200e03409401c008840703040f50003941c1820b04121454081d480840e00c00d00602e4000d038000e51020420961181c00030740208054003115008003006440b00d8001540200b400342694042038009c5103001c1e00c0c00800c0007a00e04518965841840c0030240000c4403101500c041d03c514428070b09205443e981c0c2ea0302020300c41c05101c05881c001100700080d9040f42c080d4029035210811094003104030b6141d446040450684422460190b0721803041800503000311740d030103984e50701d01d41210154682080c81081d00d81c05800695001e120140c2c2211346659201c3c0c202d1500c1c10b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 669561960 1250 669560710 669560767
    0x3121611090901050103031416110103020f07050601050a15081314010f14061c06020310150c0b06030c010905062d042c010302061606050c0a0207051014 67
    0x1420701da01640d000306020700c01107011402d40940c00690624803419200a9002c0494400e00910180c444ac5060410901010304240c3c3c00c00c460031b1011181d07006402d404e80a0300040c8a198180b40c103100006e0036513000f41101c90720744030316014900d40c400007040c1c0c4078441740e103400c00310940c0345803d002c4881e4140c001c50082d400d0048000000c82d00b0f0740031668546402c1d41010998550341c090103044002250108012448902c0c044045007181d00290741010301074202c0e01c2c049a44a544c4034047c1d00991404d00013070b003010f804070240485185e6298100344120050640ca5501c0d00010f06500302a208080c0035100c0401c0d2000210a150100381c0c084400c03205c0f0042420382010368040ba40c1c0940503904080e80205540444242020322500ca18404824034803c9a401e5400301314580d08102c9000c120803070342d8030491001400d240a002d006604420026031160300803400a0f04141c21504064060462150701c210881d601c0442c2c10740b4160703410034040d03803000c07107111010840315180c6104070755 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 669563210 1250 669561960 669561979
    0x2210d090f0501050a02090a1409010b0a020a12080a0c0908071202030f0102030702061e0c0a031107150f060509090a320c10051c11040e1302090603121611 68
    0x10005150024407421f07030211540ca40b03484d04d8012010300342a0580c034564012043d800188594100c1e00014010580c00d40120380e6145d1403030707403050000d8207c1300071a00050b00031018423002c141640203201d40001c0609118192a0410f080c05965a58906c41e4440340c1d2140340c1c0c52025900c044c016032502c0b00c5044000c0d1768919003a60065560841550380c4000744081000105c07035500c0c800c08407801140c07001c003000d02e049a00c41048000e80406003601226800c1003003d000000d40035461000b02000b03098011903030100c6e51291034121003460344041c1c0100e0b0845c0400c5403c00010458400075a4016074281f0759513106410780101110300103003c0c00b01c2550315000740d503200b40069001c0c90f1640403141c59000094440003182c81e0700403409082130b010010307140c0815100c0c0c0b50b082000140c000960090400d0365404200c81e0303501c4103030741070001900f400c03002c0d0003541080c5184545c0301505030300504810028100e210030750722070981541244c45100c8402401c02242c0203107483c001000500306400b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 669564460 1250 669563210 669563221
    0x9161d0603010905480a05150301050405041401140109150605071b030c03060f0c0e09060904060e121801050906120c04050604060e031b010e090a1104030c030302210d090f050105 78
    0x200b507100f01c0c14240309184500c0001510708e00643c0c10101070605403402429a4604030500010380750180c0708850b40840100c000700d6001c2d00740b00340c0510f9100c0035840c004079450040079001300d601300f81000b103040325006001c2c480c4a410034101d07240540d010b00b04801138040810180301a000383d0704002d06000002800205000540d042103c68a51039441001120a481000c0d91880707100c01303140e9008a8030300c1c00500149003004425030310502030a400704bc05004541e4640c02c11000500d2106085001b04000030134611030030544c0b40c096403e082540c5402034441c0051114001c6210004000c403456000921403882c0c83d050340d00400c0042d00c02601c5603280e0340301400354801d81e140c3c0e9029200c2d030170602444106c0045024042501a10707984448150170040c001c800a00922003001c0716120300c14240761641c4040140001c6005807031100c00d150441c60300a00b040c00444c1088240450040c0318101c0c40b018008544000001f00c0000807596100d2502030044940184058080e529200070002e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 669565710 1250 669564460 669564583
    0x12081b0f072d0f06060b1809041713030308060d1703180105040822030b0c07050304080f060f0108030a080106030209011803031d040219030509161d0603010905 70
    0x2190f05114603810322110b13031038243c21040d5000d00e203804043e0400300400384459040c101c844a812a015000229851046c18500310556010780f0700e503d00f02c0d038119030170402e05522000898100b40b0131904a03600703460ba40c90fa11001e2030310541034140c1c1000080454071004440c5d6010b0301e4650720000a00c450710341801e02001d140c1250414080c4101098013a4103103200f0103030308209981d409032107082035444440300d02c003103500729402c200d07141d12003000045000d40080000010f02c0c40b03400028100340ca09041402045541a8426940c940c814040099a550028a6141521001d140050b144e01d00600121409850201e01304100001c0e0080071082c1a84100c01d0307144000c12007a403242803005503040c08101d01c502d8442d0b45100c0e0a0581d15500b152281d0826034005c80b420702154038492242152000e0a1401d500c00c40c10a140d001c20204211150103400d680160300310020010395030552545900c6d0343d034881c01400c031a03c007a601031044102c000050801c00300801100d0078002c20141c80907 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 669566960 1250 669565710 669565733
    0x30c061501090504090b07050306060d06080106050f0a0608151807020d020c010507030206040b0a110a03050415180627050f0105090304050105070b060a0312081b0f072d 74
    0x540002c5000c0c60115260a00b80115680381d40c1c80140131a2941d60681d04542d0b5401c064811680b00300d081011030001d0095005c0c0b50040e041d80400058400d1400c01049984000880c25600501500008100054001d2003d56005181b00c400c0095000940000f072140e9400d404407102d4168020107001ca650350000b00c2c080080c1c140d0302140d0817110368000540d07050140000045c0103a01c000000340002e001001c840345c1060090030080383c0200030305030400c441e8110612400c0066994070400007480291560701d14641f204030402c11003001428000034040c4022000500810b4555000018080c0c034203107800380c140e20a204030301d119201460a01d4403a080307141040a030f5824000440e10020002c401c80f001ca8a058485e03600d00412a80d401e030561070010880e5500040b800c8000000c65444203e49214000075624002c071490001d801024031051404160103d580031b00140400d94030b50710483e250a5044141508200d4140c096440310a919003030400c1c184850701e21840030040c040c4c0c1003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 669568210 1250 669566960 669567001
    0xf08040608040201080a1a040b0406031e0b0114150307020c09090f071e03121e03140f0702030f090d080a02031306050705070513140f0a0c0305091e030c06 68
    0x400016440741ea0004c01aa47d15000b4030317011041d8004815042d150a601c40d0460780d8000d44041a055500d03100c0414801600758030400c1640710349001000c01c8140c40115024003248207003000340a1074031011491310b805442d0a100e10704400004200321900030000916000e100821665980c0b606002440d120aa040841402403041510205c2d110007070070910301c00c07000e00c800c030305a07410b02c1e60301c6403400d502d0815015801d10030070407500c40c074030240044010420003447d01c0120b15080110340c0c0408030b940080001840007030a8083c014600d0340482144c1c003009410b2070b01c6454100c400002610b500c0b0545000b007400b28001080d061140c2c003c406802c444640c01010307000c2c1580e646083d582842100c400400b1900401d20a01c0307a45030001207032181ca5038503a8005140808040d00e01c50309501610400036000b50a0100b00d6141c040740202c00c0c030030fa00d51500380702504142203942c1c0d0b214410908459010305401c02d1108407102041901c0700518000211002420800303120709456181f60f40 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 669569460 1250 669568210 669568217
    0x140702100f05040f032601140f0f030c040f0605060c1510150f030212040f05010501080a0f0602160f0c06021509060a0c0e0406030803090d140706090f08040608040201 73
    0x608a84610706204880c0300702e8100c4040c181d40001540c049071400743c0c2800415660a19038113803000a180c0d001c509018262607410b440c400d480200070003402c0902440721500c14000540040c000380c030080740200102d0710a580c0131508030406081c0c6405482c60740c200b03e805c4000410440c038840070020307003211a1700714101201c1030740c1c8415808000c410550701542881300440002510007a1194440081a140c280780050911013803140f400a181000e035070644005454030451810300500380f24107801007050600804104840e607030b8a6001030b4a258001e03020990104090680c0041c03a50300d621740c1179100c482d0107072081309440c00c07002e100081d015400040c403800301d6001e804c241411315035005238610802440546d840480440103040d88000e6007040214022124219445901400c00038500c511041900d920309a1542407a2840c0c01c1c844104001c4102600b01714848540102c9440d1030304000b010070b151250741030100300b0141c01800180b20003000540007560551125000d0700451003681c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 669570710 1250 669569460 669569471
    0x2180a090b1507050a0f0302030c07060201051512010e010908030a0e2a0a0f080a050f0c18040609080d05180a02030d0e030c0301020d0606020f0f0709090614070210 72
    0x11042412200c180101c2034009140c00c00020b98803040c80d0250036214441e00881d0100607440d80c0380110380210072030403409070344081540c030180502404a1000303800c1d00c0c4020031440c071b4104080300c08804607820322400391071300c400008000282900a01c580030745400090201302014541a1042d0380100c1d00018140d10f13001040205070400304543d80c000c48255101d410500321407031042c1c0c0080a242c640303a0321424524002903100886d0b40440e008240705c6000e01200c82c1241840d078280462000c10078103980241404400742e690300702c41c00c0c4400c10024500701c1c240d03031035140c094000e10031040302800c0401c01041d0310a10401a81141c1c0c49610052411152034204224807951811403000081d415000080c140c40840d118550b020401400201248c10010312003001c0380c00c99220f1090b49288640f1484184101a010030070303d05224060001803500c0a13088140c95100e10b03081c003800360925120b0103104180101d80d00988014014200c0707004487c11b118401958030a001c1d4100d9a4507800c04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 669571960 1250 669570710 669570719
    0x90a050d05120c22090b03010e011404080c03040b03091e1f021e0318071e090b010309020414070f0e03030304150e07090510050904150507110102180a 66
    0x7042900c20041d02a418040389880d6405002e000d13801c403400b200b5800400809090a19446010500040c0703e0320300c000031141c0d080e005150966079900041c42c0141e0406d1307500d9000541080103e58404e0300800740c2c545400d00c1741d11450541c4142d5001c09140310001c0300b4048014000302d1440c210f042541c1c80c204060840648071502c550000a84800d02c0a801204282e800c0c6039030001c0c0310903d00d01140101c20f5941403200361103a081520580708490141c2a008403680d0200402009045050203400c0103004000d0f5201d40310f405806100910b230344955244649900a810030310580754010002d100b003092146400003901c508960400000303e00f0a07500d00c1d01e60003401c500581900c050040c40c656940d0b45c440b022800e62221001c1c100e6aa01c8104c50710409041c840140a0210110041014140034004400549080d0045c0c0d104040d16010f00001551424040740084170164011a0702ea981080c240c613583c0f00f41e4004010341d40001034a0480201e00d9211280c1d50307004548001445488 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 669573210 1250 669571960 669571967
    0x21c1e090605031801240e0108031e07020415120c05040506060703320d2412031806092103210b03030403030e01080a1a100512090a050d 60
    0x840c0718510110710200045003409442d010b503810600c40e20000881d242040140e8202100011009415031101c1c0020600c40d00c8145070342d43c0d004003140710046090800ca0030642000e110392240403901002c0006101c821511142c101d650b0300f1411b401503680007941d4440803517414444102c03c40e008008104040340c986454401d19010f24409000c85003840d00030ba50549203a1080000445482e05151020500039005402e9130004d4442041d81c42d290320120305294240c996810180e240101d600c09100c010808100c41013040b22121090b440082c0214201560440c440395010800000130718004510300d9000300d9518210380005900d9240000c10902c061405000300c0d1000f030005003407007803001650b1884d0360000c08820b5942000501c9140070b400107450f540c06540200c1c00318200241e496115a0030040503980800c1010302485030384070a60031f084015044000c4284a0320600c9141c501c6544500c00341c03a950103000104130703c50305001803600d81d50f101d2002c04035694400c8550180e040b910 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 669574460 1250 669573210 669573227
    0xb130509070513110307021c081b0a17090706021506030604060213120c0614030405100c030e030d0e070510051602040b1909061703030402090403021c1e 67
    0x4a0201514190342408104024400340160080c1c0082e01c0c1c500742c1c50386028910066024104030b80003494080d258850480b803103031104235000c05104c2d05100b0001c14400c0600001001c0e00000c282c00d0741c0f402c051806071200c15a005200346170050300e400700120340d20002403090035900c03d43c0032115020610307400c08203e00001c6030700e240c05802900100740046c1c42c43d009014165803803500800f84a071940d260b44807412013841c0950703804490103010003841c0e410074504250707003056240091562038030751152079075003400d5090310410075a00c03050304500d0342c030961200d2191800001680d07912425541602d0242c401061034006d42d0007580d03000a42031505001c4500b201c10942c64240c14040f881500c98684d230310f44501a070708161914a081c0941e0303560000019411000302447d07840d40d00305400e034422500d480e005542c42202059800400d800b0010a0301d910507030440340002580e48600e005c0b8140138100341c07030381c0d4400e10007006013090540140d800110f0001084401d828119031800c200d80004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 669575710 1250 669574460 669574471
    0x61b1701121505151201020403110f0102030a1202040906030f110f0108070e01021905031c0b0307030b0a0b0306071d09011a1b03040b0a021b0f060310030609060b1305 73
    0x38091421504914650300190380c090b03a4600000314074901400420645c405140d000d68881e5400a0188104444046083e91340c1105070b50240c59a0380100000c3d540384900317444030301400b5a800300d443e5105000d4040700c01070301c08940280b04171075a0380303440501e03110a404102c07082c1da624104004d09003445090074880030416580c2084075161180143c422006601a440c114001c000c109000a40c441e40268000f911900040d44e031040c12841448004d00581104034400741080c1c10005030b9a80055036000b941c0c1c2080c0c1450554844400200040003079449080c0c1500900c010001c40c00c1d04903409000000c03140c0e420800604080040040d824424011070f108030b011541207040e410000005460300383d00e119a11413000340170441d11855134105501036025081d00254250040360f05000c0b1108010f12500d440399491034000002d80744040d407005142c0289004800240300b40c409440200c02584c00c40d400304243c0390301c0d05000011f801d21606050181d036603002c06941c1c0c101070b44107603413191 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 669576960 1250 669575710 669575723
    0x50f040b010b07030509060a0c05010507020d05030c090102190506040213020c1b04020d1b0e19050603041e0b1008060603070603020d0209090c0301030b0108120d0207061b170112 78
    0x1a82000c07000c1450f904869000c0c1c0800c041449010503e4407031200900203080940c03a044104a01440c2107425680001d00f09011074120515504034507401c20192034100b64100c40c003035210200700c0c0040385040e0044c10081c0c4060f41d043c40741400c3c0b00000c01c3c0ca5028a000f90f03000004e04201c145000103920a11900320020381c0803071300c05000709850495500301640700910161520010755001c209940c11031807807040c9401c1c10382920b014943c004061204600d810750301c081c50f9245452882c03419030520721a6078001c2c0c800200150030400110101c1c0088940703070078500701d00400e07030420402c40c4404681044c10306070306c80001b03e44440e000450600c03c1c20014021b0a009061120072400b9405c4103140c039640a03024040d016460b42c50359107540c03041e20102e0b245503c0b50300d10305201c2d510150603480400303142c020040082074440364508480c0840743c10ba01c0981e5070f080d90710f00030009000c01c03421003080042c410015910302d0f40c40040b0b40d6044040405480059803a1010072000d80c04251004008 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 669578210 1250 669576960 669576983
    0x31305240f071d0f090405010b010f0234050607050106061803021c0c050a06051c0203010e0f090a06021215060c0d0c0503070515101e0e0a1d10050f04 66
    0x4903203c074103403014620b0042d20308012010360324040b03084a041940c00700c4e60380e5101c020188413540d0102642d00c244800740700800c1d5600d22404144138180130400c81e91508603025240341c005000b000c1078800200300c050442503645001c2e040880c004c100f1402079400080d01c605c0843c00251341c3c080d000e401da0341c00420305441800c030b030507800315500c1f40c41004031080300c45214001096075074107a02030014001900d03841d90741c090980075039102d40154408100614070500c0107010104500204135480015409014000e881e00828035180132404040141005c0c000101101d40441007200b041c004c4d60494403c00d080e0740382c03604000c03080c002c4014408595024542031524184900d840c4140d05000b13030243da00d4130791a074a4050800e01e0b98145c0740c3c4200920800e0210700c0705d000007014020048035040e0545040b1865503095004170620807400d1241681e004135500e0f144660204415a094000f03142c018130501c0da020351100e4902a8403040e040c070701070000d01401c100021451040b5484000b8908 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 669579460 1250 669578210 669578237
    0x5070b0703080a0b0a09230a2a021c1e020604080904021e070c0314030c0d08070513060206010501020717030904020f0d0c030b0901120512031305240f07 67
    0x400344901503507446241c0410010b190086c03886501a11006802002100c0d40f40c2003144910080c06000807070403920742240c004180010740852a551101d581c0c0f92840c855071004202c1c5020380d2042c112888411901d44903554036080751810038041c086e88d20304500c1840786502643c840508aa0140000500b000075051714606a0300a00196145040600000b0440e4440720024cc00c0214101d4482802180034030a001211030b04000d40c030340000c010361800c101c010580d070711000d0200e9101c0034003103000045803005000f00141c8421402d018500807405039241030080d0303a010300784202405406801e4001c900300e00d084d61480c1c4101849030041d403411b240441800001d60062030a540380140c144032241800b001c60160840060159a010403815010070821000007010713071242c002d800e03203c24003000203100410310320a005181400c560b04d9030345000c0c1d04d030641c81c200c550080250062a50800c941d00806418802442203440e600d1001d0b51540d030909a82c090517038140d00402c0d80c102d004c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 669580710 1250 669579460 669579481
    0xb1c0f0501060e2d180903130816050d020f04020d090209060102010c1409010908100c02120a120b06040b120907060c1e0615060c0201030b06030709030b3105070b070308 74
    0x241d111402500f5030b08a004500c1c01000c42c45d209441000c1c450f00005aa01039100755641303440e01030075148001c0e00c0c5603140360003810011480751090b9030160580140c40da040d991204120a5500030241c0159034810b0710310b06510003070054550072807003000c851010403155441446900d0352980c0644a402c032200c00d5412040094200038034850400c000703000081002082440076403601001288003042d007040280c00a81802c03540d00401d0704111040c0040b109140c5d12030314000c011910007400203454040d080c0822450710035904981520b00d80002c42450600019607004e2103a21140700b0f942c6c2268030b8400c100d45010740288050014818a402802c458001c0d09200d01600e20640d4005180c00200f022808422600d52200011411030011907080d96054050400600030071a0600e1030f500d41008060102c0c80b144c000a80441100000501503071404200b01c815030703245000f50a41d01001c01c0708000d0000801900326503d00915200082554a800581d120701e40d0644401900d60348008280c03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 669581960 1250 669580710 669580789
    0xc150c100504060b030a050708070b030c030105090709030804060c2108010b130305060c0301030317010513020d060b1602100504080a020409061805060717100b1c0f0501060e 76
    0x503240e0780e913100040149990200151890300340f20313074050710400c7e1408130301a081040550002d100c086041080000750720b00340003100c1c103460302122814041e03101c2c5e4400b01c42000460f08014a00d610016010a0750b54009e122114071502c21007459862100440401000c00d00c0c544070032000c10340e4403005112900345100a80451289404c00e624419501d407141840c107033054400d00e10705900000103006055018040c00560451008000129494180845c40c40141c616026a0042c1d02258501100010350410390051076009811500c800756071019540d07000304e540e8100c3c07180440c9034100c0c186a0140003a241198180030140242000d190240405840f03180c6046802c1c0d039a45003607075090610201000f0985000d00d0040040745010b2401600c42400c414688003070001400802c2001070007052090142c030f121240c80c0b40c641c11181402100ca040d0391500c00e01c02410003080d0040d8011030740c462812280c150360344203220300d0034406200c603001c01c200e102d034805032005606019168540c2c003207 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 669583210 1250 669581960 669581963
    0x3130b0405030606101205070e011101021e030c2a0c0108010b161a070f030b121905030412210f0c11030708010c0804020910120618140c150c100504 65
    0x80c555500455122001f11030081f500032020500050100b01503503401340744400322220a2008600e88130031400500c20740341e20880305004400d00000094145441c80c002e0b2462800107201d001000340c42210800542110505945600d21802d03c650600b98400c9918504072007000c1d44407850250414400040c1072403910055411030001c20000c81e55070141c454941c4138a81e15034800c501100c1c0c62400509549041e21002d12407a04140000060600880c40f41240701400021102882e45c1e45042c81c114000c9901088034640007441c0d5005026010360341c10700b00c03d1081400104580301c608181d96084170780c01030741d00085814014200003207010f00031725000000141110206955002000d080d100680452400204510184411820185249504807003000800b03121141007030440002c080c000003000d04096101e211418a9110601c00100f201da00b01301640c01c13284084841301d60790f43c5040072450285000070344403000402c5850030f98a404928001170032801442c0b001e648003905003c3c00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 669584460 1250 669583210 669583217
    0x50903030f0301080d0806030d0e010e0f030a0c060f021908070203010b040204181a03190606180e0d0e060f0c030f04030c3b0c09030f03130b040503060610 68
    0x1a6241404480001c2c41c001d0290900074402080507400c02000b1503000341a083c0030340e00a03998508907640290803010000c60a10b041c00f07403c0c00d520300103280070091841c42c64040c02113910b84000c0c041e503519440140c840c03640ba0918481c080c1c0f44200e903503441ca50355803a841a4041400b40004441c9401807103450300013000803514925540c0064103d0b405030b444443c401d02d0111041c0d030007031030318094081603445a50901c0c124040e5000403035140c40d61520b282280795009010b644c2000540e9001101130a42005110300c842e6904030b00200900064146c541d02d40b2071443c207500702502c20354942d03101d80310107410282080030300340c282c491a4208061115075404140204041d412100000c3c0c80114041d4086011051a148900f000d80c1148010b50281e181b15480c050740003821003040071640b0050400d04a441ea90340440b501036030280c03181603503140c0140140300c15203040000140140300000a0600043c41d81c841040d00c1b18801c0384140c44d0107800c0a030008006141001d425006003c480c00c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 669585710 1250 669584460 669584467
    0x3090501050c010f0c02030c070b040b040e040c030b15210a030f110105090a0c08030403080702151b1015060206010b031005100f0909050408030417211902041505090303 74
    0x40c0c16080c5c445403a01c210059101040c1081d10780c1d000c00192004060307000c1c1c190700d0f00d070070411414603034400c500401000c002c164010408100c1000b9003e0002e541007044000c46013051503448040c00b1401c4c401601c070341181e060802c95540016001011221590024900700001707aa0a942520303891095805001107400105100002802481d220780c03000c1c1c0c00740800c0300051910b0102100c06800141440d402030005100044c40c200c1180c4220340c0468480030789615000d41406d145c8200b00c03648804150007140d910b103910000503e004201c00448090045a000c00c05640c9480220b200d19001644840010441440398a0007903801001410410400310f486002084aa00e17003e10114005503c0c5080704141c10b41c024a1100900315100703003400f03242040e4454209600010700054030300d0080781c80407045190804c0803606441482c1109030264851a405900701c1001242d41204108034281c4549250600b842100c081d40c08411044038144060310040310340750004480550148002c2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 669586960 1250 669585710 669585731
    0x114070803042d300207090c080603060c0706150e0f01090c0507020909011b09031b1a03100f0902040503010f09020a0e0c040b0d0617011506052b06150c03090501050c01 74
    0x20804002c500e0213980080503030f140341c030b40c1d14801c0b29175002c07800b401c1101c0c0e40b003401801d55007ca040c5070890741007008a52210600c0c02d0000041c0380b004a071003040c840c0000002450307105035030343c1c130301c070340c81c00c5081c01216aa111400f034252514100c03400d000640270084800107240a813502078000a034840002082e94445440e60200c19040b110140803981c40f1004104220503a065000d440511041c0f981d03920b840c0480703812101e1062815503007a01c0010001864042c0e06011400050154052080d401c596440340040298400e0150500075428003410042040c0c950040108040d800703443c405415260500c1a00340d0000940216192602004009100648100a042250b281c1c86001030b44038a0f003000c800b203a0800c000303c40c846034101119170154045058210301280ca10341842691000c1c0b07410b41941d00c1012140c3e035135601c0e2030101a501c1c415155402300040d2000c444100d00307a1400100c060f0f89980c142c0000400107460507109100e154841c0d409403500d900c2000c000308110090 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 669588210 1250 669586960 669587033
    0x61c080702090f160c03020d0c08090a0b0c1b130902060706050403031a030c0d15020d02040807050315090601212307050d030504090b0114070803042d 66
    0x1d8602150980301d0005104c100c8804203003d4a042080303082c50010445143d50294403500084207000c180000d007080c0c4405c2c05119402c0741c0301c00c1001402943d082e5110004403040b40c12081510001d403298407400c842d409028184480c2180c2c008129406024406103102e0240105000032604510240444000941c0500420740070b1071298030049014180f01091225030345142c2d0b0010702c80d51007030300f8080751074a645200d03004054020201245136a500c0616901a11800144c41242d030301c001400241c0c10300100b2000c2c15070b01d04605039420780d5191b202c00e04001d0000c1e80d003d0744a400007001006001c2440030984101d80e25000300034132800720364403003249001d01c0b01d180c24000501410301d210b4010f010300200024040442e804005400b00761001012406140284800b49946034101c200e9a030169031208a150340320440640c1e10800f40c90452801d8000742c50072101c001450ba20318480841d441408000c81503140b0740003910700403a40380c3c50410350490b4071031301c104440060b00da800d0110 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 669589460 1250 669588210 669588229
    0x1d01030e03070807120e1c2108010f060e060f250803090f062e09021c0608070b03160c060204091e0203010303140a050f0a0c1a061c080702 61
    0x60031a480e03d5003005e05186074004200c25254013000980c00d00721515a4803640303119010840c4124024545405190401e1401c04e4411188485007004002010307241e1b0041010703068402d003000d08004a0381c0c4010030351b0b042503445215a4000350502444000a070100007a00b50810201455000c4d2810308c00e01d8134800e080380314140c030030280020800907405002c108807082161100020400b034909001440c0c000d2410281170690001e02e0800d16020540070b400d81405040140130440d40c880d11800e079401107075000e00540d84a9824118005441c00011031088200d0750246405803440d40d0711400f80c5015003001282c4802d000001a246020a00034400347c0041c1000c920001204032003c0202492a82c8000c0901c24450042006200082e0310424005840f90042440b5440d2100b40c4803d84150040b40c58002900401043e0240502d81c40004d0011403801141c096103045640c05e114180352004845858002e81403c402000032260104540d80e42409030400038213050300741d0f0005a03980d4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 669590710 1250 669589460 669589463
    0x519050402042c0402061c0609020d0209090c0307170c31090b0607020427030201091a09060f130f0b0a0e0a0c0306020f461d01030e0307 60
    0x342d48410740fa01601110350844030076490b07010242c00c80d19203503001480c1343c8607040c44082040044051141c00103019003080340500784a02040d521400f150700924000c1d0010054144580e8142001c10303070b080881000c8038010492540e804030481c0c00407482402520003e0b01c0400a40c40401c01241c0340c44004a11032120f10010307080c0c48418140c05401a000c03501504025402d601e00003c40b0040d0303480f10308403810340c0c0e4107031000300d0500ca10140580c0c440a01100580076084a50004402c241d419842007011030b1042c01d01c101108011022840f600400b00c1d40c60206a0200c004210b4569a84401a6014101043c0002c0724101980c80300349420010004032440408042880b1144100b8040c2504d01c40d0b1200043c8500407181d111041403024502c070140c00c7c580c0c001201c801c0c004d00002121021a09003c00301e0174645003c5c160824511081d103a103014544101c0d030441c64801e1036020081c0000a07983e15080c0c41180e40840c10450b204040d844d0500d503a4601c80300340700340c3c24005448080e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 669591960 1250 669590710 669590729
    0x2151e2a060f010609080c040f0b090a1512080a030e0f16080c0102010c0f080a0603021e040e061017100501150908010203130602030a0b03100f0b040e0304051905040204 74
    0x60610b016103156107201a0002018403014131814411401c001402c01d0b0307806422940811080c15454841c801800e08000443d007000865080022011058100c41c600417601d01003500b010342e41c0c03100c1c03e8007045440720040001d102004810003a610903000004111802350590b40c0e14400c105605203002c0c0c10541c90050507805080030001900c05100041e0080d40c2030000b40004034400c0401402c41d04500516410310881d1008601c403140135170300c4500603540c054000700c00851405207081c542041a02d10350310460901c030106550800224145006485106c4121000750820707000c4004215083d0b041655489400007104c03000329036001d06e41c000c00c40d8109210030300c3c1c110500104041c1c4117805c01040e03a80108140160f280051039228101d80d004800180c490300c0d10140b88010304218003030075a01d481981d00441002c02e107580003080c2c11519000030408205103100340310075a1070120701041540c10610080040d428070200303d602c19041711503040c0e882c54640c0d00013030072600315070005003a1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 669593210 1250 669591960 669591973
    0x306031213060e06040323070b04090e060a0614060705190b0907060503040812040f051b011b0f030e030f01091b090510090b0103022502151e2a 63
    0x5543c0011928410481c251902d91815081d622074998004542903000c40000c601c9100456900b400c0c00309601900940c0412075440350344520943c09006145c07040030140c0980030120f003a040d000c0c8a82c46c110b50030494038146201c540700c00c100650300424400d640b18090070060f1043c10030501c051a4400d4414088544103042c1a00024034100550300603a060200070418040424980c0c0c0a44000b01006e107105030384d40c0d0720307480c000c0c01b07030029114001d119109040340d0300c203111400c11459185100a80c6c80b0388281240301900c5c1c10301030b91010040c10015080201202092189a40c0400d00c0d6000d800c94111090741c440c1142100ea588900380ca0811010700310b00104c005952100700100201041400307241064848280003c4481c45400b240c135654044000c0301e40d000c1d03015034200c5186022034100000c1e003e010b60786016600070f4100e2050805114155022030303042d09680c1030035407a410783d64000f100da40b80c56001e079201600d41c0c000441c800d0395088120081500c2c55504000b940003501c030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 669594460 1250 669593210 669593219
    0x51204060903021e0c0d1406040303050f09010b0112150506040e010311100e10021e011d03030709060516020a0305031909081213050907090303020c010804020a0306020306031213 78
    0x61000d0408580f113007100300c60f44c00610540000d0072010f5800102c501c2145443c1307a10341051240c01e5400500318601821017008141505075201c80d01ca84108a03580240341ea60230429800c03205c8144056000c52104441c032140302e0fa07a680041307800e4074450348030000076403604002803180d001644800c0861030b0800050041090b0f00e502c0405480c0309447c1d00d8200e20300d020380076021014841003336020b8400c050f40300414610030411442121050203407a09035500d00c2001038046c1540702920108005030310038200e01400000200da01c5450b5503030f24000c845080c00400c031910f03070003812481e240c880142c18080240e078403841c0c0d250055104030000c40d6a0340d4011500582d2060619a180a01120180c104a00480403441d41c3c1510b82c1380e809143d65403010104070402000b030380c110a4003c02c50000b0040100d0b0004103403400d82740070381c0880b00e00708816801144e02c0d10084070001e4006243d100e0070800100d041d00074681005004055440c0b40d0021580280b054000c262269045030b13000d5010803 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 669595710 1250 669594460 669594463
    0x30b040c12020a06111005130209010503070b090108100530010e0309041e0c080f090106050102071703190504090b010e060306010e1906021b032a0105120406090302 72
    0xc004002003412070003000d0060b000165180128450281441440005048201810310003118111072002c001c220038149009024001d4064503401c9004400c560000701d141e10300041c91104a60181c0095481c190514004607055000a0046d100c100340015010a903a6590040040041ca213801b00403a8545201441c0551a0130301904140c5649000c88a86440c1e034084126800740b441a140402d9150580000600140c81186003881503840c0011102d1419402140c40b40520620904180300b5140c00300441e003295514851140545e2003105d00b04500d00d11020905058030941050f00d041c2040010000c24189049407007500007880058103100008079031003103440d010304c00e19280c2501410200450442d10014295034180aa00180d40c50103503604100c82988902c003c100710001c0340da441e40039580b0400100e81142000010010b880c150270b00240c86010000d4138017079800601c802d598044100c030804c140c01410010100a86005803001420040c022881b406000500110b0b07800c009 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 669596960 1250 669595710 669595733
    0x114070f0302132d0308070b060a080a120c1505010f0f080709020702031207060506210a02040f15170f010207020a0e0601090302041d060612070e180106030b04 70
    0xe007418814030040c800f0810341c80b4080b003076516000311250b44030502c1100d0761241c07600f002d1241c41600c10800100403c21540c0c050030710507100301091a52911290200044801c1c0c500a42c4d480d0f512031011003005c43d44450b0350b81004c0220741000861051745440700d420722403190305c680001c107880e038004000f41030003154200010030034500c000700140d040418064031441148240c0312a070b6004150310703080d90303814000910411034648405070345152624003500580421500790b449000c036400701486a41840b44c561041c0281745001d402802d03256800c010050001030002030581e0b5a40740c0f42d44010038030544030800b0b40307a1140041401a44020348502c0c0000c03051590b0700c90390051044400503101c41c41c0c1003041d01d28803038507910941d4039040100c41002d4183d0010794058140000e0f08800459a00e24404107203000701500d015540b0141070004004000300303001c140b03a020010801441090408040d041741c40d80c07034444480109810141d0940d006030b08191801c810507000e000422001c62101d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 669598210 1250 669596960 669596987
    0xd0903031a060415030b150c0a150b060904051f0b04030605010f0b07300503010302190614071a0f0702150106050d0b1c050d030e280206040305011407 66
    0x2a02d414240106045021a0060040149030b19003014000e6607445070201c400c1541d40001590b1030300c2340d0500b040d40d00c1103042000d0302ca80105c040c040e0712219840c090260360a90140c44c0a10340112401030100030040107000c24444048d5440603100c0c0b50000b401d0f08010114042015100d50650400004592040c2c1c082000c0405404042203480b17000d2095a0400c0e0700804a200a803080e02d044100c142c0400002c03400c103811000010303858603041405581600d00a80d461b00b803000c0320713108a0140ca00e007400740e06e0119910500541540304030350300401c1d0315442481d501c441807242e079400111f070041c140c1c0d00901c079409203000c10040e19410000c1b0120010a50815411545070480280a80c800c444102a03071607100c45040c0c8180e01e8030b00700c10b2070f042c26a00c0d031101c3c469501d040c1140ca032110107803440c0009003003406c680b400c1e00b0005085000c080480e10030402d40d400b0780c04480031400b05804101d0300400c2c10b00002001c60001e210b9212583d6000d0151742c070915180c00e0003480300514200 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 669599460 1250 669598210 669598219
    0x1030506070e0f090f06150a0306140108102304020301031208060117240319170f160204090b0907030b010617070f090b160c0603020423060d0903031a 66
    0x14003d05030f65901481034110981c0224030032561a00130100d04000d494441c1c00c0356440700000c003624025459441441103480c403400c056042c1150000444811005079495040440e102c0414130403450030782a1400705000e10028000500400c001007000d90b0001d0744143d82203609407981880700c50300038075055403005007441e040d104419032030726034448620040c1080492242c41121001041041e844180601000078115205440c40d0050720180e6000503c2c121000c1c1d0300d01d031038000580100015a00e044049884541c10316403488500203c04840950a9a2084d211003015020841400c0168001c17400710000e0140982141000340d0300641c1a407065082000000c2a0350200c2c001c0c0c061b03290003944510701017905a011803001c48124405400c02c082074500000d401800642700c050311442103100e40c4040d441e41c4d80c1c940040d02280941d100d112030100840303400c82104031040c0542901c000000b0720140c2800805000031049480900d411404241d40780005403940b440c030341201c02003900465 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 669600710 1250 669599460 669599479
    0x5040f2c0a0f0305090d0b0702010e0106060c030309080412030c0b0702210904060b0310030b090109050304060f14070629031e070510051b15070813060501030506070e 73
    0x5031020355038607241d0009004004030440190800d84036000701e8003000030040c91200344c48134600b4004d2003100b060b00c1503070240d071910300c000319150010b01684003200c0c1d10b0340703d2014140c41a20250302074264007034200c80e0300900700030110b48014031070340480c2c4850017030340d581c0103028043c5015080000c0c0a00b4030003c0d5030011800c0360340400c0030280000106c007500522510b402c07a200100d03002d820240c000144401c0040f0801c200100502d54890440e0700039a40c1110300e0b260000c6003404c0394500c4801500c140c008210030300000b401603821078003030400fa140902c1240405030f440441c640103120f04070f85039038950358461503a0b004078944a40b0101c000d03400e098400d215100090383d07184500a00d030845002200780040529003400000000d0001070900181c1c1d100d5550010710079800f010007402da008803900c1003c40403400141c002c800441e040f0240071991100f240a40b10a42c00a02c040103d01552401c1000100b983c052039000710700c02c000410302800d1002c80a007600301d00c0c03031103280110240d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 669601960 1250 669600710 669600791
    0x105090109020d02070b07020319090b0706110f1c1113091a0405132d0303021b0316060c11100506150a0e031005071e050405040f 57
    0x290011411a02944001640d90104143e02d03000390240c001d000e4004d5500004200318250080010a48081603004402001c0e409882c1600c410409000e00713008101d0500c5100c00140b801d074011080c000074100110300301012803142c0d040300e501c28071060041200340c004c1c0c2070380e521560241141800f411140b50b810281d18603d5042202c0083c030404002da9101c40c50b01180541d0a080c1c0030021038090418491807a01c0c0c1165140c055032410203e402e80d51004200020b40f900d00e40706d80d5820360540ca04e8800c070105440840281d00420310110030201070349002200f1183c2000144100c4036000707042d000980040c2404011110010001c82c10b0010540014130116004964140b1604440b400090303c0d0300c03560041902d250b00c0341c110b88501c100004030520700e9600504507000809085044442c000c12004900d400e581050f541100410700c1c0c40c3c010150307551001c100941c0004c03180785c014107080e82c440015007580d17202c4060f0541d255854023030520140703901e1020242440b02c409060207410300d8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 669603210 1250 669601960 669601969
    0x6120e0604020d03110d0e0909010204050108040b07030b0a1701060803040b0d020c0709140121124d0106080a021507080307110f06012d0e16170105 65
    0x700024890800c001400303040501a802d81d50505500c80200c58140c1500c00b00600781e08003007807500e40b1505418001402146050080340c0035503030181c0d07910f00d103521140d03142d0581020242400b0185600e5124040b006d4481c2c2d801c0d14010300d005038015900f114000061401c4802070340110003280c0040100f48150300c041021960888500c2e0300043c0d40c0d000070301046050025030f0308181210342c00c0444032406440031080280c1642d2a0780f40001200084400307000324502034910051070020b0040721500c881e400340301c0021462044001000180e4041090f20000c141500c100013281030b4091140758003007240c040c200071003070038250080044506054141e580c60f441844024801c6e161b0744010280c035040c81c800d6511080c0e0048415480342880381010b80340701101c0e520b440d081d11503801c0400c5180d400181550480311900741005840610040d001506990340394643c80800121800141228041030340038403900500005161405031104010700350f00e00208a0384483c644a8014011a1359 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 669604316 1106 669603210 669603223
    0x14210a23271002131d250c150501090e0a08030a0b1c0c150c020a060305070c140124030b0c030612010f15051206010513180c06120e 58
    0x441c2d41c0a40c45480480341039004040c0e8004118a080d01c02400d480000c0356840c2003840000306888c0c09103030041507900c0d0200d09964000400c94074685200d0683ca000024000d05540141a00d4100d81c9020181103803141581c0c40c1d080076201d69a20b00f20b12100c02e442e11300c5503050740c1c1c103090250280b0154800c00b070717511101001d495510341c460382440200a50040c40c48480c0f84c2001b01c02c60040000410b07000a00505000803800328114506000c9440c0c2c41c440003213001904114421240074606400f400e0305403483e1001e000051980114a0307210f88004505900c81e660340740000d800c0c0c165022018060f520b00301000c0340390002c070381181000c582c1c001003190446580700c040c00048040b6400d00c4d02c56030801c100501c0b4919000d443c520540303034004008586450b60400311358000003c22400ca81e210504e0200f0000301e80c03c0150001800c000c10400c001041c1d01c54030b0a42c8800 = true := by decide +kernel

theorem cover : BRFrame.Cov 669424460 669604316 := by
  have h0 := BRFrame.cov_init 669424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 669424460 ≤ n) (h2 : n < 669604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
