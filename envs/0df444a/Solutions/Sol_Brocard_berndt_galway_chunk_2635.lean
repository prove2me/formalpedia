-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2635
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:17:45.454232+00:00
-- url     : https://prove2.me/submissions/67e0cf39-d723-4d9a-8a43-ac7435dbebd2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 473741007 ≤ n < 473920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 473742257 1250 473741007 473741017
    0xa0c12050a020a1d0108030a0206160e060f09040b0901030201020607180803040e1806130b040201170901053103030e07090507020709061e030213020c03390c06 70
    0x81080700c00400103900411210040c0783c02091030f4442104424418040342240b584c0105400c4009520703152018030000d444100241440d10308003000980729101c684a08062040300d00003d018941d04c848200303540b1165403042c070285000300d0038403405000c1d81c504021581e048a4041c0c018010075516070008544c1c038207226088400c0c0d0604080080740080040003d0b001412560b028101c240c01c0200c0701e21400c3d076074003503a0201356004200b0007491446034190301c810140e1052090103c4d80391840161008020008150703005010303042081100d08054100b540100300d0409002a110900c409440041e11880050310444040312500d0002a202e0b82c8003440b502c40c05400d8808542c0c40300d88200545405842d203000590080c001401210708a1149000900f0084c00c0f582001841c0d41c140350074580a80301c06032081510940b0ba900565181e01211641c0c000481641c0e030311485500044400c00620f285244038103260340da40c8440a420000451400c1e080c1c0b4001c1081500800402a1580c89 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 473743507 1250 473742257 473742263
    0xd0c0b0318030d0212090d0903020d110d05010f050702031303080d02070818030d111c03020c03160b1b12061804050109050c010305100501030911030d090e01080a0c12 73
    0x1924000081c9600a10243c141d0441c1c0c0900560b44110607449503040040103082036600703400515401440c10f4000c19504c0450b070b0305a8041d40e40c01418240414602c84100300d8980040c1c1c048003400c100070041d4015a52114504810426500c030100200c2e42d0f40213001d0100f030f1044550100307102080080c00500700000e1100c03030143c078102c1c0c030b035880045540200c0802c3c0180c0b007840051080e0b5107001e2203a0416440d0303924022803510710126030640d403000b10391200d0881c0020301200e04006c81c1309030101c403000361070340040300c0c0e403041407042661507030b00035071020350340040800d000c25030764001d0080712814200b0858156040c10401440c81d03020582c05040c070343e4010329600201e1045100c10083c40e206600607400007a842c07589050031401d040710712442c5410540346c4010460315103001482e06c02915000e00c0c00050f0200c1515180c41d1200000742c403140d0500c600281c010a15034000031403000c1e1000e00c200d518069071b035104025a03071043c80340002d0001c0c07100d81c4240014010442c8005103540 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 473744757 1250 473743507 473743531
    0xc03021203070e1c0f0b0103060b150904020a02070b0307091e08150702012304021c02130c120515010f050408030906030a1b030b010f021605120307080d0203060a050d0c0b03 76
    0x1c3c00d562003081c1c0d03d40321710040700e0190340a40104203101c15481801e82420301602d0a40f2503900001c4828400d200d01c039140392142d13030f02160510200e4402c101d02e0019142d00d0b400c1e2907803414103180c060400c446c94441e40781d007460412000041c0e6100050400704941d603d40003070256811801801d0074401e0001d04400c2151360351141e4a00c841441200304800c400c1c41a044007030b50910303006000420344420070000300484101c01c010b00607101d4515100d19141c0d01d46000400711080d100403a2035032043da00003a100c5041c5414000d01d400318024088506800740c9401c00c6210508030183c58a018030b209a078030329041408400064101007004641c8090003d81c0010382a14407060781206034001c3c520900020381d40c4294a5695130480d0300701d0300001490004110200c440d4036402000011401040e000b03007207224409031003080406c20340c2d4a141c3d0102d042c5450b810189800c40094004540441c8030b11071010700054603041c40500d48041d83c0d00003500c545d4142c2041200c08580c0c2c00500038103000b01c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 473746007 1250 473744757 473744809
    0x1606170f090f030a0e090702030306010e09100302060309010f050601110303010b03072007060f0e0303030a02070614091f050103110108040201260f01050a0501091806030c060c03021203070e 83
    0xc0b4041c8002c1c0070b007490f00d0702c50003810100b000c1480107654005260b9015540300700140000b80c0e820095041000d1812264031b80381d0340d50762010090084140d03000a40103035001c01030080244044d00f1404602c0c02d100020000381d0394074401120145017140c03000c12150020401803224805410041d80c0c000594100710b150081280003040c8100c1030780b0120fa00b00e800201d1b0034848141d00503440d20301c45d040c074980442c11158030f50000f41c0b20321002c0d006030440307580002c07104100555038000120308071131400d00185d00c1c41c00080381900c624601c0c8026107080400400500d0400c403900c100c0703060b2a0042c40c050f0310500a900103590941d40544180d050002c2050503116100c40041c411482d8003c11002403d02d04045007200d1355401c060300081d104440407102800541d82c80001c00c0120b03011010503160a65a8070b4550700145519040503042c08000c0c00007165494002e180000150312030303421100b4201704081c0b0042e6030701054401c0000614400e04501d001d01c2c00500203201079800100d07100c049 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 473747257 1250 473746007 473746033
    0x41d0c18072d050a0201050a11090d060605040e0706020d0f090603051e011401081b03220b07030e0d09050a1701230105031608070302040e0114091606170f09 69
    0x918802c1e111200000da000400c1c268031170703080c029260043d090072414445114900306561351400703401c50075405141d41951950038081507030001d00040c580078000700446646a14401d0301c2d014103005110252003050341c01c0605521804003030004c071a0300e5580c05142c40c10b207082200030b00b601030b080c402da600c000000301d0480c0348040076450007400c5400803031074000d00c0c850004d00b4420000b01509850740401c00c01c0311071a800607089a600c07003407449515035100a01900c110800c0749980300a001d4800c440d00300b01040307805910101458811500b00d03000c000c0c0b13015045403405182c0c0541900060b100340200b01c10401c050b41c0d45200540300e0700204220343c88201000121a0401c00d070005508040010001c40c10b0600259408403252000304c26402d0a060f0183e64a800ba40320007070103a542d407002080012070a50140c001c2008150742d003541824004007050340c0d422043c0740001c803034250141c0000c046014030424071003001031210120480c1e035168041c144078000204505407030701411402802c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 473748507 1250 473747257 473747327
    0x1602040507050d0e0c0a061b06020a02060a0f05100e0c270f010221072f12161a2503030c030b0d140705041d0c1807 51
    0x801c0046645450300c4940051841055801c0d0000c4060503030092264a0f465841c3c44680380d0136990310307061411301d10140ca088400700e45241000600818404100d00000d01d80c0802c0b607034002c0040090510042603e0090802201e07800d8540b07110110f00882d00f005100d4901a00c0380d80501e40c80d01f034500b0b090041d440500d04220501608180150050341c4004510306041c201f02003030000e00c01006d04030a414030840d00701a4003c2260500310010486804100110044d091488480012601511856104480e800041390308031031084244000000600c0c0000605001000ba607015500c0d81d1441d081a80b05420082003030000311100812070b20708800f0120500341c94140c88030704801c040781101d060080458104403c00b00425080042100d816911005041380326030708144011f034094045a1410321345580d55108503042814404015030340c07001110326400c1904102e007961038001c610801c008500c0064030005541d140010003041c400761103000c00f20103044d0740400204156501802c1109 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 473749757 1250 473748507 473748511
    0x14040803070507271e020f0c06220b100308040e04051002130e13050d02030c010b06030424020c0714120c060a050c07090501030f0308070507021516020405 68
    0x499500005003041000b1040004200501841c1c800c0303003100344c1400c2c0100c11603e00b00b40c1c0c8004141c8549210300c4440601c0b42d0001c08940040c000c668400d1100802e0b00a40c00010b4441420300a0500282d2084550601e44003285840ea94031081500a0341d103400710001c000d011103404031f2025030040002078601c8000c1010386401d81f0b0880d2545040c0c58818603080460580c05030950041c800003014030742c503c000e40305881d0001616002c66407810744a9426004402001d03001d0b21940c4120790b90990080005c0c482010182c3c000c0c403d50300850305001161006660007420108001103c103d01c0d01680b070f0b031041d191a0220701515140440f0141d5140c18001e420a0401d41c5405c0c1001c800c5107025403001d15041890409007117544518400034000d030203030002c424240040046e0351504540705102c2d210203007090400802140d612420103e03d442c2080b00118041802c586c003240c016070003070703054426241c1d0040c00f13415000380d180b4440c100785e006050b0385450060031801200041c1d549000d118 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 473751007 1250 473749757 473749769
    0x1119030603052e05090307021e0f1f031e06030501050a05010519150e03120910050f070609020d20031b010509090702160f0e0105010e0d020d031404 65
    0x411018110b003055420501c5450310398000305100e03400c10001c030002ea190034841c100400350001c1d03607036640e1110a003944601c1701d0080d0f11030300000885901503214138120381660400e490a1280703200170820320058a11300341001c084c60050b21020b910741480b0390085004056141110a007560301d0004003420358000d50011506039464030304011407809280b041c0782c0100001c4490b40f61032640841200003952544c000d54005e91364101081241c1401590039148280000e0120390444912001c84042c540100d280d0710b10608980c00c402d460340b481070081d21540c12140010078584060707580c624004149410040360040c040403d800007284880c40540cbc5883c0303c4004610f8a21502d5040600340240807500e14201c0c440d001e0307103054a90b03011040c1c2c2c03145101520700c4145920341503402e030300e0012111100c200441e900c0b41d02040d031508079414107085580d4841910100e90700c0340010b40b400d00c8511142074018411913601d10144c5403840c0c043c0d200c107000e0305140f001c42c5106800100580e1142e0090 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 473752257 1250 473751007 473751011
    0xf0f0f05011a0d02010e0f060f0406080103060506030606330a020309040e030310120602130b0706050f070807031d030301090b120a030905100210020a0c020108130203030d111903 78
    0x1c0d03400c103003900408080041110f246509154680c0042e0904040400460040e0400701d40c0c011079488040c219002d200c440c3c118107440e2991411b0050540e01c00740000c40344542441c01284140c100042c4403070046000402c003c48017102150383d0807620503003d02c40c104000b13105404201244101004190260f05a0f018603a500da01e8000d0005403080300000301d5859104008010b00341165000d210103480d43e00f000c062102e007444c2880c0b030180c05804080328541040400c0040d05035801001412254482c01050200c4e50310b01800088030141213035030030003003001100001c0704a4443d600408103066000300e030709011400080c42c186950002d0304800e10a40e6111160102460501003800105c9130400040100b00f42e2950000c0c0287c04501c5410300803c07402d12260b200d14024405030458254920007192100d01e42080105100c4007050140d000c80c0340070000ca100c032411512007400280d0040e005614043c1c541e00c40c64010240c840c0074844042003882201521001d0303002d400e0107091260740c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 473753507 1250 473752257 473752271
    0x90a0803010f0e06030f0309100306030206180918120705210306030114010b0711120102120f0901020c0c061e0403060603030e06041d070c1407080d020f0a0f0f0f0501 73
    0x40c800c0562005807100384286d00aaa00311140100042190001d141c00c0d2542c1200b26211030041d00030707220940000790701820101c1c0f60720f40b100201c00000b1807910102c928030700c903498000e0741c00c041000306080019290400f500c1200f00d420568001d0400512032001ca030740c0000c0c403400c10f0041d500042d15298403c1c8001080c0b0000c1e28007402556290002c03280d420301039515180e440d403030305e129841008000402161000026580e16503811031943c2550000b95607a1210844091128000321030a5190500130408507540700014804c1c0e885001c1d09200400c407039050360040021036003210000302d40800301d800d078181c298070401020340010f52140c000450139606514000c2c1084c000715440901820062108010480000d00307005442250700a5075080c641350309204031101d682c44c0b03202901400809204084a1500280c030001300c81c4110107994103440c0701e8004a03260100b42c2403270a0154440d480d910041100d400d01c1c2da00c8103100d0f030921010200382d84e6402850103850b00301074440381d6417059 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 473754757 1250 473753507 473753519
    0x5070903051515012604060204081e12032a0c0f060f0105040908030112150207030f2a020f0f04090b1501090f06080a1e02090307050406050f0108090a0803010f 70
    0x1c060705500c0017420468080c0340305004454400014101102802407401e0100741030029036411100079166610903221200c1a1103d01c01039121765400340012481070000340c500000440c000e49000708030300d462070044090100080c1c1d40c4401f0518100c0d10340c100403c0400307280740042042c10b158070902d6001d000c0924001d68000f0081c0c10582c400340c0202c2c1403001500005505600302c03410b40b60108181050804241041d0003040d29501039080d01c0c83c40082c9030300074107400108801450815585041c02d500072540c2c00c0c1404600000010f0040d0000741040e0700601d0801044e0308041805014401981003220005042e0ba100e1081030b60100c2410060000912800401458406080c01d1841c0702c82d28048044800f1009440707520201f019000104052400540000640e04100c0000d0b011070f841c0c8005100007540100c9540f0700c244076401e8000340e41e01301401020101c44004041e900444410001522148001418658940a4a10344d03000190801c400365010340400b8850034100d9003010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 473756007 1250 473754757 473754781
    0x303050105060f09090406150b030f100602100902030109080406080f0702060906072a0602030a1401080d11031b0d0801090213031e050a05010b0916050706050709030515 74
    0x81c000740d000304000c00c2006410b0307100c202160102c0f94107070380c00d0105603034500b8140020000311003800701c051000080001c4040b5110055801012088801c11158807001e00940a1051364811600560041c8800c160341003420703485035520500140010032000401d650700300141d803007604400086416034082c8202c0002e401800c507070005c44c1e0b00080a079801c01c440140d41d1900c00034805e40c2088009803001c800303280c00400700300440743c041c214038407400801d2401c50b010b50000c550100c10f031440e1405441c41441c200e0725550403142c4039000b40182004100741141c0c805e104001080f0988410480c071404421100c00a4074840c128502804060703200c408004c00c00d60040c0e00c09a001c81c0148408040380303640c2004401241c0d0300004550021860074091144800c0140d00a82640140d008140602c135040d0400d04a40c00225040c1040e030762070602d5100e55406528401d00014000c1c014030b800036805503c02034228905082020409075a0b80c2c95038904200014501c10050986051040d944521 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 473757257 1250 473756007 473756009
    0x110d0b01090b030103020f0d06022a01060b0f0307031523100813020301111c060b0a09030b091207061a010302090f0409060b030a0c15031512060f0e070303030501 71
    0xd1070a040e0540c82d2001100460006000c041d110350200741105105541d140005000f9030750040040d5192500c86c103a07003080441640f02c01c04217041012090100f0362061203070780165030f031520907641004a1544004c080b41c00c0101130740705240d5540044440c401c0842e800f44000c040029007a8048007000780801c42c1d030002c84400e507000b0b60f15412117806243d0400441a03000f14045041d807100302c0d10340002800742c551001000703420b050004100140d6034028000c5040c1b5206c040c402e000059550010f00200d105e400025400582c4401c41030000800119500390000d0304541114000c0d41d0b5000c240c1000d62008900312030055407031040100195032800c3c182d509038024207085040c080c99002042002a6184255204e240d0300d10b0810200301d8198401d940800303002d0100c840c540f08034030300040c1504150284840940b4891140c0340700500c203010b0961210400043c5040261401070415210000d00008031450784d114080d18070301c88454401c000216000000401c0a03924505001d01180c0701 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 473758507 1250 473757257 473757259
    0x1112010e045610031a0103021c0c0e2706060109051201020d2309010207080406110a0f081b0f030304080906070b01080a0210021528110d0b 61
    0x1c8500342c51054042c0ba5019510102094001810a0809145490007620501010403018600c801e2110b002c40102c00501900e2050512014082041d191078800080c248030003984040c2e0315800c071840c034800709c52480e031281c8200c020851158590402d035001030000c403a030290a0aa08240307000c05484004179000031300071b050190a2508040c400240404418083d080c01600ca800662105950950403500015588035040100c5e503000d1003030580400d0201210800f02d030417400409e80800044c801c44140c80d6101406070700e020314000c01500c01d158004804c0505006020201d004251103c0f01a00c0507403250740c00c4d43d40c6070340036105050358202200e000519540401c00c014607602001080760b801a40200340162201401030000e84180310300d0000a2100b03002500006d584a0b001815a204074401c480d8006000110700049a03a0310150213600384000186000c17800d81d065900129003214441403454502c032118071700500c180e80c111049000c4e481c02c006440d60140f60f45205507104d03104 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 473759757 1250 473758507 473758553
    0x6040b040b031e0f250621050c0903010e06100b04030302030d1a06160308011418070e04090c030506010b031e070c06110d0605150d1112010e04 63
    0x8219021a90707590424204a02080305544450120201013115101c081c071040d0850300001c0c02002e000211400c4025200e021045d200d00104080d4041c00c0b0140560780d556010580044000312040050000030b001100b60900070040c08089031401c0c000c900c151400c1c08014825400c2051105480426503803240e1141c040c10721003840021350100480300c41d8011048041004c801c024001c1510304000d44a03184e2090340042c0c4844485070915100300401c1c029243c81026a0340d03111001222480003084960020b81d070000040c440c43c0004031035030000314074a06040b00c8011240818102c4040b2030301174880c1c00281000704100030701000070501400b4100541800d50405c078400301907010050060741e90305440280020b02103486142d03c8140a50010402e01816410b03402c64200caa100080720ba25142c1844004a82070400401181010600d00c2e0030515142540c00d90744024140031004001c110002c100a800390884010168045c03c60306141104500b0186441c400d401c08810f03140700410 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 473761007 1250 473759757 473759771
    0x30c050606030d0f0e03160602100507090b1c06090204120c12020904240f1e0608100903030f090c0602160501080408030402180f1e060f061e07080306040b04 69
    0x3644080d00402e01044d80c10140701c50410400002d003810032807841d6410440040c800020703900e50000c0c030114070145c00c01c03042010b92140c0e00100c8980c0d080b8015107000b800108442d109030075020424480c01400400c0014800b40c07500001e00990380182d008000d0658050800028040ca41051400a00503d01845100350f855804140e500d03800030009461007031610b0060081300307011400d0140100050008200015211000704001c0c0703e151055202d501400080d441c02481603c1904c0030344d21118010000e0842402000000e015030800480405403502c000c0c3c1e0404225000300c0740001d21840105080e1400c121000f41742c07140074000b580070f44c401040e080250343d030000d00c1c07247c03c190000d00c0359550382d56a0011503240c080c51900345400187c86001c006c000e03d9080d200341e0180150100101c000d0000200e85a907410090350056400400140012864a0030100800b20800301e070740d20b0151419450340c010713900e4220603000e4403180f038000100003041c5482e10601c070005900b110100280 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 473762257 1250 473761007 473761033
    0x10501080c03301e0a09030309060c050a12030e10060617040c05010c1e0501061e030b0c07030309021201141308090103050403030f11130608090a030f050d0504030c05060603 76
    0x3d9042d8203058040700000183c2c1c01c00318221910308011103061407400130b940c3c402c08007005001011601c400e0f03000030081078011030030500c0340d00b2803280a500301c2d0040c20301c8103940d20380641c80c200540106080c0b60f83c40501110146d000d10041621034101003001504503d00b840c00781034449001090604c0d000c58030100800038200031050710030b076102860b2410400401c0d00c4d00c590910900d20850780c00004c0318190310b081000540060040e106001c8081c800304100c2200664511944c0c0802880140d203040060810080c2c0707805084650b020389800704070503001d90045445500b880c1294043d59450392a210f10038104003482d0341d00180348c8841801c81842d25295185031b4064504168101501c6d03002103428188213400810741c50400340c1040022001c199800790066110768603044110400003400508603018110191003600d40720701405810000e903604a0794205501c004109101e018400041c0025840c0700c2c4900c114403913145d6034842245030034a5460004002c01c49403090781f08006204c01c03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 473763507 1250 473762257 473762323
    0x405120403150515150304060f0509030405220e030406020d0f1e0306090204080325020d080708040803042d030c060e0a03020405090a03080a060302090c0309030c010501080c03 77
    0x2145020340400a03031500d4031203145070004c2581d2041382d40070203015810052220701000560050740b160f40d04001c9038000450820541e88119610b24640e0806d200030071203400c160650030007503500c8c540400310780d030903044c845001c0318000800d030030055001080900015404000072100305810741824136240d904600002c00d01900390548800c005489850010b4680c0284c1015000d050154810b544860f10340303c10903540d400101880700c0b640f80d8008141ea10ba410403c483c1d0026070054600078030383c106034490b900158024202101e40c80001c00000952101c10310141000d800f0406503150400d8003101c07603101e55907003800010f0010300380b1a8204001020500c49038201d07038150503c0340725503040000240d981000c50b48040e4100e4208410010060008520100c00b24403075250026031351280e0350b03420221010b9020080d005481800400d640c480540f000d076900011000803603103010400b208031801d5070030a0380080d0095010302213100840ca0188903072010b88640c1c0709140c0c45120404e0383d12030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 473764757 1250 473763507 473763533
    0x3051e030a0e01120c050a020c06190c0807060e06010f051002070504050a0e0a0f02090f0705030a0209040e0d09090c0e030601120201020a0f081213110f011b0b0405120403 75
    0x81030002d4000e41140c2d82c1d0061007a80d81d005004c820412542c001080c0c05403190b44190038610040c020444400c11514207a0f0503504500139800d03800340840e00464003660f00c14000c00055403280c205006960004000380105682e020f4034501608080d49001c01c0d150b08000e01c0d070401d52061116481c1c0500d11540002c12000300c1c4d10444001c41e142e1500000341e001005908001c2240e802001d0200090001c00920140d480c0e1081d100315150382c1e5452401c0e00b0f24401607440710f001602c00c001040d41204035801400c0d0365080103000184060072426014644441c11618502150485000304400c0034a44581b200f11365040c240030104182a800003070301c07080140143c0050065002141c02564401c00c12100115030000d80b603a1414101e052081c22074122804d006403101411000130101a00e000600d100c2c298401d41d40c142801c0a8000c002e120803002040b01d04104e0b071903da40000580310044550043d004140803451802c0c6400c0203030514102003402c0552a408010400024115841c0c2c14 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 473766007 1250 473764757 473764777
    0x6030c070b0601120f020909220b1506030702210306030703020105071b0e040c14010c0303050a0b10050a0905030f0706050304050c0d0c09051612020a12090501050103051e03 76
    0x70340c50340e940600590f182c1001c0c903e05800140b5001c0000c280502c9503001f051032820454481c0c40655903100355000d1010011b0b8001d2040e81d114a80380000343c0482c0070140c04c140a0700d80030120718200004500950001c13030707040340143d100c412000c5260300e41034140305205440b01c425615516255020940d142907e10000303041001c0001d852062010714080e20414040d05a0200e4109580d035050181891050b10180c1c0e0081c01400001249007000c0b402c0800943c060311404480d58141c0c5054004110042048c131107582c45042d042d10a0396425401c00ca00c08250301c40c0754031440302400c000c19152094200c0c42c020350150f20700300700f6406e000924204403040b0b171404503541c2e0f03070f00d03c0d01d1800c1c4a6500b0501da080041c0e2842d860402410a206205642d002d580411440d82c9180b07100d51524483e40e815030114641a070f581c200c68150342c00410b00700d1000d040c0b40003512000c001d40000ca403071140c0240c074180d40d1880103204100b000c4c0075030015000d4107103035106487c1c10002210b80700d03c1000c201d6 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 473767257 1250 473766007 473766023
    0x13051506070515160906030504170304030302090a0b040f0906240507060501030803192906120a051806190b0d14280302100f0209120c03010b06030c07 66
    0x100c20402e04220848040c1580b004400e1141403800e1840041c00c142d0b864040450000d040108500d480791040f0352049403c031010018071551458a008140d00c040d0044d002c041c0c0030040c421064650860b44401810b101124968540c60b12220b840d12038400c0d0440d10006040107020003048019020120010341c0111b0004502c111194050300c1501c15038030014199400c020002091061441c051807280c1541121002c43d0b5900b080700300b08480304001429038584080c4580a2001e8406041001a1101814003460800203260040c0402405c594001c0126210030820404001440002500f81c1c130080c01007a02c0d0902401031412604081c600300070590f42c81c60100340954400b1040300c0b000707420410354031500540c20012502c50507610b106c0c05d414171030f043d64040d401c10004080c0080e150194058416440b41e840d503c1e01030845030711301e050349680034002c4003001e81d06c0550720401d507040b002c01003c40c48040c6e41803600356041c4003072051103000140200020710107070204840500b0745c01800 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 473768507 1250 473767257 473767267
    0x70e040803060d1707020411030708040b1008120315060a02030708090604030f0f05070807082d03131d04020a120312020a030605090c07230307080d0b13051506 70
    0x3083c441d141e9501c004d001d580090b50113501400c80000102a92402600c05001800d02c01038070308a20300c025148000041d85060024000c501071203041ca0300031141c07100564840b659403100c545010300380084405004000800e03c4007030300c10090b81c01c0101c607040c2d03011390500385c000348082d40724020b0f198050040e01c000108103500769910300448001c1c50340641d101004d18043e040ca02040031780150110360b180716480000c200d01c000056503004903001c480041c90074900c01300b01425840307100403101e50714413040702840c0503086003840a030411580104240f05160710306941042101c0780c0c15400c2d08909402801d04c03000d82c48500308001aa0030a441245a8043c5441e045508038010130a00180c0c5201042054015906400c05421602c044401840c079803907541184e405846400300c01400202040041058660814080401c42c0d0528094900b0320320a074640e04495072002c11410134039955036551307090f41d02d400d0704020248501c54404021901e012400c1008500021451306d03c40e160203e5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 473769757 1250 473768507 473768509
    0x80d17040321060806070503180f070b0c01020c06011502150c0a050a0e0901030309080f011b0e0a0305160e01091e020c071806050108070c05210706020304140609070e04080306 77
    0x1044001382001c070111101d919145000408640040c5c0e1b030000002051001850032443c0041c801e561200700b80054111145040d03208095548611a4049155000e21181d01d06500034001d8600912000030b51140c03071100b018009082007000180c1001c003035099810302c440340000f4015500014114200644e41d20090001501d00e00c006600302a4003019403c004410103078020b0020046507804022110007818101a240c240d8030250b403603101000e110135122001d2841103c403140031090107407003145003c0e207130348580d810b0004001d4038043d02042d00c0c0007000444511076a141c01002949030802070110300c08403084840144580042d40942c0101c0d107a48108014046a402044030f20405034030494024461809884103100d0f6034041980e400008242d180640303400098542d105002d0001d100b20541c40907207150400f07030484e40c604018040907000440c58030003940918042c00c200c10402010007010361070000003c00280c400d0300111383c00c1007200207121090f90450381c4580315a807a641e40038 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 473771007 1250 473769757 473769761
    0x41a24010908030a02101d0a08070f0b090a02090709140411040f0306320f0907030206031f08030c0a03050c0115030c060f05041412011104080d17040321 67
    0x6040b0300b64034000080c5100d0100d800240c4d8418030a9500401d001000103041409040d10007200980c5840d002341c3d0403240010803038001003081a10502c03214104002d01d840d44030484508a0f100c103541d9003e1660b01d02540f034002e03c807942c4881d603850640c02d86400c04106000380b001000d4520702a640b0340070762410032000c03042502c001d003000200e403c1d209079903424180040e10740d80213400c1141c07041d0450000291240401011050b07054481d03014252138002803540c014000511014060282007804001655400d004500868440400c0610703500c500300c9004014070540c0c4100001c1d0310030000085038540208100d0051038041c01d05a45443c024035659000d009894414480410801c00200c1009207075040c0070162080c81d940d400401e03141a07400e90f85c91242d03000e02c440c0c0f0790b2001c6001403a8a480c50000013625079000002c10480c040f03000703205068100d5003024103203402004848450a600403508401e03098400001486030501d40c038090240035205081c040781445494100604040030303 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 473772257 1250 473771007 473771009
    0x313050a15030218120a2901060c060603060c090503010f0e0c060a0e120f0d0305041a0c071a09100216030f05040806040c23090115090503060f041a240109 68
    0x10700101d41d03031740030284d0482c0c1b102d0088100712a0000c215005104074101c0c920302e641004100750401a0316403d00070280c4128864000880300d00780c61f400084001a0b5030f000c1c4540344107054548820440c100810507003503600f00d051204020780b03008000a842c4d403000803030b60329045d000da40480e661003501008445c2250351030505a000112888500d4102c40c00007a4842000300c0e40003070b01c4001000c14030480940740c0645c1c015019210071840e45e42c14480281255400c40501001b6501d00354581d520445400c3c115804500d02c40f41d00001c2041240303052001c1c004040820740c04600d003800c040d900d41d0844860348405000c00c0032000030b1555a502400407100503166000844075a0315291808001c4008240110340204146003800d08103d8601104980902d0006016400030f07800c004c551484110f14950310001c00510f40b000040c262024041c0720b00a0398071040ca00090715081c00c1c0200d8513115110b442c002c0c1c0388074008002407034081c007102400140010f503040940d103940000407100325880f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 473773507 1250 473772257 473772259
    0x60f0a0e1e100606140909071b0c03020108010504090803010e0a06030f050102070215090102030d05150a0602010e0606220902010c0b1e01080304060210150e04050313050a15030218 79
    0x4440000035907018001094690784036201d0080c062103481e0041191410382c1c40c4003280c1c0d1010113200c604c445140101c4441e0340301e0a40c1c50b00203552210b24111014003a0079100949158408020034001e40d688400c415000d008140c506010001444d51101581d100500c00c2d0002c80c00c002000c00c00e640c0c060381100340115000410019201c480b414914000e41c84228101e225401d6102d4010100003e4420343d0180b02058002d0342c00c0c8492410460050035008100c2d5001045010144009960305003200e80030b4001ca0b4000280e181c21038240c3c0d45001030251403640f1554074040000804240c03104109602440d190303011038070b49030310310050300c001c0305c10a4020038500022040058100c09030030040b00c00002e8080c2484d450741d0f20b1064588070721580c0500401078110360b0030b03101e5205503900711030801d212401c0070b44085036a4004c0c17030704400c1d0242c500711842e0f0000104500d40d21071103001400645000c552031030409180c0300c18440700d12011950041810380108840d104008031070850381c0b070808 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 473774757 1250 473773507 473773543
    0x110c070b040f09060b1902010905071712031501051309060902070506060d020108130f05010213050a0b0405010504052107030305041706090a0311031b01020714060f0a0e 74
    0x519020000c0c0d2a8016001d20707801c034020b01000050784609405983c1c11102074440380341c81e00e40070300342c41011402e1080102e4255900c40c00b050340041c00410034500200204281d12244c400035030348540c100b14070202880d81401c401c0c0203102c240106031400d030761410000d0900a40d1825051040c2080f02400d900c40c180303c52034841c0004000c000c5800811900f0b2061003901c4450b170381c3d8002c1000b580354070403010380041c030340c1000902c040150007403000469016001c40c0b40e51034910b680d1907013664410403054070380c070202503400c20903414611000f1010300660440385041c241402c0000b407141c007451094503c1001000705001a50400343d00c0040607103458803d6503110b40c0c40781000390545d030051207003402942803c04000dd000801083d01406000c0e100083d090300022524219030031007041c40c42003620b0208010042c010010000c00d103082a0310788001503101c00780c505041110034800c04500c1840d8020800704040c0c01e00c80b10400d0b42c041c10b0700e00001081103040c0d40560ae004140401520702e80 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 473776007 1250 473774757 473774759
    0x1406030c330403030e03060f1b07240b100c080901030e01021b070f3c0e04170a081906090204081f090203060f06040f0c1107080f0c04110c07 62
    0xc41e8080082007601d02075202c3c10003100e000d0041c10740d603100031606a001440c08001044a25a0200345400451103e40015007411802d48900c3c07049030301e4405855034038550280600350100140a039070b1065104407441d9a00e0748401401900c03990803410020106040010320840c568000d5001e0303e803100300762008540310058401c40c1001c0c9040d00925a0483c840c071400001e002010300011000c0d41c0c000382d03094102d640c4580c00500100015030300d501c92000d44400020072110f2044101c4c0c01030100e0142c02081e81468180180c0c0d01d0f42c1c48003d8002000100b1203000000e40051714075810021001da01461603688070900e40080407940c10a000c0c072400040d000441c9500000d540c046483e8800b14040141c89442000c003c40c7c10114000750990071010000703481e80d50383d4460b00d9219002400100b008007294001c0b604459511100901146503030703041d01c0311050100a04405040400002e140d80d1714060000c0c1c1c1d4801400300f80703901c520f4442c11a210f001c55038000b40c0c2c03110443c1c1c1049490403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 473777257 1250 473776007 473776099
    0x31407060f050a0c20121216140403240203150103050a0603050703020603040809040623012f01020415020601051e1003020304061b0e01031406030c 65
    0x60729032003481200721401c0401103090700f5014841c540f145031160b12058180c0321184960404c00008200d800481e014000d641014248000003e2850120860340c051007850900e00b00c0346a036500411170302c1003203294441084154140411241070300d4101d50147d5000b0b0145110010301c0384110710070810980080240246c41e2031003461034420320b0091703d060040327541d8a68406d0440740d135413001405541c0510005c00250400e0700c000c5070020b0152040320f1802840c0780104040c1c401e2580b05502041c40070b1401590008011043d44116001b4a0011204408a85d10840e4620300070039850301303041d0341ca9040f1201e480c00d40c1290001c065800d04410800004840691500000d1060038020f0001c942885808181600d091a02010060621184111740ca23002c9009400c000c03c110780c041c2c0d0b41d902145103c6240d0b071455503c0307500c2d87d0300c5111414488000500340c50035224401080e44861081c0500c0d55000726405d094043d003691500d40760002d881c40090001c02e881400340104001220101c08 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 473778507 1250 473777257 473777261
    0x19020901300b160c0807060506060706020a210905060708090102070228060903120c230c0a1415032502030d150e400b010501030606051603140706 64
    0x820140c8034010b070301c0c07590030310402c0c0c4050041c02c900602c842c02c10406e60001806613440990082c1e406841d06c0d0510708166503030360480e40302c02d1071f40c0081074055503088581c0d24640b4280b8040b184810050000d42143e684290340ea00b00500414180710b220000500014025415950fa003a00200018110035034202460702d01030740e0360071088400c84118004959203020f0404041140c0c0e11105d0008140d110030700484401e43c2c1184115008144d2519108907503002c0071800c050400e500000c3e1002035031010400c80030b1641ca0307110b15450045445d0b8940a40c0c0c1e40c144141303040d00141c14007652680d409140110360503017840c85081d041d0340781c6007000c0031a40c000054010000903410402c41031420300146880702c8030b540f250003140081e0400040c0c0700c04030750380900c0d08102c40405030000507402c1106940e003000a4072000304245001408507080c083d400803c580140700c01c2c2803c0000c5818001e00030075510428045500018241a580c8101440f481550440c030709050205501c94502e4603040f00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 473779757 1250 473778507 473778511
    0x2040e0603070506031003060515040203010b0c06010602190308040212010c0228020a0618170307052a0d0804090c0807030f05010e0106210213050319020901300b 71
    0xc0240709482c00401e29003042070841c0d004030005031444001e02d140d80d440c00041d010050400c401210400c200028940345c6001540c040c14543d402151220502c90942d0310784501680030f10210340c8407081c113548005214004090140d01440d0446940d615030000c1100000105500b90680d8a000c0c600c440d52540850402c0300700f614680c001106140e00016108880500c00c40a50300024241041061a014600ba00040d00703e20501002d801c2d0744030b50b0b0300802c95025202103019080000ea440400005005480000b03108208d24464a2400d00c10107942d44082c442042c09264800400c6040c04280c506880080982c28028000110111002010100255400c034003080c200f00d28800020010302896040c1e50290b50350030403d03840c04c04200e502184070503c4d2030308060300b83c0ca0340e401c0c0a0b8030b000a0600003204411501018909010700d072a000d0118480c1c0d4240000e000410b0050390b9a10030f160442c0c0c4501d07060b540288901d802000561295041e000740000d012400008025103044058 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 473781007 1250 473779757 473779759
    0x1e05191824050f09010f03140a0b010e0603190903090b0301120b1e0604110d05040b060a170303010504020702042702130606080c0c0f060403020a120509130b1302040e06 74
    0x2070040d48800c034007510107000399a4864a03103002440102a0380d4450302074a0402c0e040c2e454081002c1081080030080507200303135440c0b60032545421800e500755800550f8070381d03030fa0002c4c1d540a20390300c0e00410303041180703102082c400c0046481e0030000341810310800c182c1c0c000d40804440d0b1036903960b40f41303070b14050306640c21012620700071070390002045904103401d1140c1d0002900343c803036415544e007010000203082c0f04568404480042c03020210002c024410b0038441c80c4500224aa90300744031041240081c2c0c1540640000c642d05803182919071404001c2d01e0448005a50250b00d6803010310000d00a80b4191411000030b000c20402c1c030054082c0880200f40c034900a4a851a59501c804043c0090355042d000d0540402da400012600e000c0c098402040da0081c02c0054980c120500000e03103050042c10795050700107a200c070360050103021100719100b000d10803a062180c070b08910540416854161941c100308030a940302980f0045480f0702c41c00b03421300809404110754031503c501214125003015101c0c9 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 473782257 1250 473781007 473781059
    0x7030c080601050a0e0f13020406030204050306130320010912050304060b040203071b050102040302030f061e010317070501141f080d0e131e0c1e051918 67
    0xc030341e0707a500440072190448096a6030700720354070001c01480b560188030303a50190800b807035001c0b0280800f50b80c4060006001160340260b62030b841c00040606c3c000b8041c0010703840780b02c0c0f00545000280c003c47d440298a20511404418401070f038141d0340142241c02c230150801c0758a8000000499215000314070941c8140d0041200e07064101c00d00c0201e00080b605100031503040b22402a0030310100700350282072889100007600e016142d0303020a040c02000c088254950f840207003813200300202c25001c103401e00158041e010781c1d58519150300c26007002010741d5584040d03000840703001b408030030b4000007070840c0990360111090038580500b4204100f080c0e50365000300746c10940850508404141d880b8074003e546d50b0704118003000c0c000c1042d1114148103000d8070903640d00340d043c26105034030b14125045c204490300041003c191032000d80b002844130422242041040004c200454020003030f41e2824004810250344140c0f150030940745202d40f1614801d5170700020b880000c020b019a074400341403904a10322 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 473783507 1250 473782257 473782261
    0x9030f0f02030d09151a0112050402031e011407020c012a030e12161d0621010908070503040602010c020706020c1c02090f06040b01021207140c0907030c08 68
    0x111462840108180010703001000724051203600c0750460030010b402442c1c1815201c11070071905c4103c0c0c3c0c80300f00d4250302083c0050709036220741e04903200b0401680c02e48401c0c4110314040d40002d441c0e100603001880410011944e000026400358040706081081c0c1080002c28105110080d41d58640c000410380018101070f80c2c00c07a007a128001304948200c0c0450750f40c810a4007a40c00b0b888204c4903000d19604030b8641d0304280c0000300708100c95400c4e6405210485021410000d000301d0300c0c1c14020b111482c004c041d13018003007070341c54030b5001c01c0e1041b501c0f1102d200103581d4035000c1800341940c0100600702d50000b1071108140b103400304c020021554150000c0014038620b03101030761a800148121400340e082005030500b07900f40100320005a40e50070401003801100c540c0081e409000c2507440820096850003002503509040c4150202144240020008002c841c80003400b18400d8601c02017920740e07680020400303e4010808000c40010052003604580790030b04004000f041a00144400201c07a800 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 473784757 1250 473783507 473783537
    0x8100b10030b0901120317070f02150408070f2f120c01080412120509030712050f071407210302120306061206030c130b1504050307210f03030903 64
    0x10030b400502001074801611a880c0c031300380c00c00d02029010103406200c5100c10741c0030a4603581e5181442204162900e01d400c5800810085c540650b10210000c3d050030a410710000ca6810800e4074140c03a4001c07030361443e513807451a1114a0392080301d042034040c1081c1c40700000c940b150080104402c10151000e15120400d00c503034a0f5544032203130303d250200d00d8500208000c00c0600741454610440c1c0e00703014800424042c0d84c0c0007286c008a9012040342c0002c202c82c000c00030a03548000c42040c081ca0900d0030700d410f0381483c1406100d510001001070f41c103130541c0181c0580c280004c00c000c00a0000d03c40c41102c0c2c68544459207403904100b14011301480c0c82d440c6032010301c40180ca000c0c4d50b003c0d05032401c0403e041d52460032902c0240c4a0f075410b120302803201074513580780000d191188400c4100464115245028408021801c4400d900b20b03580900081c091038400040d01411203480c403450000800440701c51050b810003e01d0060888440c41302e5000915030181c00c0b4a081900c0790399072134030f2108901 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 473786007 1250 473784757 473784761
    0x2090108130f021c0b040c17010e0606040c1416050d11060a2408070f0f030515100e0c093c2d0405130503040905070908100b1003 57
    0x103540140542d04180c100300c0076050002041c00d4141380741c1028010030540c2d480380617070748100301c800322900280450180088107006024400d5034505c0c0c0000e000f9400d01c0c5c020315403a00030041009000c3e07503540814030345a91080d142101c200010724107e556550003120b00421a043c107030829102d6100314180d51400030300c10f0458485009605010785250b032200c0030400b010f440080d2045440b84044001b04c01d8010184032028002c1040200400c1b020f440c04a102019001e90703804076101d01d1000320708201040000c10904000c10048010b9078081c1d44582c1c40558400ca86d402180345008810200311100d000d1400402d07032568212212142081454601c841e405420003000420404c80811680d98070b0904101c079a484200400015055039540030444802c001e00b4080826404070303410b41062070901d0f01c16650810715410104802c004030703840b15540c038442c0f031061085940c1d4541c00100300380c3c03041c811000074003100c01c16150910828003003480030748092448544200205110486014001c4c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 473787257 1250 473786007 473786041
    0x90f060503120f030403140417061501020a0f0b040305190c0c0e0402180705041a25120e0415090509101a04020c010908070b0f0c040b0d02160b010902090108 69
    0x45040303145036940356501190042030300071f154160141c040c000450741a194a0f020701c10b4810442c000d210900e4a07080c504800d908024015040d900030b65a0280815641072b0429441ca410104000c0340d51210710b0300b1600c5100340c04d08a03440c400c1c0742405038400e542c0480083d07050350103000035075115a1288000a001401500c000350b00005c0c038000420038940292490782d00c41101c2c00c2181c181560350303203900945507da89412040b9100018a0146404000001344921860484241410005541f0136108500c4a100b113070038440c40854440c2c55654035000700c002000d03401e4030070041c1c0e0398a4000f5405840262031448040c06a000100c0001d90207102c4e40b0b11419072051500c80c03489000c010f204c001d610090031419655241c9680201144007200108002e9100b81d0b00c071000d92500c0400c42d03551000c003815010411f0001c000c10045040342030280c0320b01d07207840f034030060752942125500c010403040b40c50000c1c200c24440d000090012160fa01a003540c16087e00c402e2040d41c1c401d1141d40ca03804030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 473788507 1250 473787257 473787277
    0x4170f0304110a0b0307030b1302090102060705030a1b12050708150f06070b100e0106020a330c02061501090f030f0c09020d05070f02030310140604090f06050312 71
    0x400d10004002c12051031112400c0b60001c1d002160b196190403901080d640201d8030701c80440e40716414024075041c0300c00303540711051403030f1811414040c0050000751601c80107800c010400501001041100c075065101c1c00c0380441000c1e00c220070000da510003602401504100c1e1402c10302c1c003400200e0150003500720601c2440e0300103010704001558010001035529020160760050000c0c0200340004181614190055100c061802c841602d84601000070401c1604840219040b008075803000514090080146800443c43e0050a45403040000e50144da020000012217003801c40c0b544840c2c2d000304069000d04d411600344021400e0744401542d8100b2035119580311a51024802c00229000345e04400c0e803a0322031000050030650302d416035400d80c0c001034001682c4a580d10103204820303403c1072140002401d94000b560651a01612209000005214400000d86080032080d01551050100d07400303071192030403c11141d00c000807520300070513403805a140207114240d64182500701400a440c45000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 473789757 1250 473788507 473788537
    0x60506090a1e050c1201030606092004030f020d060c0f020c030a0807110121050108070905010806040311030d020d0516090b0d0f0b0d0b0703051006020d05091809060417 74
    0x9a00402e040062070001c01c0c0d902180410310840c2ca0201861018038000c1d40103400c007194280c1412544000c40c1c15910b254140d401140c45101d07584049101030f501141d0700500384010300074603800891085e1064401c001c102c13501d00018020341e240c1181c410000c9841c181d00711042c441d42d40c0107242d40c078404280d0142500c00d040c0306100000e0313506a0210083c000624111070b003450500030001d55011961000c00e00c690b11031006100d0740c1000c03c000c00040409500600903545000c040716162540900040c040004060a4800343c403001c0044600300819400115510290500300100810041c0c03494040086940d900d80c2f078203481510035805441c0d101e82c1052401d107101e410742000313051040d0404a616228452101556250b0004100742c034002d45510009103402d92004080318070040070f2401580882c07106100d29603002800c00b41020a9040031680e5184410021301d802040d000940b022900480400084007004104d0a0103503104950008100a00c55801030040c080c40f52085003841c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 473791007 1250 473789757 473789801
    0x402030c0d0b21031b03090d0602090a1e03051902030303240901090c030c1409012f0a020306071b03050d0f0c09081002040e0406090519060506090a 65
    0x82501d90100c164402d00400340300040c50100810410386008000f0070b80c82e50004500010050842e000d104041c244010256140c161701c0c03000503c0c140340314540a8002980030800c803034a6150000801c0240c08080410794480250441a5400c0e506500040b900c6000b981c40741141d040594401921040d401400780d800c60303070740b907000000c0e4075502d007040c502120000d403c02d203032a110307454020b0181208480115030b10f00e0145002d8160b58010940c4020000c0c44e15602585900160940c1d802c000d007440c00800d02118510111040003a95001c0900303c442c0c610715138a0350380000b4100d1f403100d00c01da055403070030360702d4030001e82e0244a03028106686141030301d02d40740000e2207a0000c01b03c1c007401d050001264900c4504090864043c00c40c05004591280e85c14032081a08003d1002d084808460541c0307441d042c070607942502440540002c140603218440031082220030300a41b00004209000d8150341c0780740381482d8010b00700507035115000c0d44113100807803c940e2903800740780032200724030020300f90303036 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 473792257 1250 473791007 473791027
    0x17181209030729091302030403050307080114090a0c03150b0702150309060c0706020c150702100c021209060f0310031106030103031b0804080d09092304030f05040504020a0810050402030c 82
    0x1d038070040b4110b603c80c0d08200c80b903040240d81c0c400385001d235010f581e45549910344848041c001000680020749030f250861540310300f85e0344075040c030350344401d86c0d15011512910b0490280d01501c01001079600030712800c0c2000c540009400007628419008031840122900e022468400500c420703213407807849030881d0300001c46004488000f4140c181c4910b5005140007071010900e402c001b594003e0585284100f802c1c00703981a41001075007090318810304108640034109801075500c807440040c080c802240803d51000e682d44040c107690100301c0c0600310550b00e03d42001c0303004032664907001c2140c5c024000031803060981000002c0e28180c035815182d0b0401c1c0d0401e440340e842d0245d241c2c50100c030303a11810032010034584414030946c804030041d5100d11078003e040012132801c2d0343c1e8149510200d0208941c814074a41101542c40381c01c1038060130981e20380050020704441d85d108036045a504680002a075065081d44609034074800d00710030300030040d0151208100402d80c44141c03005100307100180700181903 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 473793507 1250 473792257 473792339
    0x101206020a0e1c02030601060f0e04051f030c1509060e0904020a150e031b0a030821010f05011206030c052803050a051501030201171812090307 63
    0x9000c066082c0380c81421418000210080750101c103e0720a40c0d01100070500714281080040d014101908004040012807500106284a500c2c4038600c10f40d00d410100f055034680021140c8030b44004400410391903101e040a489940c214443d0000e4002c1c8440130000051251100b113068860690342d4404442c2248201311360040041d0090b0390003001d00c0c1000440d4044510710b03404040e465212400c501c08400c08140c18502011f89084041118080000e40ca948140d00c0f034094a9025184d16204c103290300e0f481b00c5641400113410303e00c00c1c003480086140c0301d00610100441e0000d80e030b0704100034a40480304003950304921004140f40c1010b8018840f910b09506000f10300c041c0180100603003802c17070b05520717030050066006903505c2c0c101c0300040d014003400b803100804004840160385075952442c2e000030404070742440c004000c0c0c0809008240c441d02c1c540740140c0da4030880380482c4c00d0030302900c2d2039160130740c080035900784a40300301d6000141500c10f10011001502c1c41c06410f81401081455600b0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 473794757 1250 473793507 473793517
    0x60106031d0f01050a0c034104060b0a05061315050705060a0522050303060112060302030d0f0f0306050f1212160b0105060403050604120201110c010207050610120602 73
    0x21800d101c0a02000036400c11142600c040c0c2031001062608104030458101c07072500407008201130401e00e00d50035509094640001003002c4074450b0b4032004910680b10600454103d042d280303245c1010622003400f220b0382080b80b0b015422145954203694401c20850140300f24042000d01201c42c0c4800c01c400c0703c1c80034141455002c13505101d0b103003650507540c503828102e01711448184959981c041c840315100746030341140ba2008441c10582c0100306034441079520300009101b64101700c241c608511014070142c228000465019044590742926620043d0412404400c8030380059018030011540900c02c3c06901e040703550190580e04c0c503010000074004400c140e601c9032045446200c100d01000f183c1100144a208014100d00c000783d102460120084401a8007140c812402800b0034408503501080454101d135200e150000c84404102050f8090002405d080e10f2110001c41c03000407003041900204282ea00c900c0c1540c1c1d441e41c2d10403101082d14440c1c060741d40a040c2f040801c0c0000740d1030b40c3c0101 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 473796007 1250 473794757 473794781
    0x2100f050d090b090105100506161b030602090f0103021e16170304060e0703020105030a0504050a05061806090d0c290c040302013902040e0f010203040302070f0806010603 75
    0x61400c00281401c906481400d1422901e4050180c10000da801c1e00784140c03900311002d0b00c030340c060303403803500000030524090b50311308414490403a034024040005940041248554044082c60000e5890400c80c0003904088800c5014070703514805003809600c2071080700c010244901980e10001c43c101525115074010b107420030300402901f002e030b1001c04c0341540032140010000c280c1c180c0ea4540340c50401c00740c40c10760404880680c426801800180c1c1c01c00140c079030101d0000c40c00241540c0314100240342603d0365002404038040c03401444590800611002e02040d00d6600702c410644809103c1c99a41072808420340000301000d2000c4000b4444d81501009041036200d0039205031503603030b400c940303d0f0f8042d100c6040070100010200215600155802131031a640c904260862600750103440100200e200484131101030000104115601e0398040c18204100000b150032600e003540005000b0360050382c0660151103200340010301a2814a1a0b00a80d0031a17800780915919110f4140d01501c1c0c220010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 473797257 1250 473796007 473796017
    0xd031808030f04050709020327030d060e061813020f0102031207080601030c1701060522030b040b090304060c021003180327080a0b090114102102100f 66
    0x1500490840c101641c082d1440380c146061904044c50714900e0040141c3c0004e185900600801c603840681030422003451500f2001e1001c5541c0c1c1c2c030a81da0440c456401c80c00c02192178005c01050611841201520541e4260351076100e4596480c03c11860070b404460b4801c601064600007001410440c03110341d014241030045034180404c1290780c201e08a001c44000e0001400301c010031580f03603410300600c0c01408040c201188a00011380709a044000c050141e002488000910000314103194494480c03040192000c02c0c24058032131400000c3c140017540d0a50341081e150010030030106010003150b00b101d12030303201c109819100340c0c00e102d43c1c41c0c0344004903014503546466641c1580040301e400d0783c07414441e5070f8600080d07a41c0300318a8800c82c4200154824801203200030b0000107000a01030b02e0440d04002c0050146c1d0ba10052280501000c2095006100c40a0207009036503410100c2031081c1c448040d090402e44289101d5820078100256001c1c5d030120244030744001450040c44401610900c1d483c00d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 473798507 1250 473797257 473797301
    0x40e0c18100f02010c0314040f021f020c030d080c0703140d0905010b040e0706020a23070807061413030b13080f07060b092a0d110421050d03 62
    0x519884a5032401c1808030381502112240c103503085c8205120307031710300b403c0c100324006001e003d810b0741c0903004000400844400001c00150354410002400c05440103607020001d1148000c02501c64091946050180c401c200d503c224041c01441c007544a44524010581414419281141d03440844041417890510402541c41720394510300560680600480010550740004c00c1440125043c006400c0d88640003907005100481c0e01007031a01803180c00440700d240400503d00c543d50a4031444080c2151841079403800240e13820042807500880301a45c41c1c0c2d50400c40309220110700c610a81001c0160641d03280005c2c400920407010745170304500d0007940e001c44002c142c1d8640b13185500990141c5201302c000706c1c0c008104032081c000c20000d010180d0f95401e0500b0301581015081c2004030022503d0b440510b10320f03203003070311131000d641140600e0036007171203038129260140000b5402401a0885070b09200981c98503210364036030412030958814020070050311030342822001409039503039009040c958641 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 473799757 1250 473798507 473798509
    0x60409111e0d08031e0106020606040b0310060f1703280e0306010b130902090904062d0606090803031b1804140a06150e040908040b030f0105100203040e0c18 69
    0x442c00b00e0a4400e1504070380d20b082004020703841c0c0e10400c045180000240005103c61607010603883c1d0030401c1a2804110003031081c00003800c1910740f0940b03502580c45c0600002c0d00c4a100c0154108491002641b045819401241e2513128410349141e0140e0f01203485c00d2010304080002a18030228051130044119082000001e00b0043c0c203911202503040c011078880e1500409580d28030060105070011407801a4203001f20b0ba024030f008102030241ca0743c1700d0030181c000034003803d0881d80041001d011201070092061312001131450740507500004109800208501d02c0010840740110b605888000309103000c106101141c0e48488000c180200d03000d450303041c82d0303102e03800740d0710100800c92200300c0780d8034017058208210744095000401012031340240ca0503180d046050350b910100c1c10f81d4081000c40090414001510855103c807150b0403000080240e004101d000e541d0684104554444040d800079108076564002d07030250041c810050030108654601d207400030028115401000b2149940c03c0d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 473801007 1250 473799757 473799769
    0x40c0b030703060f120c0e0c1207020a0318050105071b0b04030807110303030121030203070b0901020702032b110c04020a110706090f0b0306010c0503180108060409111e 74
    0x5501880440c3e19507009002d12200507101c80043d00e0400200301c50182d1036102e200280f1041d128420680300300101080072207000c44220b800c07144a8142d1074000341030165000359034001081c4243c00258000c100d0016400d0414501c0c0c086460580d00e450804840d516260211181c119022180b00c3c9030100000e9000b940001400086024040305604c0e5080c40c20f20030142400040c00311710035001000140585810418900080c95600c0c80900310740c01a49821f903e5440341c42006040c1980720f02c10031201c0d060540003042503e100350b01740c1d9002c1e00340300c0d078010484081d801d104041c1002c04048091042c8900ca032502060f050f0401c8400185500000c6412039021801d90b41c0011104d00b4580c034044020004607000300396901d400d030b070403a1a00c005034140d50610700610907a4240000426007503840303070410b43c503850740003020740ba61440381c10803000d41e40300e0b6950f915011990b00b400050152170184036610b007054100b504940d0a40e203520070000035040322801c0c11800103401410316400c1c0c9501d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 473802257 1250 473801007 473801011
    0x6180c06092101150f140105030112051501091b1d040b01020a0f0317090307172b0e010b18040b040c242c130605041404030810080c09040c0b03 63
    0x1c02908104c03900b018600c201c0c80c03015800c0003035200100d40e01580c1d10b0364404100e9045442142400404d40c580e860042d003042003040011040c8100307980041090a02a031003400c6011149940500150340c000e4144e607408110300c0c00b504403000905000c00385041541200d0000403051041d42c4000b00d04d0350b50b8040c40090040244c4c00220001080220900354204181d04245048011414011181e44030742c2c0704c1c0480c0001c14082c0300040f0320044503420010321008109000025030002c0d064103807241004007012100c07429130358200078180c640390411200c0600301400c0ca54002000e90740c2c42d1900c5840d4800540b0880f0660900c800019000d0001141c883c050f800c105010007075044680380c020107507080001540d001d040c2820190b240840d050b030783c0f9a0382010640e00345e4007200b070040241d0700801c0dc640c019608903040400d6485080e0b041000e80e071081c0c0c46511000360315142c9811007201c440440c0640403540d4010b0349442c1d15860120305403a401407140340a10003051319000041f000c1c0d001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 473803507 1250 473802257 473802281
    0x30a0f060507080106210c1101020c010e0615210f030a090f2c060418050c0a1707030807080d0204090515030d050418020904090506180c06092101 64
    0x24501c00d01a40542c01402c1e2070050100345040b0031810f8006140301a0500602d20941c21641d4031691400c0442c014408a418126030300c00071074940020344055406000801c5070a842030081c00c0010340d006c0c84007101104614000303401050900c1c0750340d40001b6140304608468405100b80603203c0350f02c000810050840841c250f0300c0c0303048646000302d03200d00150303d9003041e4020150060340581c580300e8070980c02640c502c1c0d8001c1c40340035100e003000718004081001c104400c40303441c41c00c010240a400601c1490200c016a95004107690b5a0707290141c0f54800c0c00034100039040340004001140c440000f4002c00b50207120f03004d00d01008010340c18200da002c2e501411440340c41d070702000781c250301d21411060201c9040d406031a101801000061041c450743c058800034180c0c2103401440a0300079411381b8600e8030082d208003d01a103d041a55440030100c030780d11603403010444500042d03440401d5145a04002a22450510a615040101e440140c40d03a54515045030210082054000d008110241c3e036 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 473804757 1250 473803507 473803511
    0x2060c1e0c0d170a05130b1015020d0912020f011d06070c03262d0f0c070f08060a05041b0f05040e06150904020d06110a09050d050d0e030a0f06 63
    0x1014640c2a03c000c0b4000f41540f22007480c00d400c002610a031440480510760b0710000085841c6d843c0540205281d232640c01000007111612942402517070005074849001c403490b214070700c0103551820101c0314840040002034001c515031b60b2010031940120315050b428070b0300722091020f8504076404202180c0003c0c00503158543d03016010030070310100c2117190041e01c0e94a0703c0820510300d204d15080e01445000d018203070780501c82808080b0b032102d01140078084a41c8181d215900c40c0800c0181c682c503007221640248a000da0f010015103078004c1403540c1d0440d400c000281095076204502500148401070042d0f07050108500d80404a0a5081404002c1c041d10122801c0c2607080100b40421191000c1e10ba003015440300b410320a50b01d8070450b00c985840c4080308c4a1005588501c003190209002e00001048a42081034024070900c450700070303100c030525aa8920b02850b40d0340040005807004a400a40303c0c2d00720040b114059842a40c026006081c003070100c9504030074955500780c00340110101598125 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 473806007 1250 473804757 473804777
    0x3040809090c0a20030909090102030411030610061817160f03080306040c020c1201050915040b070c0305090d0c0e060402030c0f09040b0a08060402090702060c1e0c0d 73
    0x454404081500102c440c030020341008031105000d0003400710104007100b40c0140c0260500015010021035845140160034403215040070700300c1c20301075003003175400b11034100c080041590a424005001846191614080c14585240c40b009a43c1ba1003200a010100013060038003103003807000900d45a1404054200601c41a400300070b000c0c4178101c1c0c070703008041246803115003040400d541000f940d400c01012240020040c28000c0280d152020080000e60083d0007a560809505c5040d400140b0a00b84281034941510000500c0da42102040310300806420009020400d203d128000103a0124403078104a8544140c1c940000d00005030b482040b43c1c8003050200a204a2000701101030304608191400d50a500700200f010009009450f43c02401c04004998001241e5840d082000340210190031141081c0d00d486405494580031642a0b008030290b0010640551000a1051081007044242810120150781d0b281c2003c2000c0e00d2500c4003c8244034404511005001c0020703100d00c5600d59682c18 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 473807257 1250 473806007 473806009
    0x30a0203061f0c141b01030209061b0a140d090e040c030b0a1e061a0d02040e01030602040e100f05010c03090f0b0910030b0d0206071509110f0a08121e03040809 70
    0x100c41041910701141d0000c25000006091a80700e440c1024424240236849e0407100004c80c20314002c00800484040c421117400a0241001c01c00071a03650140d20159814000e08000c00d82c2d5a01d00400c4000080308110100f00004110840a800501ca80e40020380795a69031211b60b40c0d02c2e000d907000d4220543d5070032000100b416400a95450600440090220b03d2070f1090890220001c1c2e912450a4040025240c0c400055075046401401440c00c03c4642c5507102e0514000940050181c20030b04d040c100007140d60b02d00641b03041412120182c66041e05c29041c50300450384282840030031401e1203400c400100e4010410920f00780505152107600340c031740c50000c0c01c0020351610080c409040c1880c020700c44c012a02e40d000b071000c1194060f9a40750391224a8604940b0b481034500304070980c949046001410855480c82c005a9072408541003803e03001d21408205941c512442020b44960004100700340e14040103020302050032101e6000d411201e282560380320594000c480c00c86000b5800030740300d525 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 473808507 1250 473807257 473807273
    0x30f082b060611070b160c0308040501300c030e0316120f0e041d0303040c050a09022503020a230610080c042a230f030a0203061f0c 58
    0x500841c03500c0c409601503841095107404c0f050240d941e8262000803480624141400b0030525540d1103000b107150030343c2d41c2c20a02031503005402550b000581600d2482d0203400c01c1b003e5440d14205c048404091a407041440000508260000506140c0c694002c20340800040c030240c804072000d120003843da00079915184440c003010882d440288a0091000d0030380b079a1001200c00004010b603130000702060b0140c108803040001e624801d03042d1200000300010414400c410380e0803140151040d450a54885a031f0000b68000d05500c0302c01e80d0180242e07003244006501c1c80e01420760180c0152040b100207510392002080e0164074014010b4400216454440810001c481d03000711030814203040c480c106a442a102c4501920b40c1e0f1007a52110360030103410398601000d00d410744c166070500c5c1d8104000e400c0507081050360910103200e218122003540c03000c000c10040b02d80c41101c50203800d14681d64951600b00079003010700b1607a0000740c039210340401d09994200710300c01d001c01030f00d44d80c0e958a0580b801c646 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 473809757 1250 473808507 473808509
    0x90c050307080a0c05040e0705190525080f040e011e0e0432011e0903020a0308040804051c05010b041505060c01390203040f030f082b06 60
    0x10020200104035075658002c1c0c03081d03007000e0b240c032020444070200c4900321500d0260340c00400f2000c40315028419a282c2200051540c60300d101e07101e14a4800182d81501d440c0038000c4c003040c2c1c074444044840d440ca94010409034107a0f219076603603410400207001145294010b60000a41c00300e0150044c0318800759442002d40d07210041c40f14132074550900f540ca40e41d5980140005184111301083da080c0a044850301c1600d003860301002d807014400001c82907000e041c2d2003400c00b41c0704040e0400302700e240381140103010000303800d500148034a2180781d40490f441e11008000340c030403503c11b103c0400c1540da6540d00000030103da00b00c00d501d6066a040c49400c460201103a244554649074241401104881c0f41d0001c44208139030b150745443c40850300354050800c2c651001200840501d07072919401307da420201d08500030f10307000e413610440c0c0700099949103c0c90140341d50000b65800104000303103004884210320340c03158100d01d0600310000054851207245520940c4807440d06d03035201e0244107080c07090304 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 473811007 1250 473809757 473809781
    0xf02040317030c07030804020f0907030c091a0f030709030f0c030b0a09110103050604060f1d07051201030807080c0303070e090912161403030106110c012c040b0d050709 74
    0x42c1c51400c004948550a101d050300040c01d200c007010020703042d9a1245902c0300c1c02c1c5006442d201d91464110001401850300c0080100415154040400e16000c8001da0101c0882c3d1000401c0c03030090302500c901d10320f800080c002c40402c55030100100010b0b0092140c81c0030548a62200e400d20f40c158504190100c00050800c051146030080031804525481c524048184003802d0000e0651103840101e0041c0031543c1103e02400b03c26140024a004181041d050507001c06001f0801610380000445440c414105c1c1c00c0e110020038001030010401140050442d10b104a2125143c09050306240c0c2c20768004403441004503810410300040ba040400b02e9a5200750510701500200c18022101421409561103460b00b130b05580c0d1144041001c039403103030640c1d4201081143e0300c0350f07501d1000078401c456040001c07456000e800351240d283c0d4010303c1440600058100181d08410001100e40344202c62203821540c0f107503c07680314008944441031115010380c0210007800c1064282101c510a40702002448 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 473812257 1250 473811007 473811053
    0x6051002060a0c0905061206090604090506010315060e01061d061e130801110315011b0204020a17010b0405030705100527100c021f08070e0102030c010f020403 70
    0x169418950110720241d00102245000405003c04202124031500a401590b0050800110000104002140103115010460301c0ca0b800c0d42d903da041c48240c6540440060203039202100500000f40314a080c5202001c7c0c9030f1001a8803503503840c124038038500a07030004d400b06c5c440c001540c601c805100c0c10b4422502080d05c3c0b4910300036880c0b22040250000182c0c1103000b1030007054111001e018100a00000e1080d0b900074001030003038000e01c0e04c040d40706581c07000c2c0c01f280101d0980400d50007000c495480025001c011000301505400b4040030b5401010707000d04102000b0b1440f1011800340680038060140600255100c03030a2030107140c03a14159402c000c1c4501400700390780140582c4041154000c100d1803002c00080044c20300300c070480c0c444880d0042e07881000402041d001130b0303009402e248658002c031404d00714a980080c2c690304840090800750300059000d00012301ca02e004010181c43c43c4018030450f41340086188403e0b003113690241c0d001e001d035900010100144003801e441d000c1001c01d02e501c9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 473813507 1250 473812257 473812279
    0x10b03060609010c1401020a170103170a2705100801230105130b070b1305100b0f1804033504060204030f0b0a050c0c190507051302040501030605 64
    0x501001800000c110521a0350001240c6034240d104030382c010441c0707903ca1109003481d03e000c01e00501070742080c6806000a880c012403801012440741075075040300c2d0050b428500d400c0060303440c640b0710b500801014041c800001c6101000c1d101c895584808407602001c01c0700070074284410498030801c0c05100d035040002c010010b000380e6500c040e2002d01c0c0080d54008054695403c00140c4a6018031115030a000145110018113039840100070200d01384115031070b8185503900a0481040e100e400d001030141d901821505100038035503802400301d0035004010012802c040300008200380700c11040748492010003c00c0c00101a00030407500d03920110704c085a030403104982c50800c9441c0e007000384e400e0804c0165011400307024046d41220095a00b101c42444505240e08144501e2241a90b00396603c5140c2000240803001a0041d1810441410090400300c1203d1940404c44400002c3c281d840e401003503c001103943c0c442c5203094600420113030158407507180400140441d00d0540c0510b01800e05020 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 473814757 1250 473813507 473813519
    0x30607020102040303201e0109110a260c10020f100c050f0307090e01030303020a080721050a0e01180c0e04022b06060603061a0f030c0d111611040501 66
    0x40741d80a041841c0000001000a4009036445e103083c0d4907410b000c20312514107100c41f4005c190860b80d603407402421100c811a07002400d00c041070505128404d603050710f159103070710140001801180072071444400ca40c1070290080000301d0886002c807804c80940e2007512140c030381c200240038281d500100300364200891460884040c0040c8a0404003039240f038000000510b00c1c0e80102d02c1d6001804c1c2604042100b9a140d1074041c000b94404006403011600706800251018401c2c12902462111240311200c0e1103280301401018040107000c402c0040c1d1140007203a04134409108a0464030981800401400702c10304095a0000e07480c1c02204400d16004100009a21503000c0c0708188208a03000b4214290700c2800401150365940004100c02e040400c0003d060358160000c409807555440480c2c1c805503010030352905442106400c0811610500018507000844005089020314041003c00c91440740348010000d60301880001041c10100c00340c40c1c007130001c14441c0c0c0f003109406880811041d41042 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 473816007 1250 473814757 473814767
    0x5030a02061b0105100603050a050106050f07060e15060a080102070f11011107030803010812070c0306091a010f1a0306030c1e0d05060105030f0d0c020f0f0d03030b030607020102040303 81
    0x840080c0c014000054a51052403800280c0042c010b41e0388000c00c00c5042ca21100c11655405104400c0040c0c144801724101d000d151044e14102d8040b616a035280102001c4161100d401400080d43c586603900c04130811040240500603e049184144a035185850700400540d81e1040d082000c560388148218030014225250303e41225401081501c4000c4a902c0122800c0f646130f150003c80d406805000800c012804000d5810703207629000781d030134600000004401900808902500260308600200701003500c0750306c001c03075aa0050701200700609021802c4600810f080c1c2c04003407807504800c010407980404100e03810040c40147c800c24603500381000020341d1001ca809030540f0844150b1601e1161181c1402081c4805c1d4000d07020000c0a20300f41801611980244900b038080d000714107240801759404254046008181d4446102d001c1042d0244421101203030358040d0048600309012800b40ea03071144450980384681e84c0890140016418541403c50180c680c200f076a0045c0000c6c00021707002 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 473817257 1250 473816007 473816023
    0xc1e050a0503061507050c03070614041e0803040311040b06033709110906030a03020a06050604150e1006052a010b060a081006050f0d0c02070b160c0b040503 69
    0x5103412034680d00d50000141904c030030320780b42100c0c1e00310010b10b000c1084000304440001a104405845042d82d0308c10064442c40c0704140302c86c03110382c0100014040202c1406030741242115591610007115140c040e418611f6119070825556052001e41c440420b1911703005058051206584440c21818440307a1040c000700c0904c010410ba40000720f60700d0301d054074451f5030003601035031240c1031200812609010803140e007004000b501a10302d000010b81c00c5d09000510030313840e40c1d00d03500401c142039443e1203130401024007038030039503220f612944544402403001034107001800c031450103013409007440d0300041d41e00a81d03607101c601480310a1241c401d00c020900032040c002800c01e48074001c400c7c40145a94010900800001d034000310105240000551100006118410303492441c40d105840701025519401a00300801103400100301011640070107801c9104080201c4c0101c652660302ca60300c141c0560030820303400102c0f105003141c0d6014000700010700401000b01d4680c640c075050812000c60307103507140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 473818507 1250 473817257 473817277
    0x50c041a13060e010e0301110c0c0a21031115190e0d050904140109020a021e0606010e13090615120503250f03170a05100e100306050108010c1e05 64
    0x6940c0f0110311503400380c20344002a420040c001c2140d881024170756816500402c1c0c02c225240300c1c001410b141030a01c192418141d90550443d2482d5000c1c3c01828400c0d06042c40e01101086810303100c030b1015480401004482c8001c21448240e20f1406442070110300d0303008010140f41508114048621002c0814200003070105031030b01d0360f034034a065404940a0551410301c8020102c01000015a140155024000580b420b0b401c0d030b0110304200c40c684210038943c4603803079091382200c3c000c80d02560145001c01040800502809c1c5030300f42d00181141190700101050310182d458460b5641a02d00d44603d8070060109404030300345145894130350540d44c2c0548541725100c26000b01132860481c2903105803000700da034001041c45e83d015103458000e200703e21070b4280401c0401c080300410040c1c402d0703001d090f2103140c0c5408400c850a00d0040740c0c8102030b00c06402c4441004c024400070000c20040d0040c20b000e0403003a40003080740c40c02c041d8000c0500c00d001141664007040c56030f249000d254008129600811 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 473819757 1250 473818507 473818517
    0xc0308040b0721021e03010f0905041703040614091609050903040b19031413020d02010e0a030605041104020316050f040e070f1103030702120319050c041a1306 70
    0x5100b240542d03803140c4400002001c0e0110002e0b110320321240707400609041420910030b03608515042c0c50718910340428002d180c001241508180302614195004071f60060103070020102884200f0045075550348107850039500f89413686044c0e011203c41c160304580001d81840141221600c2e1849500c045000b4003480124603250030220700054070800c141d130b0140420780701e44d550b80c04014002851300c071020514a00840d0038041c0c01c6401802c25004240b09562070011705400b000700360708014404800103400ca060103451302105006488106201c805540b00700000152420682840c0300d40400c400c3c0050710650042007000100d1607c180189262a590b051054035484840c0ca601414010b64002480d256076101c200300e121903100510060039003151700d0745242d13225840107260b200e1008554640c0560711428950004281050003958000c01a01d41594400310711b00c100d8042d00d80541d8100b582007004102441661603070150221845c0300c4090307a0707240c207456101405030600107114040c01d200e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 473821007 1250 473819757 473819761
    0xa0e031621050c030d02100608070302211005280203060303090919020307030501091a01050412030e0306040f120905010c030f0309060e010c1202070507050613030b010b07030f0c0308040b 82
    0x408221010f0a91001030070790740c01034090b0600a641d80b58002206100d13a0404000003955880400e0000075a50007802845070104005100c000382621880d81010038400ea80a0720040307030691103094050150301e10b440601e842014070020201c882c4039201710401c3c2c41001808503581c0c00104035046100107840c02d0b2074582d03500c00044100c0c42d0300f00c21482018000001c00c44c0d807035030542c8a241038408125080055030b000305007565a040c0d410040f503000c24000c00042c441584144031104d0f24501c20b00c2c00f000064040070209080c0f0405407421915a8000714984c0700300800c680760f24103001d205242c084422803034140003c01420b0401c0014051015520800710031902c41c0c0c00800340c59410840600c01c54801904150007001412180c60004411481c0c4c03d04d4250b1a000703e13900741d034110000701113685c100420400705034010502c4400c0c1c5480c00c8000000914a030031094001c0051941490b02c2c1c5030b042c1005420084000540001c1240701512600080c1d003020480b9007040c0c000100000307c1d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 473822257 1250 473821007 473821013
    0x140705150723121506072a08160b03060f04060909031403130201202d010e060a11091302040612060509040b07020129030f010501080607050a030906020a0e031621 71
    0x6486000c4d03014207028990703080c4500701f41f2030304110b20580110289155400f0b0356024150b84030914a13000c0c0c1252200100104242500340c0702542e0030980007130000e0070301404580040c0842e04035038414485036032a040c006091503086007031204810746a01c0380910790f01c0c115030b901c80380701c1e120b01c00241448001510000070403440c410041c9007441c003004650b40704204400e50010760418400c01c1c00040e09080c8512141c90041c0680c1032500200d0000785126241c80141d007014142d600f5101144140034403860340241c1e5041000b806a1620150042e951030525800074140900c4040b42110030341808c004004a0300c1d6903c1035503206130081799860403070310740c2c0000b207014000d211800702c800c95805000482c03084450303808448001d02102110740880c5103423020750036240e00340300d0141e9907001000040ea03034074020300c000d102078400c91400040f41700301d981d540c00072a001840c044001a8064002600da03040030003403c0740f412144c103a00204030b8541038100ca5590700740c0e0000404038050741800790030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 473823507 1250 473822257 473822269
    0x15081f0b040203161116090218040b060409090206070506100e0108010b0d030f09151706091e130c06350106180302032b0905011407051507231215 64
    0x10529403840106c60240d998144801940000c03215040148a0303100d44100d40c9031922440d9012070004d0000c0e400c0c03916100c292401009106816a00004100f04140000d20b0501c0700511802c1040045848242484209000640160410001c1d0b0303150000c41915641e64107680c8100740c2c0d0510b40b03814101038400d0102c4420b800d580c401d203503100400c44941c0c03c080d0403c00c110f04803070800c01ca807051581c0b10400c006141400340d0340c0144480f0401e0500036103550202c0030a41c042202e4078030705049030040d41c508400007001e0380715000107922125075101e010441344844040c1c40c1541d40d0002111009101c07808003a406104400c18023419200c0264665108020380c0c0c0110b4000307040c1ea00401c040018005c0150303249207c050b0030340e040948260098000c0c1e99600a6603010380d5200200041c0c1c2601c0308196010000940d40c61051101600340c0280c0d083c1000e102c3c4041d40d54030904440c50a83d07401154400b581541230240c01170040d5000307401c804c100d8030703800117103051014590408030000c00c032 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 473824757 1250 473823507 473823523
    0xf0d09140423011409040b06040902120d02071a03040507060806030f070305030304021f050909070908161811091302161a06040203070c020415081f0b0402031611 71
    0x9400a50b40341d400035202d05032011504880b111007000425451074410032140040848006140710f501d507000c038440e802d041d88409511440075119068040c0d41200703592400c800101300038010b9005d5441444140251102c076441c003d40002010300b182401e039581030f203071a0b550054004000010f00011115901008030500c2c620f226001c0e00d0340c094807400c00399180d900c111010f9000300a0034000d10403400c03a82c0c10f502e40d01071180d6512824040080c040165900e40a010b54040000804001c00c41403014020000c2d40c1c0000940c3c0b14002d460044401c5c0c0c8a80d0000d04500190301d081e0440f000200100304490000c03800b02c4289541401d10030207240280107040c1c1c60b450700c0c00c044051508200740c0500081d461002035203c03216035902d02003044140c0c441168040f000410301c0f00781000600300360300309103c2c9454000710301d03108648590750185070007000303002d0039045040d00301151558603091185501900c41940e06516610f4541a220f42d9075981003480804c00041d042d6000340b41c0c4062201030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 473826007 1250 473824757 473824781
    0x1a090903040b13140d0b0f19060e1e160c0503070c0f0303022b051303020405070f031d060f090102090607030903110102010903141312030c050f0d091404 67
    0x1622030f440741d50788200814007401592540369280d41c425280c0d1400c010005519580807601401980e40d9820000c02c0d100007500c524195440325180f12600102d500030000901410307003d5100500d0f1140f8040110010140301c48103071840181400410b00c0064017004c0301d0794081c10000148205494064030707512440c08090b1080706c0a01001ca01c540d0110212400c8034000d42c2242d4110a88000450103100005a01000103e02240001c0c1290040000d8407000003440107010f20705542c1e0b000b2030262003080340d866001508004142003c2e981521441c44c00350b1081c0c13a41400321102d800955613514000d40403614500e00180010203040c001d40403610a001c020f40104d407140020f14014240b115140000c07210b40e1300d040c0340000720f035105201e011040c9816560351288222320603080c0103140e010a52400540404c1100400c0c200301b16003280704070134840e41e40c9040d80010350038003d00708101007000365241e07080401314075802980702e005082a6106000c050500400d10000140181000c665079 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 473827257 1250 473826007 473826029
    0x4050105060a0507050f010207241505010309080c060a1523010c0f1e0201090806100611011103011d100b030a02130e0a0903080106230c01021303081c1a09090304 71
    0x5401000b00c090300c262070030303243c4403001e030ae100c07503c03284010a440c080009490707101d1100c001044290b2103078010394a218042c040d81890170081d00013450a0580c202c1d0814980c58880c4400c850240d032284403103008010703684060b003041400f60321039002d04010031038060410082c2c4141c1030503c035006004c0c9400e80d51000323014420b40c080326003980c01a0003c504c280d0204424940000307460701c1c0418010311420103900c0c00c1000c2c904001052300e1501a03140514840d43d6540c0c41042c106600400460203404a1144840c61815040180069101c0140418514044200f08002d902c00c0c18050b207400c500704680140c0c0342c1d000703071949021581c591340c400c3e031003950200e003400307480071060f8001c003c580d02941d0340c1400c1e40e803164402e841000c8500628803c8040c40d42068000100352805041d545000c00000f40c5400d10043c0d141040e48101d4000b600c51000004106802681507160442c401441072014044052001560000443c41c0720b20a4055100316001894010040c81100c018140c0c81780b403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 473828507 1250 473827257 473827267
    0x80711060f0a0201090b131208040c1d09010f0b10032d020a0f0e060403020108100e281802040207060605100504050a12050d050f0903010207110102010b04050105060a0507050f0102 79
    0x2c000e019041010099400600d1003020882e544601d282c01008603070003101e9039210700c0105204807a240001001501c8005d10200003041c113040c0d4120002c0302e2074070500c103011070b81443d80e080c0b821280c0180301400164503040e8448425220020220303031010b01400e00080368105c24000c9a010444440f40c2c0c8034001ca008401d00e2290305590151a01c4001c3d90744814a0f2215560f0030b0b2081c1120020150740324006020410040d880b030071205501046000941c00c4a03079850340c00341801501070703c0d5890751000901d035568280010780d04401201507400c50074400e0134290340b80004202e032200c0002c1d000701d0b00015000c0c1440b42603044a0020600070344542000712001070010b040d500a40245842170107404400101d2240c0d0034041003c0c40d400c0000ba00402c5800b01054034039030b00c80c90340200d4240c0244100c000790390b420700c05000700304c1c0114592103e040042c0300080c00c445666512911480c84d00005005a03141e01058840d43c280904040d07a44070b02c1800c02e20f2401601405140309980000b0b6 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 473829757 1250 473828507 473828527
    0x80f1503010908120f091903020c090103030903022b1106090306010e06030f06040803150102070b12180109032a0204060b071202030708180d02090a0506010206060607080711060f 78
    0x24049402182500306645d181c02c0705c06500795200b0380300e09007642d002040344200c901c02e566030707800c009200340102d410713400400300403c84000c0c0036401900424503a200030010750501f040e00b41c20015401c40385060003900094078812911201c600038081d030b00c0003140c1e0300301c40d1651011160004002802c0f01c070f19680d11a50300380c00b07882c102c9260740607018005402c10301c2400003030b0541c0101e6107c2c0005043d50398504190b000e0852550105045124080000911813602401000b0324810207010145900d065244800034490011036507259078900995180400e60040c0c500a5460b00d0f03804a660307400c604140d03101201a1403030041e502600d061400111020886d000708151441003600300c1901c5000b8030140d07180e0151003c040d1000502f0400310040d004c603440000500c0900034040344080d03071130345c0100301510811101401c24994842c203000a035130f01009641da01501c115102032500341c4a03510300c4102d005841d801070040300200c44565095030380c04142c424000441c2c0540f52242c3e902d003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 473831007 1250 473829757 473829773
    0x1404031220011401080c040e1b0f060c0303040308070c051c030b060f0414030c1804030306030609120e06030c0a030e010e01020c160b03010e0f250e1807080f15030109 73
    0x71155090070710500c1b0040f0a2418540110001c005142024040940303034456880f0f441c00083c04195403048130700140391070390b540b0031001c1c00140010300004d58882c40e1625014048000151204d81849820100f080000d1000160307841c500b0f240815061848070300741c8042d8041c0a541d882e00354484030200d9003070b00340c11600d00034000325000c0c00c06c44203805918406040e02c1e075510401c8503410889014002c407507001040c00300c0390050311074540000d0305903503071716014110b03254148120307a94040c0000a1804c00c0c0d104600303132010710702245c40901e1402c08a680d090584a0002050145912101e084002400030f5210007040c0d00c03908003d554800005200340c0e1038480d2060100720f401c1200340040b4036040140140c9040e07a00c0c00a03400469140c10002001c1c44200a0000102444c08640110514004550901518400e45509641d040303c04104030021f80d00c041e05010200001c81080f254952210540c0e0b00007c0034407020b01c4540310407055a440700044015980c1660070134480d03008001502c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 473832257 1250 473831007 473831009
    0x11010b041a0118060807110703080a051801080106020c040b03070b0a09030b0a02130306021606060e180307020307030b09070f0303080a0605040c020601090c0c0209161404031220011401 81
    0x260384441c0303003581c01a101420129240144800101000d000804640c041d00085250300c7d40c560803110300558070355901c0c100d40c2c01031040d039002034000708411a80d958001030749140d0b5402420464500e604105000f561140102c0701c040c03013a502c84921b5481501d080c0050800342c036500180740d80e00c40c47c4641c0900340300032611003203400b03641b4040040c012411910070b4540c42c41d50249845c0f9410701d541c0740c01d03001e03403c518400c1c01011005844e00b40020941e1080000802085414030050701c4c15840c0d8000c0d2007a190725000b00d5410030031030b007001642c0100300310040d01e90014611f100e98507a42d26440c6840000e400918841c407803584044107158020545a00c030310003015052090a131280144000e44d214903600390050703440340c801400390b40360715004007600742482c0c40e21650380c034030075000903280181c241c81d12460620003036022100d9645c06421303007041030070f001001490107103155110284241d90455001c101703c3c114400540ca03601c001c0325201100d0a180c003e110b03045081940c10203003842 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 473833507 1250 473832257 473832259
    0x7110a050117010605030a0209041a0f0103060317030405070e040302060603070b04060807140f0a050403060f0605101b0812060306060915010302090616050a060b1c020111010b041a 79
    0x252020018a56108002c000c0081c0d15a20100c0d1140e4606082038402c3d406c0a4191401d2940a0011416030748540c424000d0f0004220802c000045201c0c081c05241101d00c94006d0406041400c14004201c1c003c40312905213003580c2c0c0b4607a880d5a02e042c2541080c0185c5c018803502d400036000e2006145d800240c45019101c21070030794001d59960070b440d20062140703204050114142c5030000c2c0b030f480d00503070240c3c2c41c0c90a0462000c0c40c00c1c1c3c02e285460340f1a8045000000811700200c2c051003400b45a100d021609400c40c2000c00c501800d1500180d8604492180d0318100005c49801d10000c1e44403420401d00396a0103c4032030344441d003000c0004006102124030318000d2003190001541880c0c40e11000c0e014900041c0c2c0c0c090881901401140650310100d446c0d5048070f0708006105021041e81c0e1074000c203d0088000d00040241841c0c00c1d0b0940c0d410195075445070002c00d103001d9503e040f00c006983e40c0d17942402c020100a07122903880780034249080042d540b1038034008220100e207403110104022020 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 473834757 1250 473833507 473833519
    0x190e070503011502061605033d0512031c020715022503090501200d3b0103051503120a120603050601060e060706060807030c14131a060711 61
    0x61403a104917511035040701c3c0e005202c035800c41c44100a90156008580246881240e00005e078000d200040340c1d5100001d4078030651a5210440d900d06400481d4907028000031550247c0c9000e8a2080d0786c1e40c0c0c015001c40d220045c0a4541c840c0720441164102d41c070050b84a0014038816900c210040001d4010403005044803554560358030b4525081020810300701e43c5034540c420320600f84001150742c2d200d180300060341d201414010b9281440100710b5942407031400c0d95a00d500280141c0c100c4447c01a0740070030704000c401c030a02d0301038602480722114118582864000f07003503a02c0d5440c024120030603030307400b51b0517003d80c400035205450014000c01030028151a0b5914030311150748070b05c0407580140b1000d02a900440700510640380b151052000085008005038208000c07a103403041299480c1c0d2040155030700c4410304104104c13100904c84000c0c0085400c408030002e54901081e06000b80703920280034596072300580e5482e00b584140307407071100202038980e940320006858408511500030341d00d284244 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 473836007 1250 473834757 473834789
    0x7120620032710150302010e030d080f060136060c1e0303150f0315090503030a0c1e120608030306150d230402090702010507020c190e07050301 63
    0xc0c4031044038041c0c2e0140e050300b0400c41d030070398038600034240141e030b030301c0e5140982d100840c000001e5000d94901110040d04800c1d0700b915500c005070030703000411405800ba4000c5916041c08a400007800381e8803115900303041180d40d41b8440100c400001254145400801c108043c028406d0003201204a40d41d2180c0211140c0b0746848007501c03241d09501c33000b800710f00c10340445603038100c80400144019109080104401800d5901c4803c48078454001140c51015800c0c100148507184075880000c800e404001c11010505480d069103c2c4001880303603c0254841c44802c22052041800259043d02000c4c45144001c000b8802800e80c02c48001043ca01c078181700d8042103245010044038006c40000303155954005070440da40c041074200c15140500240d640180204180811b602c803015208048070100c45403410f88100160b800b0301800d4841160324100070808015000200d09201000c202c0d070880c501401542024548840ca4021401e010351301010b12004a400a01a40c169119401c04080c41 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 473837257 1250 473836007 473836061
    0x1a070201020a030b04060b180f09010e10090c050405101814091503250801020703080103140a02090601050f07050102040626040312050c090a15020c091003060509071206 74
    0x1d1b032824000c2d07031120a03040003000310000411413405030705280034001019000107000043d400700800d07132044074494032000130800d02801102e1142c1c0038121f500820491b044106000500b540610b000c0d807030040d101400c802c0c4229003e0701050143c04407003102d504601380c9640c6a41d07010509881880e00411007000818a0050b03c000d48041c0c80001800520300b000e03102c0c0c3e0b4940302e82850000115a00003010010a06080a00040140a0107510340d1b418951452501500050101c1b02d5617115400c00096000140c0d2070342422134212409107815600d452944c5040403282c0f140344030041096200050004180f60082c4040140500d45080c42d481400c515280700070505044400030001028230349480e525410680c0640d40042c113748c001ca04241500e40451080003e54001e00005a004c014520300d06904101c280c000392410b4407a80c400c1c0c20030400d01c2e0490009408000d000b513445030000354000000b003200c0e00040c000705030b661030345021509094000341001801200902060303800790150f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 473838507 1250 473837257 473837261
    0x1c030507020d0f140d0f090e1b1b1b0f0f0103020307120203040c0e13110d0c080102180909010e031e0c1c030f020405060702010c0606081b0a050409120503041a070201020a030b04 78
    0x4c0b0b900c00e0b04010003d580d0034007080e90020346909e40207009002400050307188a0a942c00041c0c1820503402008032207287c001c50118207002000c0244166450003000c4003c0c5c8805250511001080c02c0145e00c0391200101521085110501d1030710a901c003108020030711a2200901c42100c4204d04a084242c803601030007080d00c40120390290880d20380c82d41654060134403000c902c940c50b01030145c0145d040c0d141c41c2e4150076030340300300d0440c05510141c4403004009c0c0340c07596006070007032950300003000102c0c5072030506603da004440d0000e040d02a082010070100700c0f41402c840111080009840f11150f01040c0c1c80166509442e00d600000c1c03800030101c0c5061128800c48083c2c800003000c040c201200c5174011a1340e2405100111012038484c80001a9050100f100903480018040030040070030004050011140c0c0503400300f40320700e04110601c004500341506080c20010309250076641c9a42d1070902000d00408005480340c204000e008001901c1c0d41035002e007010740c490741c2d424084416441c0c20441 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 473839757 1250 473838507 473838509
    0x110a0215040203030912030a0e0105040f030f06142401020705180907031407030212010507050313050c0d3801230301050c091c030507020d0f140d0f09 66
    0x40940e020300ca03203044004110921a610502c001c049038034010640e0041061aa90440300707188540c4046401d0508940042c12100225001c1c6482d41c00d0610b80050190b8502503444098890002d201800b800d0281c2c68100101c071401503010034900381003140c406802c9603501041410007840800c0c105045610100f0742c00202c0e0390041411818244c40750390840f2081c000b614400c0c00c0c0c41004000030019820300700e10107598030759402601400b40b4600510045114000e8600000d034944010401c40c15000800e607034200812074611072000d4420714041d45000c940e200c8107940012101800700401c403010304d42d800280f0300c3c01d070b00004030070810b01c6c5a0004006c0e04001c45440104900500001a00c500c035282580d0003005803850540842c1d0201e0300b141d8041d109404000400510000e5900300a9a4061003000c00c10442c1c80c0100302c0c0d2001812402000130007071140350349030516000e0092031803c020340c03240c100d85104008003088030301c6585c41544194440210392240340c007a11260003900f00d40 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 473841007 1250 473839757 473839777
    0x708192705010e0d02090403020714091009050603070b030f0604180f021c0b0c0301030b0c040b0405040207080d0f0911010905031207031b03030204091512030309020a1703030a11 78
    0x103114a82000010344405a42d400307801d400424512280015030b40f59103001d80100c2c081d070060941c041c01d01c0e07181c40280c4501c0702c1c4c3c280034a410006000f00040c4a8000104468080c4030001e0311b9107030500040e00f04040759000d2590f0880c003100744030010b0f5420003068040d81c42140c00704000117459a20700741d1002000d0000c0c01d001d00030140c800c05402d1040c1504c5059000004136070764801103a880100030b504c161401075039204084018400c0140e49480d407034000044440c0c0da41020b140c5644242e480c4924050b2601030764011500800b0820328806942040d01c000e03609100107039464071607100034a62500150340f12030b0111280c104030350003410302c00c050700c1001d406403d00300403007203600c0e0199000c104100c081105005414028145e50008004001e100b031b6009070ba10f5140c00300c50300c1919000150050340510702101007280803400401400c2003985402c0100c1c0006141c00000c4a5941c254441260500c041000400f0081d012006601c1055100e50800100544807a00255402070030f082d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 473842257 1250 473841007 473841077
    0xa0b01081609081e1905120702060d020d0f0c031109150d020304030f080907180e070b0c0d0836010b040c030c020105060d0323070819 59
    0x401e00d41c52241803403054450040c1001401c1583d1900700501e841c9148800c682e03203039500241d422a0000c1030004101c000c4480b81200c2c1c030040551141622140c1e1010701d5402c3d424001807030400c540700c5009a07000c40081680854503980c03034103062405400c50f11280340700c0d01e24000c40c0d814a076010b4890804900c2c044400e241c1046500c5082c821030b842e0311802e031100e191050040741303000002c03400110701c95442a500c180d104040d240b009000d015000e400f00045401402c000d00c461481c0c040b541607089101e04022031002c203c0e50b512401d040d02d0707404c9816641c10014411384080d0001500700c4171254940d503010003580d141c403003030700032031031101e04e070b11f0310042650b854002ca482c081c0241d41c0703503054a000024030b65100320700150450b0b0a0903403604c01b00307840e180765a02030b03038080c8500d552012095400b018882802c1d030b4000c299600c000030305d07550400c801c2d82c020500050b9604cc1c900480d40002c6541c0e0700c1344c59111428905406035655000185114205100a801301c200c500000c1010914 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 473843507 1250 473842257 473842261
    0xa09030807120207050d03060f0806090303070302030c12041101170129040e01270b030a02060a140c060405070807031a1b03041406060607050c090903071203020a080a0b0108 76
    0x1048829195107a49007102c0c0b42c09000e000d011440078004641241026100000c0b036034a803e1602c12800980c0c0d00c98103454005d041003040d502d002008172940306000d40380050f07032a503e0190b02c0300240034030b100c0d403130030100d1078002c21080022102400554042c241c0351900f0042c00e506400012403400d00550100003480d4414a00a024501c81100000040780c111410613072952a4145480b50036400800e044403034900d54001103480200b022803000740e8030704c18005002c058000c03030b0b603454108000034016100010100d840394454443d40c180100c40d95040b0356101c0700605040d54071b020a540946003401202000101c542c000104c0350308495005034000c41d41103404414880034603008044140389024000805a8886071070b008620451148508200c008804603410349084001455503008200130040384003c1480000c14401e00e00b0200e400d440e960b0383d01e032680c50860058103002000740303d00000e000f810035015005005402c00a0f91070902030368826810390181c1e039440704864045094200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 473844757 1250 473843507 473843521
    0x703020c100c120206150f09060910090e1b030c01020a0f0c12140c010206061e030f01021209060718170111040b071704050a120f0606060809060a090308 67
    0x20301040d544800c0c10054000180b9450b40900206084960030060304810f04100c003d140382c0c4812481c1d5182555540c010300c590b031000ca0f05106010b031440f03101d00710900005000d0300c107000250000c0d0a00d000203104940120007225a03400092464800191140d4000001401d000800e5100108141c0c000d204140d03071501c0c2c0a841c02401001550700b0704c00d4030004540c007226030000c4460b440c402c8502c04102c503402c40c4803604118008038941d04540018042c006165102508032500300503010524001140c050002841c01101089050702d950000c5140800005030764015031181060300c06881541d40c0b4002c040b2074140320300e940e0800ca511800703000e00078031603c1064449209806000056002c5800c0021081a0481c0c0d1164460010001b041803c1050000480d2513400b50007410604190605000600f16021801144a03c540d401414002e102c0040c0e159084640c10000401a80d900c4140046c6070f0303203046418080a201c0c032004100b100c12035200f50741406806039200086503c0c2c0c40 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 473846007 1250 473844757 473844769
    0x90604030b0a150609080615060324040609051801020a050d0504140f06090c01030519051024030c020c0306061203121906050a0806060d082208010e030703020c 70
    0x90000030705a42e03501c0ba40b0102c1d42c1e08503407000c0031308901d0b100c4c010382500c0c018080d86400f6006150001000d8030741d0240032a901c0c2c1d60b081d25007014100300100c0b00c0780d555079914441d02d44c10124081c1d2044c10040c000800b00c0c4158007041c0902d0900d2a0f0842c201d00e0301d4809820b0744105d03024080001c2c2c0c1040500103108460307104540092140c034110000d00d5444010514281c000560f000a5821400c18008500000c1120380401030080c207081c0900e10700386041e8101c5c0100540d003410455110000220700b131181c0540100548041049000c100002e0700300715140c140011703e02d00110340b6018000210074000240b012100000900400d0980d84207002d0100c200c8018200440c1c5220910a54100c6038140394801c2c4142300007640b40b0f9030b000c1020700f003c05a405a5000c540142c49584040c0301d071040100b08a80e1090094a82019130303445460441c08034030075841302540080400e200c0c061100c07503c030f0310780044601040c001d02000340f0714402c40343c40c2d10a84000801591001040003400c1c10b002d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 473847257 1250 473846007 473846011
    0x70309120f050109120e0f01050f0a030b03030c0d080601080c0d1d0111031b07050d180302060f03060108070509220212040f050d0207140904050c031207110402090604030b 75
    0x92501500451102c1c1d9809080d120f10301004c407240e00703084e40345c61300d041e512006996802d20100d4100740c01401510000e04980329101c50f02d0445040007420903096806900001c13003100d8050210317680c50f20300c06212611a0301d81801000040e2501d80400c055601c200190350051440d4a81c45184c03a20b5080814002d041030f1060440306040d04a40401065083c400d400540c02c02030f5202d6900e2920300320f460440200144040036140041c0a0007011400002e00913003d8241c40c1410000c003501c5982500c040740403a0300c000d40c0000c00103491a03940c440036000d180078000c283c03101c01568880510079101801404000b5420140114000301e141c6200180e80e16041b91901f00103251100c91294106800300486050312400541ca6424040100030086c480341c0d51001d00c003410f41c05050004d0080ca103059502c1c8148208003203030114082c000140030991081d1001000c03260140d001000118413604051410f440e1000c0300e010300d1586080c10300846600c0fa40c0200003e280509580d128403101d180 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 473848507 1250 473847257 473847263
    0xa12150506090a0903030b03031c060f060206041e1b030302100e0d0309110d05031207050c07150516030806010207051503040b0c071a190b01020a0212013b0307030912 73
    0x4940c0741c413445031424001084cac0c160310304452206182014000b182500e005030f03c03d4185620031041040501e60108901f0780196218142e0400700d540108021b21219401c00041c10355107581c0704140003101d5250078041228465000d448100f0003480c0300100319080098681c100ea0440c60301032030154400c0d88510f418a115150380d24103a80810041502c0e2001c50508803050b52000500b10014000f2400707099100f8a14500940740c400580049e0340c440d40745210b1411480d8200c0141210103000708141c50740ba03103240c000000c80e4503580c00d00506545098500c01d016010703904011a450038001c2e8074405004074002c689195403500e69600b12407084c000d2a407000718409101083c0011b480000305142c20580360514401c6040014104d501c1c44045140c82d00e460b89801c00905e502c0e600808c00802044e01151070b2000b8010030110980580041d400310725201140030340c3e103c7e509201d0030401b41203004a041000703003040d01e403114a03a00e00c20403502402054011504000c0304050040c98284144 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 473849757 1250 473848507 473848511
    0xa081f1a0c0303010f030b060d0f021504080d03150b0408070b031503031603080f061c150f09050c010305041e151806050f01050f1903020a12150506090a090303 70
    0x207528000701e4150380080e00001c13050f204c6000704106000400503a103070080130444030040c8240b401d03500c2c030f414038400410003070042509080c140b21102081041d41c00420b4803030f0643d00c6030030301020020000c040404e40c01c4a00d80303640001050103c070450079903058a22800c020100d40b42400380042d01500018200601c0000c0034504502d03e46090000e400d8034401c90340300c08a0f40240c0d140290002c10020851140001d000042007400d80d42e10b1810302d0429441c9001d050001003a00b00156a0421009902d50300c40c20000480c0d0403c0144d84000851030080d001d4980314010b690044040c3c4400396009490a0409089c03a032008a40b032804803a11b80c82500705100f0340e00b890344400c0c103403985c04400c80022414041d6140500259006466100440044000c0c5035030505000800034111404030b180181003440c0010582d02c204000c5d14048c54004008440c03080d40e8030b158403400403072000c085078003c0441082044040f02400341c0d40c0a404010100c103482c0c1c2d140174282008040d54801602015 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 473851007 1250 473849757 473849767
    0x7021905031204031110090506070201030b04020315010912080417210309060603120a031107060f020703021212060f04090c0905100807080604060b0604030c0603020a081f1a 76
    0x69000c0241580c481c03610079485480d03e1450501c2800086400c0f00f1314041c04414201c10b54a40d400101f000594100315005502c800283c0012030040400301c41c215001440001031110b14581d2901500801200f640c0d850394440e1103880710303011410325000c01002002c5c20300050180302c0c0c9840e00030b0f0030001c101d4120307481c005040240c0e2103000117920003003031028800000d00c0210882404450750224040d00200510110110018210710403629241c0403d5a40d0b120008001d22220803140b0103034001e4020b100341c200c0e0386090300c020b41c00010110050300ca101c07010010460408240c0b0800e082d039185540345903903690140522040c0009245611a0b950402440020b000e808420041d14440c03000180e1841e1044a40e641d50303186030082d2000e84d01c160340420850300c1c0042ca559101d40c0c810713004681010308402090141c003c9410060541003c0c07500451003a40c07581c003a1508485694420320103460746403e08040082c85074468442401050090050501c0e80729203807880100610940d20341 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 473852257 1250 473851007 473851009
    0x506180111191109070c03030b0f19060305100b0a0e040f020a0e1009143c01170f0f06062205030f0d1b03050712031e020f07021905 58
    0x402914419520303400055041c1090091202c180000c2400c02e5658074854144170001815101c03119100508060310780400760200d4480381402e07840000c5c09440249042a0701210b40c440020500507000000d182000144038005a070003030b50304903502c1081d410f00e40031035100c08848520110080d21340003903c41d4000c050b1320381c90f4402400076185507130340c00380452000020000c4010b100c08441007041381d01d5000740811144103170440b200b19422140c22602e060348000c1c401d010958541c1d65908420851505444441101c1d5210003102d400d0380c81071200c0d070084103140c0c003010058403104d40d02410f940c001040044420004c42d002500100283d0604040700c171460512443c0b0300d101340e100340910804024a0808028030f4045a0081018280781c0d00004401060503e90030794100d02d541d40404040140340c00746044030f403859003051103144006480d50025001d0301941a0340340302c8843c0090003005e182075520a6500320414001c520349091101e40030498486241c0190f0704114206060000342 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 473853507 1250 473852257 473852263
    0x70b28051f080109020321090d050a020307080f0601050406030b061e130c140a080c0706060e0a091401050c040506130503030307080610020606010909020c010b15040f06090506180111 80
    0x2c199240c00854074620b244141800d06003401803d0101015054006851041a1045d10700c00c804c203440001c40d06e04103084c03151803d1a041e030702035050b002e80e810200d007205000c00c09564100032a01228101d0343e03907005020899025120207403038a003880c80820303050318020a41054044650001c103c41d10702500020720549080101d4421880d5260b0740c205045410000d003039a0030a06c2c003c1281014441c2d6800307414480024100740b45028005400800c114081c0d0040c00a405010801e250500c0d0907482e60005100003541500da0310758a909801c1460710500031644111000e000c12410940390805110b442d030170206240c03d109902407008100e42c2c4080000e0340c81a241680c0749013050502406000c40101c10301201130443d0000300c108041030345c00c50300c204100c5144400060307036028035441c1e00c0d0040030404031042d406010300c91400d10841080005d08151f40500f031141c4142c654941c8207848090f0f00b4860150444018003050031810101030035a4042003040c140001c180160645080c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 473854757 1250 473853507 473853509
    0x303031a100801050a0f050607061e060e150d030f120b120105061203040303140a03023a0c090302151c140f040f0605220602070b28051f 60
    0x8000b03545070004106518140001c0e000800e6060300e110810b03403c08000c1855403040341c80141010361541110a2884251045401e8100b82207100700300c1683c5644024910345070540b0b030140e014074041140c5102d807034507071102a026685904c0d9007465142c06001500c180038030380018a00d80b9606d00400401d61039281181c40041781c143c2c00012140703014008c00800852461580f0a01d074814001400083e4009860860447c0d80000b9907445611a03181140a841490ba11500304112410b5801035540010107504130840300b000c004400d40001240341c0c00300c524803c8c0034400070740140c2c400c0003d810800c010219a04501c84510318101442c0251502c952400c000b04003401ea6607814078009070884c072042c607080510360141c0d80d428240742d01c0d4590310710314000c40641100e07990f0020860003c0091001c0c220100902d001100d0f503080e5041c07000003504280e10036101102601d000a05c0404c400100100d18820400d5462403800401c17000c1005110017024140c0d80403207841c084c6962501001090 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 473856007 1250 473854757 473854789
    0x50d0509190515370f1404061b020a0f02150a09060f020303010f180b030607050a0909090b010b0a0e03011104180b09010b090612040501090b010b0909010303031a 71
    0x4145500120f18201200011310220307000c07030790603c81c0d15030007035010320683d181e801c444034030306520100745000340104040c1031001c1840d86070410304c41c0d940700401c8071548118004c05080190303d09821010a40210807032645006800c1401070600040f001c826907282d060001d000c4070001300b04050705150b19400000b201c404a880150208500c5c1d43c0180c0c1c114001100d440611f0640d49062030503000070665000c4e07094100001c1c00f0034080758bc49a4414004800024200c841a0401c0900074056900c40b0210400156000c24041103100440c004c600c0340f282c5c048103a403010303884c0403408161500003000ca0070400a4810322840035a40c00d0080c1700001186842e06e81d42e0304d18041020011252004040060700c1c1486410400c66a0764403030300341116010048540e84180a1300099828401e00f006130f544601c2107800e0005002d015440242c549101d006d4001090f6210401092a40107081020364480031540051000034444d1300b001203080103100850002c9060880000d0300d0310100703041c2e1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 473857257 1250 473856007 473856013
    0x90806060405090c0d0f080a0c0210090e0609091606030c1205040519051501080610091514010311030406050610020303010e04020d0f0209070c0606061803080a0c08070501050907060f050d05091905 86
    0x89c02d62410106e00c0605002e10300f4981c104601c0c1010010031090b0040c80184260042c0d4000b030f0030404280828402a400c0b02c4030724540700d4564102600a20104102e20300080c0c25a5007190ba0381c40a1040501454001c3c00a0600c0c0785c031100b1443d0b500b031400d2002c81351800750440650300580f511506a01030102c440240082d03192020b02d00007a003090741c1c410741080d8201881d100e13031711407011020300903031b0021f0003030550102d81c030001600a000c40c8100804070160000401042c01020790105000301e601300d9810300c5215061070100da40307010031302402a0400c001800300d0700521303240820141051003101d0501d50915683c000804024040755040042103080049004010051003650043c0030141400041c403440000114020122404000c000c8a40020000e14450103500503440c0680c1c0b00d84900e50b03030381e51450094041c1000740e840d140c4030700c00c01c0d81c00301c2d102d40220181c018000e910f0742c4031403c1240070392022028210213420030700d0a000300600c4041450480d40d1041c503241c000c40c01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 473858507 1250 473857257 473857277
    0x708031302031027210804020414010302060d0506040609020403030c0b0108061e0406020c0604050304170102070f2013021305030a0c171903090806060405090c0d0f080a 74
    0x1403604219034030540c0440c09107000031040c0046104041104246994411403100c8052403030104100c1040d80170030114004402c4000702c1a503406040144180d2080c0c0302400030200e00c0030340d00719580003804002d511041c14402c2c0b4400010380e46c055680410000e1011030317801c0d900c4401104030380c0580c0055000030074504c41c2506116a03041c440307005010a0004150516000d8105040d4402c42c091040c00790030100040340a110849d015144500002019034619051600c0c0265903984148214640b03248a41d41401d1407031410f01c00d4130ba2035500140c1c212135000f229a00d41311030017481e010742c41c030954508050150300d480e0321110300c00d03600b001c110040c1d0703a1aa145c1c4c02c2680d020540e001c83d100e9403019045000240707104886400b1240c0c0040400c1ca4a5506680c6608003101710b50000141001c21482c07500303040d80250400d044845040582d4065140e08081c001a100d04480c1400c1c2540200b8001e2864101400b001c0101d6001755111242d8a203036545420b2594401945c0c070b070018001101c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 473859757 1250 473858507 473858509
    0x190905010f09180b0105040e25050909031e1b011e0605030a080a050a090315020d0b090423030d020d06030605010608090a0b1e10080105090d050d02030601050708031302 74
    0x81410b03d0321185502c403200440f4155508114610140209030185803030f080ca030800807004000780306c150f01d5a440030f0034044008007880007142e4200e10540d8400e540c1000480d041507c0031086665a406503801409a150b82000400040d030042c044146140302014540c46040381c2032180d8503d0a444815140c0000b00000030142942d05a401c4244030b40c000381c074080001080d0714210340703200c00380381011307500e8041c126401e584040e0745500181c0a416540d002038000d400d41e5002f000140780074801000800051070510080e40c00403900200008030280182820070319040b010100d500b441000c49141010030400f030380070390304400c40301c145080d1030743d505200f0801940281c83c094040d6260240562130100038641d501c1b2003200c00a03184212032008646450901d01150b00400d0300c040c08400310b821700c02c07800d141d1024144150801d65180001041c00780380040b80102a0454955419042c410030000c054000d510150046050001c100000000203003180042c5100360b08030b0b814080900c2d40c0340 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 473861007 1250 473859757 473859761
    0x11b320f010f06060e0d0c170313060c08090112060909050a1505040206070b09010207020d03050c0d050a170603010216080406230403031d0303031f0510080105190905010f09 76
    0x107001082d681486024000c0302e6202e20a82d03840c40003151100d91000302410f103c103030001d5030340050000741d0118210000407203002000740b055810b0300044440082ea03400f81151584402c0300000c115103010041002298480c260700e00903016501d40c0080c80c1555015501b080313a805c81c0089505811410b5a4000e100e00b41880403a00400181c0c02e001d981b500d9400500140701c1c29800034800e20000300441c0404400354151130b01e1990242001c00d40c14a6800e02410b030383c2140804030040d00c1480f074030007442413142d0240c8000d907405481d50501c07030007400c500c155041001044140c0640d4280305080b854000e036251130b590303d8043c400e26541c07982040c2c0020304402d0080243c1e194101c094050f00e4602c00000c080380d049035054a8400303031304104034940151039844900c2455142c44040180300d07005400580401e4500d000b240a42109581e036418010100c0140c00c0ca0400b06111600410860503c030a8004d0b03200680255600382d2a11650410b044800a8104619000b01c00d0418080e20b0351074 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 473862257 1250 473861007 473861021
    0x61707080309091b0f2701030c020316061b030615020a020f0f040209122d060402092a04050103051e190608010e060f06011b320f01 58
    0x100300034524014000000c1648800c011340302c0b000382d100e050184000601440191444051920240390303039100341000e04062041e0340c50711035404000700e1080502ca0740c060b101e42021f0005940185040c00700e5200c1001c0802030000701903c0c0b96072504030003456544140510300080d0216100000c809040c02c07040d2641c2c2d10070b94210401d561150107800c004d6618cc00b0740810216084840c480000c400f100403c0190041d0328140d60040e402d02030311400103030041100000329040803050718010200d04500c0d60182c11450703a46030560854170218002d424211000c0e984030000766000a840400181c06490038400004509411000803405000c550fa1502410b90010b040c038020582480e443c4030111000c0078007030801e00400e040040c440c220411039401a80c0117000120080002096180820740c44040881d05d00040454a40000d15150b010380b0442d0000d80e0f48581070080d1049686d507180e00010284500c40120f003008144100803001d08401d41003a000c464054a06407150000d02c500b52010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 473863507 1250 473862257 473862269
    0x40b0a180605101d0624070606030210050f030c0c030f03070203030609010e01080d0e0a1703070c050d0804060302070201030b04020412050d02280c08010207201504091509061707 78
    0x1c15180340b981919130481036030001000c0303400d1043c1021003849240f8a02440510707804042d4041b4524051003810b50208088070300a450700c901c1c00e8201c2008950900ca4006942c00651040c03010884003402c1c0c4001d0410780ba507940850703180540c0110880c40581089609070b005a000008001103400c0c0b81180a00401400d04c181c411941000c200ca1307155100c903103018003003140112030460313955100c8060200804e0070f030211400c0300300c00345c104940360f03440f0043c242c603c0c4000000018442c18100c0e540103000381c00107880c50034581040c2046019500c0b560003039041540741c0142c05216503c600c000c0c0001c000c440c542042c18889403514a052140d00c2d0042d4040d904524280c000062500d200149190014064200c4080092403c104039113500e402c0031100d9880820018108040503c404040d20f070500d81100e07943c0c403000c041141e040b40308100c5044460051200700f00045c02030f0800212247c00b042203d0805490704584400c46602c1d500600c1c0c006880c421522010400b0300c524805010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 473864757 1250 473863507 473863529
    0x304030614100f1404051302120a170c03090919050a0204030506060f010509010e18010801021c0c0504060f0c1401050105040b040b0f01050c2406120303040308040b0a18060510 77
    0x841c0c5a0004080000c44d0700c814007a03510343c00040da2400845a061030682d500074039580511800c6002c242c3d03111802e05e400c840800e448070700c07020341e298402d0941c1c40710801c0000030340c604174140b001d0005e00302000d000e0942881e1009004241e003003007030007410300c9000704075401070712985142002898040c025120501547c1c0d096014106641e05c48205c4150110a081c03610344024a00c010603500c3d00c1c1095003894104264002140b1282c040d001071082c0301c80e0b51400400c249400c00c10728101e652403c29880410010401000034502501c02c102094069042c21102c400d01504e4101d00e01d040da090601080e50f5410060202c3d2500d40f240e030900250507201080702008903808a0a03456412500c107042c80307000304844c07070a050300308001e5002c00c0050441c80d0b1808491420703c6400340d025140c2510503081c14030b503031600c001c001090704d01c256015555440c95407035584548118440c0a4500e1072502d4444511140041d44074502009451103014001420f240c6030300c034070714410100d81200184070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 473866007 1250 473864757 473864759
    0x7081014060d0b010905090709090602070501140c0307030f0b0d0f02040c1704021c0813050a0506190c0204061e1d06130b010519020a05060108060c04030809030304030614100f 77
    0x60a80b40100d055070801c01740041c2c02c0c0c440074845487c201d0aa849a25081c1c00c10b400181000000d802901000e48250000e0041381110060404449021a00701503800c1d4240300140c0081d2184d0441d00c020013000000242c1c0c0f0141001041d038010302d43d04150303800664007410004500b020702c60b507c40c5548924003592000040c1c4c101c521002009031010b48221780700000c80c0110403603a20b512042c0c0743d005071590754410110102c403040240b90311507030b031003aa01c007140000c0a0420f03500b00d44140351040822015468190300640c1c88020411040c0e8100f40c0c2c0348804030b203069411000510342980b854540740407d1a140e411850040c24100400403c024401070000f683c59000d51132414090348280846c01c0c0c003030040101d805000e904000382103e5a0250629a11500800ea07080ca140c014000d0751804d07131301c07542d55541d510416107404680f50001c0204001003010400500540d0400400b603070f1505039280c1700c1509035090701c013000000c05c1c0310805201c5216180200c00700200200f0404c40905 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 473867257 1250 473866007 473866013
    0x2060c03060627040501030b040b150901090c090b040807260d08130b011d0711060610020106350714060906070501060612141302010f0207081014060d 66
    0x50090014880510780300040075140320803030b100301003c0c0d140e02801c10002036070741c0e007018000e241048e60240c0c5c9400081c8042056580318440c0e1a142450151050010307900e451b14400051807284001d20400202100115840f00c00c1ca000f03000600c0d4800040c0012400c0000030300b903480c2c2045480d04008004250800c0803a0b02181daa42d41180300e00308a00250760744184040e01083c9104000c041480710800032a55080803a446289185410401c24840c1e41d00001035a8403100c40d00001d0043e40440005001880e01d49150042c4e113000c2c0c0700200301c0d10343d40c40001c056044600e4140f024410001c01007130016180f1030b94000d4882c0310800400c5000e1500051018068030b481c0c5090103040e0004e00c0c1d05040c1c0340d92080f102c0685e4020002c202d21a070ba440004e20411103807441140040c03c0c08800406c800c0e07483e80f10740c003c840b82e46084040b644250300540d030346148001c99034190301540000040018090141c5d503013002c40c02401241e14004011aa012110300800c45482100600c0884000c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 473868507 1250 473867257 473867269
    0xb0a0903421518020c3901051c020a0509030604050a120f090e1e040605010608100308190c050d090f0609061b050c0a0303050405030c010503160503040f080f0a02060c0306 75
    0xc3d541e10702c00059450880c400313106d0030b1880d4002c0365640140f400443d0040e40103180e00c41c42c00c00d00b1052040105041840044425110700c03606c0300102d00d861000700d89d0300e442c80c4c3d00030b1a02d64000d04019103401d00b10070200b414000e04a5083e6210341110a47d0780a100c04110200200c80c211302d41501103415100c806410b07a00e082c00740c2001001400005282a028180c2300c0a0b040c081c032841019600e0a490706e0409010240a010700041d03040005c03940000259215409a84d40310040d41c2c1040044505166207680312200c441c20441072003800310104906000101c13445c0d00f160344880c002c42c101080c860100c01d550f40036104211615030308200181c0d0150440d0100b44401040d2090311050f410041d05e090242c000250b40007003243d41c000f04264001008200700c81041d03040c0c414441c1e005e0015541790004688541711801c842d083d22080c1841140250744c01481210484190b541d1501c64540c5900042d903910815413002a69400c015010003902d43d0040d0350070741e07070740c614a0100085a1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 473869757 1250 473868507 473868539
    0xd0503131e022d01020309030d0c060213080706020c0303031608180714031c050304020909071211122803030b031204050a0b0a09034215 60
    0x125591401514010711071010511104a54004012021404011284001d01d04144201c1201000255981c202ca54004010340c1d0b46071100030041c003440440d01703801395042444d140089512070740c02c03c0042c7c0c03603a815120600260441d14000c110107801c0c0340002e40b501e040d022096100354424070802c07059558091098519100d1458940c80f940c0707489211500002c0501200c48540c0122000441c42c0c0350402d0307044550010490440700d1441c4d64084504400070180e0724400081d070708000040240c2030030041a0303040007070300040761651a62a50707038000340014540211203c011544505002d441d041d56002c4500080c003000d4500e9030210310403100302841092408020041c0102040180350113070384107401742c0744007809a4003a240041c2c07030f981e01d5900a00556200c4c400d070100106000e18038106650301e240854884550715811741e2118000341c4841e01641c0c5d9805100310007415030b00b450b0001c0d210310000802c00040f5508001c1d40f4242924182c4030075640203400e08800708000c40001e8142a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 473871007 1250 473869757 473869763
    0x20c0f061f330f0212070c0e041a04030c03170601091503060504090b0603010c0906020304090f2306040e031606050a06050303300403050702040b04200403050d050313 73
    0xb0848080e81030b8414510880c6001c1d030300d1242c1c022000b94145030300a40c00b90303031403d000d44c01e03500c2500020396010014013070600058904440b02c40c0034000e06081448440e0028015249410311000c26074400a0001c81100c00310700103030301e40603e40c0426401a00041421002004070000d5260600000341808d98620540d121440c1c4c00480010090184e0700030005050301500600c46080c00e0b044c004203520003031340c06500a61038950107103421031103400c80300d0035140117034091841d04d8a019400c1e809440e440340b0200341a0b990300c11700291406004c0c00c03e48a60107044162405150050400c0122143c000711032001c0c0e042004050a540945060111200d5000900050f192100d01c484802401c407900081d40500c40000c1c0075809500200144800000b505c44000c283c40c28140c0e10b5551208c2554018041102400300307070700514298001c5030024070042d10000f03245c1d001e6880d00304907d41105444205050008007030080c0b140c01d000c41d44011a090907c42d140d81094044480244031900d030103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 473872257 1250 473871007 473871029
    0x5010b07020f0d15020403050a150c0903030503042409030207171e210309010b0103091509170a031a0406030c031401090803101d2403070504020c0f061f 67
    0x3c070420445000c2d4416866203001c0c21511240c40b413400e143c0c0c5007000901525103118500300f900d02c901c254061074881412541d07e00c0c0c0d450345166015a0701e60006002221243c41507643d40040c15042910400b0540200070045022001c43c21702a00f40100ea800071164041c60040362069406c00081081c416008a041c0380d4607807150860850030001b99545401d41440b1a02d44401103c6130200a1405915400000c028aa0a100043d4100c4500c1c220007001c60800842d00028410240d1007425080c7c0a0764882c2600d03d421084000d66910508100e004250390700b13680024291303000f072090414041034400f0420103046803031780d800ca0611071000510400c500b0034031820b1807400b90002e40b60f49038000b10413520713402d117200070020341446030041c5240350b055141040c0d82c1a8028600350302440d09400e48000d0049070100e80144d40c0da041d00000d030144070310280042c042d1601d01c003c0581011020140005220b0f045103d03081002c0a00184e10864a040303070701c0c0c03180c41d0000c0c401085403504a45 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 473873507 1250 473872257 473872279
    0x903020303070f0201060e07020d120e06150f0907080106090617061c33140f06040603020901090e01110304150c090902120a05090d0e120705030a0303020406020105010b07020f 77
    0x2040303000d07000c66040341550307e5032901030040c0641c0018410304010856150f17845544d100e80d41c6042282c161a800700080c1c0d000c840890030501c0306150f4200818400703002c400301c500340c886c045002d000b0140d900d00005103400300100101640500e010018010070f1900c129441c503c455812401200a04a10720a10118075510104075142d140c01c01c03a03d511403004400b0f107602602840402920f03000001a203043c0800054100040b8411b40b0b081900c0c0c14110845a00c5088040c108104001c2c40d440d0019510203020026076950813880e4000e003820b0740080741c403104116a46003950152503440c140b813401401400f0001e04001c1c5401170100d01058001054080752004a0f494a101c1e444182c501e48005101110030041c800d00511440c10035a0500641d107410f511542e03103204060550b0300040c05101c40f10380764906190586044105a4111389807140c480300001d0500c4051030049000c00e0f40050104181a02030150364014141131140c00e0030142e054021602c1001c12200080c440c940c3c0c008 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 473874757 1250 473873507 473873537
    0x6021c020c0705030d0e090126061008070905040b0f0604020f0f0d061401171e0106020c0f01230f040801020c1b090609013503091503060d0b090111180112090302030307 74
    0x3c5c00c27503407024084116450340c28020340403042d840c070900401d40306019007800030500d030300c440c0a00c5004d154040613076107181c2c0d10411600250031000c0c3c801580300750200048641150b42d030000d002d00c0328429a02696502180704504112216a0303c8181c00007807103698070f055680c0003441003150254620044205079035501c01c4000c4221000c100881c0780c40800d0010401a0340000da881d0003400c00e036032648154182c80015640031080000d804500344071419034055041034a4080d0012088254065003460f4981c1c65481c00d91300400100300e2180e0109200154009014210301401e1605607000141d034103107040800e0003102c050240003000c28160404070b075a1204a490440e030102610310307801c40d00012a82c61a100d5019a550307601ca2001c2d40c18211800d2000b504480c0580c400074415980172925640c0c1340240b04008204c4851556144040c8104404e610001c1c00c183d52100b0194810b0b05000e00054010400b08250300c0d19549000c08032000a03400004407500800907040820110003840 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 473876007 1250 473874757 473874809
    0x705070b041e080a021e06183d18080a1e0801171f0c05070c030f030f0f08070809030904020c03030a1b090306021c020c0705030d0e0901 60
    0xc0321840032442c0d00c41c80c01d220050380989011601d03a030944155034410285400c0c255a207120f0107180c2d13040703100880e584030041000c3e21a2070074180240c40340ca06c00741e034246101d005000d244941c0e034007501011b2618035800007801a402c0700d43c01010031424a6001164108040c512401040d6a038006101b0008074000c0701d40c0c2000607080c1e8440d61031419034440081c08048280300c3c00c5400e402c041d280f411104008a070082c030741001000c41d0b02425140c450345e84043c0c24200ca404082c003134100810717404221181000720185010728042c0314140803501e801440d96481012800400c8080031103221099800420345412501d01c0c58140070b02e40b20f402c40309003148206280643d001b03200184001c6030030000300185200314202002006400d003002c44100d03c000b4101020317130008211001c10710002d06e00c0d0340600718685011035400215403181c80244120307808508e004555a10245042086107000c01004004441c2840c002881c1d00c511004140c851078180206445c046868403500301d075034014 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 473877257 1250 473876007 473876033
    0x11d0607120f020c0c09060a0602030d09230d08010f0605160303020f1606050106020f0723040903020a02130e070605070219032d121d060406050a0e04050705070b04 72
    0xb810455071120703032010b00d50b92402400003035401200c400c00003c40c1481c1c004e4503c01224110b030099403904100103400e130020003494104a81041980a103081c03004d400c04030f10705860141c6e01c000c00701800d241030083c4c101c1405070700080784c03004070f80c1081c06016400b00680306c6000802e90046154242032a06601038003409075041d00d280070100c0c01540610150340c500103d503014041c1040580d0702c0d440c0407a102c4903485c11920751580650340c1000800c07419003040b6020203983c40c00480c50b00c401c0c0002030076198141010380c016440500340005515102c070640c07004c0c02034400c00700100d4003a5010283c59040c83d11a4406108012600e0401c0d5111040742d03900682003941603801e880c1c0c0f03e2428200c0c80302c8080c0d01c116007501c624400780384c070706841c01d241031140d800800b0795480c01c104a10444000032404810104100c04035030003506900d0f40c401034000b030041915200d4403100c207240000c18003000400000c0c40380f070a28043c8442d40b504030b012111426000142001740350707a2410501d40312155 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 473878507 1250 473877257 473877281
    0x60c020a080f0714070302061c0608070b0705250501030c05040b030903040f06020c031e1906021c0603020f042a051b0105100e0901060e010806060102011d060712 71
    0x1c00209107036188502401020340d980310703003052031042590200c850b07681c0f4854000250848006c111020014114440c04409145042d0340481d069845000e914108070b0160311021209401003040010054140102d8005c1401000d10b9612082c0c420340a00e040d065620034541890b0342ca501140e2190b01c0382c000c80d40604078004040f980c0341407844d150750f6240e01a21030790310650181100031544600c00300f40000d9120f0f00034000c3c0740000840c01c0080c40b031910f8000300c1c1d61a20840d6000a0a40c000041060300b1901400c00140c48807c2a010200e000c0d22a41401e8010b80c9491421300041c0e1300c40007841404281964009407000202c158088802406400000040c0154407050540f5038450001c1032036061618022031a4183c0c07406050a030790301034401840640e1601f405010703000503111501e5110306103d00102d40c445e915060008001401e0b00700c1005600407008200e85942c09000b110620030841c1c006120852001e5003032501d840024003510700304116400100540035080d004180e610803 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 473879757 1250 473878507 473878523
    0x90f15021213061803050d0203070905120d023d150e1b2d0918041109160f120609051b0906120a150b070507140607060c020a 55
    0xd29200b06030203011610012a1110700b0041c51500c12003c21003000c40381036040d11a54200754110841d03401039000201407600308005050006101e980b003001003a460101c0001401600c8481c960090030030b10301c0b042280112000400c01ea544881d00c8a0001d03141c41d40c01c25154010241c4a0b40401809002c03c038484900c05040300810381c01480c401007070041101c100c6412840518084c0010310340260b517070507056400340188110b07440c000d0740981c0059040100034945010400e6000803245407841050039180d006020400c010040050030401110004070f404001c9480c3c06100c1082c06070011040f1800c208a0400c00520030b400b605c1540c00c0c550340340d84107002c031070303262080c1c100100402c81e1003000e000507288841d05440700e40b00c201ca228880103424103103041008825198922270180c46002410b81e030340440000c4000500200000c1c0c00400b00d07441da0b800f55414914500130f0a40c022141802059800e81825502c4008580009074031017408640f580401d68107a0801d00705082c0a80401 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 473881007 1250 473879757 473879761
    0x105161b15030501210807020d0602040f030b0604020702060405190305100c0810230f120105090609070510120e01050a0c020d171323060604050a090f150212 69
    0x84800740d211044119030360200034036a40c1d681c05075002140401a450310000080a180108860700010a030440c00074044000b01d80241e61020203e071300690000c148503686045c14401c000c0c00c40c05003500180704441c03d50602d81039800207012441544030340d074812180c202c03090b00e01319406440580111b030004195104240042c3c07010018180b007854072000624000d001881e1011075207081829202c0455182c6501c2e4200c0304009600c03030f07000180c982c0c0050800510b40481d90350b802c804819281510010138039003481214146040b001800d8a1200d8101c0f0005101e2900d0b100403860106c94189170914854044180c2400245940f22a0f09600d5081c281006042c030415042130f00d123100a94200c444203400803070220b42010140d01103000303d045040124042c000c000c00d1008210f0b0144412800d2450702d4441d00e25502030f0100c440030141c02c41e40c100300d003601d01481000c5c0c0c0020f2101050080e10031550720300740c110070b034084024144071368100c480c44594040d03819240505101100c481c2e00d4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 473882257 1250 473881007 473881019
    0xb0a0203100506070b070f020307061109030c09011404020f0702030604051c030c02030415020c09040302101512030f031508030309010509011104150c020a090b031b0105161b 76
    0x2940c8125080c01c4840c000308800286410090f0480d01c40c150000380e0941503445000040b5400442950590704512007030009a020036200c3c071a0b1044402c880398801d580c0e43d103d800b03150601d500000064071a12400d0010000c200213404201d06880d001c440c01680e07415403007203a45460003400000f9425110340c20070030080201c00038a0107264600d4215490f044400c200b4100c0c140c03200c11428400507007085c402008602d1480380b0407801e006980c015070780c4c11046040443c1d0340341c200f10b50a4005038420a14500c0c080340d6441002803110911400002c0e990414042c651841d201c0d84008040200310707020180524841e90200ba28160020107825081e60303510200769680e001625501b07465482e00b0007003058004c0c1407003905035180010483e28240740c90011040c1018081c8807011007400420000280160340f00300598014110280b170015142900340180351600d01815084a02090120410344403681c10005a5043c0d071328800680c41250441d1500800f0340c196450301d40000c0c46010000310348 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 473883507 1250 473882257 473882261
    0x5180702160e0609011403101503051204210309030f020f0303040b07110936011e1b140d02070203010c030b030d0801060804030c030e0d05030a0e060f0d090f0b0a 71
    0x250b0001c0741c80c80407a03600e1b8030050310f41d10f540c62075280e4140d1007668880c0c41d110403038101c84401208102c014410b2542c0392981420662246079400000c1e100113801d00041c2c0320810310105004480d25401c0c81d242c0b0b41d95024080100e5404017401c1d02000400d40c2c021551195084d020045001d0280d80c0c54655480040d1042c2d00140e0089900f105128500501410502035091103008000720034120400070000c0401d0f00e001d0840710703900c0404920105001248240982031417401c4056584c0581d9a032010f00c1000c69801d001e11050a0100c3c210102a0540c00032044640300300c805120303556011401c90200c024070071200c0c025015400c14001c1190181c041d40312030004141a8250f50107921305141c01c6030312203000d00422010485860104011078844d04180001d40d21900705110b1160388000000c0f00b52020040c12101c03680300055810300c041d40b01000d01c48850082d41e180781000240c400c440854040d580d44400c03142d5803085c9180a20046104e1841010380104c1c50002034107200500c1c80c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 473884757 1250 473883507 473883511
    0x32004020c1e0c06090612091e0705130e0d0f0e0307032303030f0c0a05040e0f011a0a0509100201060b0307120b09061309210512010b0405180702160e 66
    0xa094010300f5144400c506014003180e5503541d000306000c0c54840c20321030300818070760050040840b5100320b841d20b072040d240a0304072440c56401c400051074120f03c2e007000c1000499060400803c96814082501c0a4920020310b03010785031303c40d003046100f507200300718115107014541c0c1c02680d162044903070000501c0000c0c81c80796008883c4d009201b4000c040441869a82c1c40190f5045005045c0d84002502c00c0055502900785031071613242051810359142244c0f8071a60003a00d240030b00860389801000400d06402030140d90554901c03410341004100540581540105001d0300c1c0142e00031500450494030079880f6101401100144688908041c10000c102080060a950065191001842c2d0340e01c0e101c800b2030300c40d260092414420341030700c142030b40281845900841e54046415060040c05401c0902600f003514282e50303842e1900c0c1c24010001d003d00e0181c0c000c0c070041408000038405a00d8240c0f41420200d01c5119414403520f40b11001c901d888040603d400f1801203610f00442c4880780340700058 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 473886007 1250 473884757 473884813
    0xd08131d060604030305030f04080d060b0d24140d0507060906110a0206030408070501060e0c0c070e09070e1e010b090112060e060d05011b0215010e01032004020c 71
    0x84581d100390034800644502d000c081e021401c1800012210308a0303078003040d480751003180e15505001030b0300c0c078a5081d51219000302c0100c040c08a40d0301100c410511075980c00120b50343d154a60075030140e4000c403002c0b51034011034030300d07042c910f81d003200644920541800f000d0f48002116025591400010502a401c0c06928005041428030b0980804e00050503072500c0e8004041503e151215034804000c1d6005940c00c84495407102400110110340d092820300c03403c5502c0409070340e00d0101003481d0520300e242e0400c0c03505908010034407074200000070b042c20071745000c1c03129004140c5440180c0c501403080c0042001c2240031080011400d41600e0b070103005010300030f8071603c0002c42048402c4060394160300070100c20443c8100000d00c18a8042c0003e00f20760701035000002d2050050184a005c1c0d01d5400700070700568011945910034002a2070540d00400010803400102d50541c0e40e068100f201c03244140d9541e81d000d01c40350f00151354039411200c0c82000181221896221a8000081d01007450703409 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 473887257 1250 473886007 473886059
    0x20103090f12140c0d08180a0302010c1101050405100b0a1e09050f070e27040803041a01060e0d060e061602010f0209180901020412060b0a0909110d0813 67
    0x480c611030096805644140300501780f00414040201e841e5030f00180030b20101c0008206000d0078035024040b41c50060300940c004100070298040107085001d105030347e000c59038503080030480403510105068105008540c40481c1031303410a000500d501c1340d0790b081216070f03000d8048110041c100b034505000489030007400500265542120301c40d070364031084408001181c48981150f20724501100c58902c55110346420720590003007203c0301100407070103c0e0111104000001440140204056078050030080d03d02540c01c90740c14000000c00c1014042410b900480b000f03182002000943d80080440d0020304044071082d140c103074003010340030319052040e4025518041000030b40840500803a544101d0180c400f110152188180000001006180244d507540c20301012652134905558018414001d10b00801d141810904004885819511069160b0700d010007a000241c82748006002020301107540c0c4501c0304107402c2140b030750f200d241110382101441280105d00d1031049450008003124100c59 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 473888507 1250 473887257 473887277
    0x1090803040e190e150a060b0c070f05060910030509070e0903030403030b0103050c09060d110705150105010305040c27021b0f0c060714030903031201090b040b0a050d020103090f12 79
    0x265030110341c0c0004d9040030a030490740140c420a0360310051a500300c092090f00190440e590b44a02e415078104000041181e00070940070014403a103445281c020300ad00f11842440e0120150000360002488110502030584810026801c0e03002072001800405201c0348421491601c0b8035180c0d00c942c002c5a04a01091402c0451155540b080c894144a454128a030503d44a02181049440d1700110481c26513a40c4485001034860184800341400501c208000c0c40010554a008941d90005800440c1018a04030400001c5800030002800b10b90241c801100789121201542581141d112b0f04541000e000044804403002c0c0704503007142440384001540d46002048102a0310350242440c01c65001c802404081c000c00c070840306488559a4510450745000c0c004008031f41150080b00c1d060041400d00c60040089400303e010300205100212402c200b440071020018841c0f183c02d0180602807184101c0075001c5900135402014a41e030448070058800f40b80d86803040c00d14252841c02d90010b146901 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 473889757 1250 473888507 473888551
    0x30412030f17040c05040b131416051317150709181107020616051203010311010c05120a0201090c0306061d0405070303080726100f0b090f01090803040e 67
    0x40b40a001e598050301d03103100c1a00d460b080002030080703a500140e0111050822101040f40c0c0d2141a030380881d5110703622228540074440412400c085504107060010400c060354035503059500d101c0c142c5256070704004c1c1c6c0640188501d442c11102102800000c1141c800388044150040c40210854440102c81c1c1d0900341e01a484200380d4030301c40700403048124241300520043c900040980141e007000c0c001c1c1713004480a6243c85160282503450b140042c18000014828001c210b00d481d5a40982030a0180c1c158149698143d80e07801d002450001000e40851070500c0d0034400c5d0801003250703820490b1007000c0e903101c0c2424801002d40c0d02c140c01d814104110f01071010f1102d03204251059030458050b003145880c40d18259110710b00141240d0422102000890008100034001410903905445000207460b00d80110072075144242c001810f28508402d003000f0741e0650750211202c04500b941c01404100b80300c401601d1740780144e0080a000e000115022414a104c010f03064841c58a075448084c01e0b9244003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 473891007 1250 473889757 473889797
    0x19090f080c03030306060f0c030a0f0207060314070c0318061107060f050403060e0106051c0228140609042406090e15031015060905090c1b030412030f 66
    0x3415010f40051000400501c1c2c103070b024110101c1e004c0c0040c2e181890035180d050079a44198440340c00b248002d2003501d4210360400c0644c01405450808100c0b190781000000450b15004002e4010000300314001d0007058815120780c2e1140d002091450300f46a00e0300d201a01004412148086500c188400007031080d00c503894100318110380341c6810b4076260450b101d0750003528040b003c0d00d03099925400e00140b2034603000038011219040c81c000d190140c0c52441041040300483e1a0868a0618600c610000b4130110465108980d01e8001040b0b02c400228003007800e60044041c16a44a841c1c401d4209112040c81c8007a0495404044c0f2201180c0c0c07100d205680344641c0303001c0c004001c00d00000180f0044ca400c80d640b0b070800402003c85e042c07200030111000a5071101200503c0504081804100080d0400490300103000c046a440c0101d140008008489000e04e421100c070f070540301c8008480b01d030706c00e200316005082c1c03043d20080c0544403414041e02c4458013445000000d01513a0b0701c245080149 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 473892257 1250 473891007 473891023
    0xf0507080d020114060906060d110706092003060a0923031e1c020d02070b18011d0613020d20120c10032003131b060801150519090f08 59
    0x1b080311100f929030700c1c10701c40ca0380c00001507101055501e040900100d0544d60150018a210351000320f11a0540d00e00000d0301c614480301c2403140e01003541031943c69079000c0744040e403120794039200094825007804c01800c040c0c24001900e10910004c0300e07648a009000c4020040360702c1c07070130340100c14080d52809203c0911420302d880281c0c2161402150041b400c50b0001d01c0d0350820410054180317441c5443e560b043c40011390b07104210010f41c02c0f8442988c0310a005814003a0399003003c80001a10000d605904c03030500401900300c0c010590740c19000c551b5100c983c4602650402c00c0039410342c50041d2001c0c1d1518820b014240314440000708081064400541c0100c0010301400c80c0c020b2418588003a00a0106101182a071122413107205100c200c0441c0603502c99400c001d80ca0805189900b460321040f040710720b04400540901d2010f1007140d0304200300030304403281c2c0214280300c10546141215540605490020480d80440e00554100d078000f02d08025a2444050803d406d5078503041d6540da2845 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 473893507 1250 473892257 473892259
    0xb030109050a06181b05130b0a020304170a03081005010c140304180506040507030216080a02031606050f0a0c0e040b03010207020a0f03060f060f0506070f0507080d02011406 76
    0x10001488440c0c2a074100d0740d0031980008001c03500945400b24580980c1242244041c2c503540c5005808403110520302c8041c50031034a0800f80e15200e0720000c1424410494054480310550014a0160321482041260007c040d030001c40c940e0200b4074a5120b071900e0341588181e000402a00215a100541d4039905049400c141c6800c0100341d15556095080d480340d4a001040c0d0209020010740f28a80c0320341d62042541c0080005502d00c1d240b0208030440340043c00900801d0310610445505100d00300328a0700e800e402007030721526420307140e0080785907200e01d401c040007403c40b4008003810010250440c83c060381041d400a405030759035528180450b0501e1034850001082c1d0240e1130068185a0701915a004010b0700142c41c0600c5a000b04004003c598082201c2c00342050042091141703500c1803110100058500f804842e240202d41c91501a444c011035210b200d00003880020044003640c110038041e4050251041c80703581e4141551510800e40504016508104208505005c594805441008 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 473894757 1250 473893507 473893529
    0x60105031603090606051c1401051e04110409111002120a1409030d0206060a0b070b0103083001051002031e0903070b280215060108090a0614180601 65
    0x7000780c2048001e4282c03200c040e203120341c0e1907a002c01c2c10380383d085500b035049103c201103088104c040d1402801c01c042030510206140d2410382440b0080105680140100c900e1561a25443e01e85040121081d060305900c65031003440d0803d034a04200030a10792105545040300d441082c160b907060203a0719400078128001032441d041010901d2140071300c3c450314100210580c900d0501c2132002c08a0721f04400356622070056481001002118a402041032001e000301025850038000c803030b6a021030401c07040c00024401a408034881281280081e6001d20b1564425000c0003204018a501c0d020540e00780075980c0038070b05440c090050240000212924500211041c14010140c012184840d42019100315410301581c41c00064599418001d41034404501102140550699600a0040d108110320a00f5908650041950f420320700c80340300d600c075500b0f00f0482c04941c0d6080b10345e0301708407002800074906403400e43c2c0454244501c206652164100c8201545405c5034851002d80e43c40f001d100343e208002c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 473896007 1250 473894757 473894791
    0x1b0c2d0504020c0a05010905030309010c0906050315010c12110c0a0e01090b010e03070f1404050f0609041502040605030f1e1303020313030525061211121e06010503 72
    0x82056801400f0300050035081e42c8001c038469449a080d20024603082d80c40360f00100611808090030301c50303850003c0701410600040740c40c01d103024203039010080509080d00000b84010042d0790080d001140040e511400c001c180824019010f864402c052044903000e21541c641c1c03032001d0034030a00c1c0405840d40030902c18026071a11300610f01405280290504002c04401c0c40d4102e62410048800541a416030400e61103007000040780d140d940300d026a910a904103001c2c17000181d002240103030062001d941400499450b81004000c550341c0c05450468103100280c00244107a004000c2d50040210888803051512146c8a103d82501440c0c0031185056031000803a11004a0b409a0b404052003030069a0a00d004008050030001d084d6100f950150014880f10035045110040b005030203c1c0c0d51744544a460a1040040034990b41c0602ea0452541d00c1c00d00280035501c41041e94074808540d60b070740342d0718a0f01c9540c0c1001c1070040d01300320702100302d03002c00300301158020019030344250800c8020003061 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 473897257 1250 473896007 473896009
    0x9030a0204090512161406150103200f0909010b0406050909151305061807300218100207051e04141602150903030c07031b0c2d05 57
    0x10021000d0450b19840365140f082004c001600103001a15103641c0744141082980c18150041d003690f02030840e454000c0c404000030840c030006612110030302032800103040c5a00d4207001010302450140e0848030040425012004007040703005169141054910681c0c0c1d9980d041c00362007a014600500b0003091087c07086065605085d85c42d15400f41a0b010000c2d0759410030000700d0401d00850426114683d00c5808000c0d031801e0262030915900b085250800040c503200760020562140e031544a100240c2c0c04038541030f40524041240c091000d0b101c81190707903101a1085514408126940742c0c0224001c80703a40e003940e40041000002c4410141c41e4002d5959161101c089116000300340a5116a5511580c142640c00420961250480d400c00390740325002031101030300c2c003007001840e00c400c102c1d00010002d6070b400c08002e498004007016412502c0304030a180c03d603280070b00350f00c0b504004000440c0354414450b07086208001c591000c0c04030544e40f4641d0300e10bc03c0421001c1c19818244071880b0080100e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 473898507 1250 473897257 473897261
    0xc05090607030f0507060e0105010e15030d030c02030909090d09060804171612091e0810090507051c0209011a031602190305030f100501170a1d030304061109030a0204 73
    0x36400c0a190103480d00f02031b561600300712100f074400d81c00355a540ba4011f02002451010b12038108824403980e407090a8403c002030f94460326210f82604040d110034220134501e0081080e903c0344880205802410b103000310703020b641d400f5118001c400182a0080010756203018498107800b03142c1018452030554200b41c1991100d6201c4a801a00c01e100e580701200420300d800450f0b10001c0e0360313036158403801e40346c8006c821002e0042c000404051040000401003204001099098520702100c045030b04e0f00a814082d040114990140741c00400a800400c01014400ca1201401e44211141c003030903601c0c3c0c40010801c8401c000000c40c0b039117040003c02c0361078048901ea549400a584100d400b22403500c20350f503a224450140880c00b20300301200740300e420905803a140742e00c00200842034a11a180900082c0085807180c00000303d01402c001041c5071461682160702c2c0308182d520190848840d0040c600d035640e00481c1c7c2503604500e0282849014402e0314112400d0080040c010301c0d640e5070170b40070000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 473899757 1250 473898507 473898527
    0x1003030c03050f070b06191202040b04060308070b2508010e0402041b0c03021c050708031801050f04021f050906130905040305130e06060d0c0c0501051005040c0509060703 75
    0x100340700003808103a03d460000401450303543e110b665809402e042c00790030302c148508840944184000581414003214070055650f50080f50111004191185108081802040710f500040c1400200040c2c14090100d1108018020b01c544c02c446252460840031030504903400b41203a17800100720070b0040042c400d80081e441d400ca400244000f4072203100b81030142c28040754040100c0816200340e40d15081c9601802011800ba0034000c42010010300034030000d2040c42542401040f003031002c008501001000403484004002c585d008201c03a04101d00314003100001190201c0c458400504007101c120340c1441d12440b41c0d00580c8405007800003060400030141c00c03614850340741000002d4006201d000b14001c003800b070b601070f8985030b90b07400e0071640c010740c1c6003110f40006120389582c00a0290750303140c402c1120b0301c03c200c42c0c00014680f92aa60700702c401c1c1c210720901501c9036080c1810312007261881c10340c1c5001c40d00112001c0069202ca004252280e0240049980d8070400034080c0d03401090003010811 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 473901007 1250 473899757 473899763
    0x307061409090a021603030c0207050d11061c060b0301031e03230919170601080303010302041a090403031a31090c061227030e04060b0c0f0c091003030c 67
    0xb60400710108410100e4114145c005d0300000c0e10350f80c3c01200c841d01800b1100190406403070500000b5825104c601856500100c02030040300000f43e1400d40600001045040c2c81410000780030710b50340e508002c013094200b800141d903400342c54a6090422440311650f03201043e895200c1540b161440000208070921414001c02c0c006010000765080740d13141d1000c0540b02c0c0501700e075106594180746544200c296104000d0309590b100800511826600000360fa045a0b412030b408100043c0c08181c036040d6290b014051a044a9020300340004c054040d00a82c4910301807040a40d451010b107010041c01051801a90108000f00a4021001e07410004000d01410302a0004144880b156407000d407452031030341c810b1000582d4001150344140e00e03070080781c65540040c6800210303003102a06441c1e1042ea0454000c00344940701094005940b110f400c208003c1c6503540d5001e40b1040500421a00c408200da00c41c40301c1d003c2e100c03001100d46000c89403640030b40401051480407504603034090703940360503481c002c0d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 473902257 1250 473901007 473901011
    0x5090319110409050a060e06060d11040618021b0c010e0405090a022806020a020a090c14030c07020f03070e0f040311060711010b09160f111b0307061409090a 69
    0x1501c942d85507030041e000418420001058000030b5800d028049883c103a500c0451a00070005100040d624401c05075184c980201940c504020084000740003080c003030380310100100313415042260506861780a030049845d50140030040910b4070321515141c00b5441328080c041041d03006500824185907026039400303002c1d002101c020341801d400040c101150a0f0513041100c664a20780c03c1505082c510410042180780001e14403034009600190f201d550500640c038959540e1110340303411138070a101c400c07000100400c0965403403c265030f29003055070002c0c00070307030044500e5030000802d0b041c001105000c50703010a01d4102651039130000540c0748003010704144e0800c0602c00007202d94090901080b030152080e178a85640820010148509442d0958a264407942e090790800244103000701c60350701c00e065180380141e407607803600b40c0c140d450200302030100d07070540b0582c8a00511150a54441c10000b05c04608880c0038030340d00c4e4400c90f00001c6a055043c0e1a44084c0138000960610400054011514040c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 473903507 1250 473902257 473902283
    0x3090602072409021305060324090706050c0a1b03120504180203040b04021003230702010b030a03170c09060c07060906030207030503061903051e010c05090319 70
    0x4040030380c1c014403800e9aa000001c1510341081504089000b20001461018805214550001280c40e070b218100320080c15243d10018440da5800e00211019941e8010300958820300030391018410142107481344498413550101089050164095404004900d030050020342c1840e920506410030100500912000c086000310020346000c80035841c0c0110340c0d45041e01d4916256580c001a0071210074400c00e684104148008100c120100f81d91007601650002c90380302e40c40c0400c800070843d0104010980c00d050000040c565144e442c103074055645a4000d1000030f01080406440305241d140040124144078100001520f01124443d400008039884500b014400e2021a009511101004e181500700b5030741402403d41000c50344010b042c0b18903003142424480d0381d0250492002502d0203104e45d960560b01c00c07544161080c0e1902a551040607240a18518164041e01d088a2242c1030b0f11542007903802c200203841f60b03003580c01c106002401400300040c500c0403c04070b107107120400e6810780030b00c0403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 473904757 1250 473903507 473903513
    0x1030f0219090509100504052d010f0b120c030a0f03020313060215011401120e030904110a0f080c0301091d1b03100e0d11030706140115090f150309 65
    0x41040000c1032094408580d031300e0f100b5446410040948408001d1915010600c4042003000a038881000e5400b1200b003541c00103100009400b81c3d8034902032107030307608151403019812401d8100d0020440c007a03070204003460100d03184035280e514180c01150180e0000d81d4607800b0882d024041e60616000b4010f60b03141004d450580d9514001c0da4002c5d0000d80d21401620083d019880b00050040040c081c0005980c0c040c10b000030001d114903c50203d8030f544030040c0c00c1c401d001c01d000300c90ec2424020000c12405050421303c482a400000c65031010a400811984006019071022803103034012106182c0786031f00f401040c130018608220000c040c02c040d0400c2c0e0a15a004000c3c0000040018115011484220080602c3c100d00310b6083c140e61401e00e04924032a400001c3d40b910050840d0620941d50b144078001d540c50f5005504000d02514101020711b041d10345142d180506032051500300350500400c4090030740b10441248550105025195010000e1000450900003011003510380400c207105991 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 473906007 1250 473904757 473904799
    0x9040305073003060513021309091b080307020f01030c020a0b011815030503090907140304080304030806061201360209010905030d120207060212040f060f1401030f02 73
    0x11040041c00082ca40c692100c2d42e8441001d506240e0482c039041c440f6609140c00700708404410340c1b2141200380c0114101d03070203082040154000c0c101d501d00812981c0c8550600c0903007070041d80c45c40c00400e484040080780740340e008070840c1c80041d000781642c10080515001100201205040d06045016003822000022281d241d03060080070340110b41c40c1c01180203441e800841d020322602440c010764085041000031004420340b0940001100c1e801c141750303140c10003074403103018664486810080000401003000815401346002d10700030f42c0c03500010760310102849503078070070081010b11b0f41410000420484c03025144421000031103c20300b440c00140c41412142c0c40b41c55034022201141c02191801481d6032048403c03004180c210300a00d85072103401c0014000f03440c1514081d0101e50002210014003050303404030340c0e0300a6007000324071407450641003050214800d4030703080300c44904103003078002104e007030380104074036000c01a09116090340b840d0b9030303800020440007080741c00c4407224410503802c103458 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 473907257 1250 473906007 473906033
    0xc08090d0e06162319141c020721150b010e0301180b1605030c0d0615020c090c091008092b0e010302070c1203113301050105090904030507 61
    0x40c10f144404101c409400c40d0300c40c405200390781c0a0b0340c4070205182804006146040c2140c0d004400750040704500d006d86400c0244911180d154032161100b5407440c00c0d80060003100301e441065100c2080d09400900e015120500c101c05080c0103c400d84590001490354868142d201d0141001850540100b01090a60311110080c0c40300480c032a0440b03060000c203d42c0c4540c0700c0205404012011000c1901a0903408058010f8428100109440c1140c041d1648581c0180c000d14203813180c040404070000350342c3d4490f4000c0c20b000c1c1e11100701141d1407100080540e40322400040818810340230f951821211034100901c0500948110031403514024010b803e0000c4a2003e240412841d006100c800b8150b03021404009040600c10024400416110b92841003130f101001044001d130101801d04450300c050400c0d0340741c8940110860060f50000f203190b0020408400c045070101e00084241d0405803c8013442018045541000011118505040010307880780c0709081c9242008883e84442444d00d80c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 473908507 1250 473907257 473907263
    0x60106120b220b030f030a0f1107050d0602030702011401150302071b0807031205090108070813020907081f150f0c0501060f0e0c0a090b03181507030c08090d0e0616 72
    0x107283c04044040c1030910601c6200b03d0f0200c002c5144c01c1141c1300c028401c4582210720810403030a00c504c800220020302c4220000e050080c940b079581d61741424400000c2d402940c003600590310b400702c3c59042600f0006003904071a18080251880c81d03c0c0b25060700030b0340c4107030011224103c025955206121100d9070f0304000e0080e41e002030450604600c0c20440c21a03009800d0303814407906100600003a0ba1218100d039100c50107103013a120301d0300d85499041d017102204400a41c898825400c020b015039000b51914440c80100f040300b40c0b108070100d184009800e0074059110004c408030314407440c15000725401c40a2060900d00f80c01042c05c60740b1114211616078010f10080b48030000d04020007017080320313aa600003680340c00385490441c0c01e23080904800400d100d180e940d5007010001441045e0305015901900080b00b0036a845c2c01200100129442c0c0110b40c3c40e004a0718010800700c1c0381c0e00c00d208040c401c1072888020400301c120480140c980e01e071580b03041e541c02103041141d209034044c00f201105003248 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 473909757 1250 473908507 473908511
    0x1e040c23150a0f02390d1208060d0305340803011e05060901110309040e07080607030c051206030a02060c0c040b12030414060c0a08070c0602060106120b22 68
    0x71848402410244900180c03c01c5520a82c3c0d007020042c080d11115150a64042c0d03034400d04000004400c000c3c0207460b60003640070340c48080d030703d080c07110001c081c4440406039520030300c1c541d17074400801c44c0b01c200c50100500004d20502c0030720364907004145100c0f0460f07030346040c01040101c400400c540c50303010307601d0803180d1180c00b0004102c45491500d1110700801c070300051080403410000418058007a0b08085410800305410056001c0400e004550011202400a0140d000100c92540d502c0d00148545000361280c10700044041d4801e21400040c02d01c169100f514001d090300500880d000d0203004251705000c0e2010020040c0c0d20700e801810440144400751254024080070481180d40d82002540981e0101448502d0300c000881140d060ba08804a9180c400d209000030030040d0003426034008061040700d00381801d00600c80e019101e034510501d030702c4038580d8a80e00200e0329a0028440c950100d24042da0f01c03681020280c000c800d40700400f030031a0f05000c540040041c2c0461703203030710f404292a07 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 473911007 1250 473909757 473909767
    0x120304020a0e1e0906071407021516051009081e0d020a170907050303040b13080601090501150519110f060126010204051008090f07060201051e040c2315 67
    0x30b90b0185038081302c04400f801440c6021800982050500100d01c0c160b402c00148070002c55580c000c2c0080f40c1c00400c0c12003a110341d035150095240080040b13007030f101403003a000383e6001c2045038040d01060a034481d08190802d10b0214810842010807040c040c2c044006004e80340b0102c0c620310140680700c1c2955103881c00d0000305500c100300040d018000c91030035004000c040c4100e807400421241116078404c1e10640d6000741803285894010640c1246d030180c001c950000440c103200e0703003007107068411b00d05905c054041070040a64061042809942c8841d0700c0715170144006005000306244c556043d8203a54280e10140010741c1010400d030094007503258000c00341c01c0d4200d141004105001e403170900840c5040e01b40000030b000a03c1c4d010024080017183c000107810780d40107018002005081ea01112181500c0798406400f800046511400454422076104c0203072070405949400399070004804001c20303003070251400510740d200301440f507110140c202240c0c0319195110410b00207200440d4440d211 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 473912257 1250 473911007 473911051
    0xd06050403111606140901020604030809030403080d0b0a05060c120a03090b0403080906010504150b03041707150b062d09030718140613090516090504020f060c120304020a0e 76
    0x2400d181c055603103417103401307100883d1166000034090347c200f90141058800703607980d40c2d076542ca50301c100d81000303100b0324002c2070b1501d040d4099002601c1f41c4004880c041c21a6441d0781c1441b101340a00040d0340361980c441c5014510040c1c8910040000403d24a000700d1000c1264035a6600c48000fa0340440c00141800100000d06000b803110034003420341110103020f00014013212525000250144840240c4000003203010031101c44481c65141d60007810494554889061541042d03180303450b0260942d00f08020030f46289807400440301180e1201110b500d10380329a041d4440c0c00018590014144030003002025155a003c0000d0401007028416020005212201100954459090300b04140d030100d020b01c00190740300000702c26454503c01300040e200c04142415858480e8490071040c1c6c0428604000c00c08294a4200a101d20300a07079048489100d00300501580f8411b00d0241c25150f040034100580c4030b1804402180c0150004110310f100c107494032120403000710b0136500c074400541952502012 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 473913507 1250 473912257 473912267
    0x40e0615160c080303060112051f080f0f07030c090218191e1514040b0d1a12190501060302090a050906070306080d200604060b0310020301050d06050403111606 70
    0xf41615074003450540c1014000a440310601040c01500f2030303141c1c80040c1c0c00c0c01461500e00030042c4801340520345595070b40d0000342c6800c2c03401c940e20400c5c01510107500c1c0500c070000304807044903808541e09036001d1905c4c1045000f90040c04000400c402c403078103000100d076640d014128418602040b58012070307240244901180058003004d065070345010b0420080404003040e08510b40d03e20381071280e06403c8003400d10140344101e03005092622804903201d015043c05600111640f440c8045071003810048000300004904002d02409031035000094603900c4402c41ca8240d078034203200380000710340c041c0c9980c0002d4202c902114140107865a601c20000340e07000421800c0c2e0400c1d03d9007410010340c1c0c01c0010741501d480549403860244043d111010240200c940c1003103007541c0640c2c00b580d0081c1414038101c0041c007078a84407288248150304124006400c1842104d0480c0c00091400f550500030f80d813000c0141100400560a12095640c14000d1420500c513030580b102c1000200521170303040980240c8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 473914757 1250 473913507 473913509
    0x28020903011a01090614040605030c0c070f1502150c130b070812010b130e0c0c0a0f02030f16052403040b061509010f0e040b06130807080109030203040e0615160c 71
    0x100b2041da86c1e80001511460b0880e016109240f4186959075500808408148103087c00d66501e481500e43c0020008400ca40000948042c4210026a6280313810100d80d104203001c12441d424065a01103076100c41d5a000405490700f1008a03508050f40d6400e0000403034005403000d941c035000000f030300400040003d20450141031541c00713441c140b11004d17050a1502c005030081401060400c40800c80101640043d15220401c030000c42e0f007608203910341141c1030614504220b019101c0c80000010b026070115a0310b0621400801783c1000d9850b00c02006031440c082d0917000f08035100d425900410303c2d43e0b81c000394070a0f40a0003041270305042c90424003c0d1209105000c4403c504207100c18052aa40a43e0810f0450500c0c40d2280c403841107800090011306c00180d1a03940640b0000e410194080c206100c0d0041300e403500b0a546825581d0461176003618020f49000b401a0400c000600802c41c0480c440790300b02001030400b2840842d280c21002880c0c0c480e2402c5c141c0c2c101044050020040d010341408 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 473916007 1250 473914757 473914769
    0x1e0201200705180a0e28020a030807110405150d030e120d0903030909050f0a0518030d0e0c120705010f02010204081006030605060d1509020d0213060305120328020903011a0109 77
    0x3007244417154950400d94403101c0d00702002121060203c155650203403414027558000ca07003d0354400340c03840d2191801503040b031507500403400c06000442e20040034a503030b4a006c502406502c18bc0b40669811138485c4129820107911103640c90009080c2c84040201d40012111512650b40c0341e0708500b0003400c51016035210b81c0040741480e0421401c3c5445209040d00805800703408a07554a1f4600103d092480c40018140144404283c10350030300711035040003001d841480c01340c400e9496500203218240904010b4010b00350310140d03003004254800c0182103000c4140b44001802e103601c501e0141d00740002c01c80341409040e1261014000d01245102d42c3e0b80101045480340205a1039585d03981800104103011056540d640100c2800e6444500702341c01503d81c0107000c440c04118030451b0f41c0041080d40000d031654852440702c0541c517020f41040340e005896000d00c8601d048202004c0f03500c0c40c203102c0c2c0c148048a40038031031000310b40c40c24010000e0080703406001c002e940c907401c000144410342960201e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 473917257 1250 473916007 473916013
    0x9100c1e0f080109090c14120111181206130c03170a030c05181e0402030421020d020a1b0302130c0e03070b07110a0b12041e0201200705180a0e 63
    0x30740006d80c0c450286003c0700c4401d00e004141c04600c1001440c003c4046000202c0c550038101e41207101c40b0b41e81c00414031034041158404100001c48140407025910000505113980420042810700300240c0f905035440b40f060740030074017040e22a52600e804488001c020b1518400110b100c0010b01e404d4001c410400f50b6038030b4030fa0704002540020442c140f50405085003e0ba01c216840b080c1e1031968050f40d064042e010b0002c8d5541e0401e841e01014980751050340d48600c00c1d49400050340c1d2403001c601e40318049030a40c0149900c82e0207444550340c0340b03120346042ca5100e0103901c0000050706c41658100402c000d071b41000460052100014050761030070340702c081c400d4024101c144413100500301610300c660307005003604020b0110000840c0b00c003042d503000001100b9010980013032040c034022903244281c1c030a09000392241b040101001d580860080e00070b02082c1c10b5030310010a840b050b81c000d0030711203141044548183d52200810100c40f0399100e440c540f40c007054200a103080440c0204614283c3c82e20003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 473918507 1250 473917257 473917271
    0x50a142d030a1a0906090702010f0e0a0c05010311030f060d0c0933030f11090103050a110103060311041e0e15090a020108010303140f0a030209040b040509100c1e0f080109 75
    0x1440d4903900074210346c45212400042203c5078800d6001c87c0c142604120100b040c0e10900c810b10345e031680d030301c0803c0343c40103400341c40801d89510038081c1800403001c8903415801c0d6250b030f000b0200040d80081034160040d9144044002003940d0f05002d6005080d54180040c0c002002401140005514003140c000104040780700e504451038144200c1c201d0b50043d00c0c1c2c40c1d090751549030608000b01c4043c00c0550241c001c1c0e00100071301002189082000d8818402501141d000e44015400c0e60004e11014000a0b4a60241021410213030008803140341168040c8208162605541003150944407010b000c50348400b60104161524000322508405030000625103100d656000a021110500004041011903000126460840c0041e902ca090240b0865911041c0a200080003900201d1341a8031403130a03c00319240e541080d11505004900c201c000d042980007811800f8040d0140040403420070015502030380c82e900e0100070301c001010241e5505070103c40c0c4803400400c07803441a044084413901e4400707 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 473919757 1250 473918507 473918509
    0x907090918030203030604090203010608010c0801180b060306060a12060308041403031207052101030f0c0603090507140a03021504050102070b0a0906030b0f03030a02010509010c050a142d030a1a 85
    0x13040c0d981c0000b0448011458511510110b80900000d92000d5855803c00d60020355507a080200da0703059a80324060803900c0014142114281e4503403a010980041c020000305026007403c0004080049032401d20314106c100030134900741202d0059009461541003c5014400100100360100842c082140103600386040c0c400e03212030b01c15024100790305103c0c0004421043c0c0400300400e985190a00036806032660303490910101042c200c940484100d01c07013201c00703e0003034001d00c50b42a2858014000340045402e0401f0315a800c00c0ca10913503070740001f84100c0040180d03200d0501c100c0750b4454160351034856152000180c6040e600da04610f52034401444420b5a0944c01141c020495049240105984c80f40ba00416440317020425003507054000010032914245c0c0540200d40100c80400082042c00d00c0d2000484090003807810300c2c4001400040c1300203042a401015000009607050b50410020180395443c0e4a40001c0302130001c040000710070009402c00c0780c07180c0f1030700401070300031403441b104608 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 473920863 1106 473919757 473919763
    0x20d050309090a330b220f051806060d02070302010504020f1002031209010e010212010603050705041802070f020306090c0f03120f0a020c09070909180302 68
    0x808101c100f1075a01c108415544ca40c0303656103601540c0c070100c50903a98200c41249a030f48616201003440c2c41c14400600810581d4101001c5480322600040d440980d150701c03c50f0940701c048000c001907201c02c2d8a9a00c014500112400c5999603480024a540100340402c0003680c404210841050340540c030080c0114001c0750500e968039000e5040200c00011000003c2c0140c1050081c180740c12041c0308041e400c514040004900c1c4401034520311b089800007815174400c0000d80c00100940c40e003520990f80c000b038152500c90310f001d01b040755503000140e90529944e481750b4001902014002100c04008202e5401000e8940702e00f03001503220743e81c43d4004c103241e125248080322070840f40344c00548805480c510400341c074144140e5126940841d000320324000d0a601905002280691f03d02e03950138031411540d120f002d038217410084420100c0302d80444d02c03500c5080f0340082d02d000c03c0d000 = true := by decide +kernel

theorem cover : BRFrame.Cov 473741007 473920863 := by
  have h0 := BRFrame.cov_init 473741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 473741007 ≤ n) (h2 : n < 473920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
