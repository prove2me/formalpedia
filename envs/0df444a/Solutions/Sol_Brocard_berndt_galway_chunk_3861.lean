-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3861
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:53:33.322474+00:00
-- url     : https://prove2.me/submissions/d28e832e-d3e3-41c3-b977-5beb7771cd8a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 694244604 ≤ n < 694424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 694245854 1250 694244604 694244641
    0xa020c0c030c100c021f1121070204020304390531150303120c0e09160c120804050d02030301080d030e0102090315010f050f0f010809160801140a0203 66
    0x644148140713810b00c0040c1d1a00c440b001c604041ca509050f040c030081d40c02209a021100b9840c003103031008880a02021481c01d50000040000103040c403685d801400e190b000b55810034072072481c0300300403a140750102d280244010303110101c0440d119a402c9410152a0f4100d01408055030740d06004a41c2c418208001c59150120801084001c1d0b280c0a00001950009085a003090404030110b992400e00070700080002800000b224504a4010708103409070351702d211030b1080684842043d50307036000c202ca03525100da01c0d102e0500242000c00800164001c3e00fa10804440f030b2034105243c01c04d410818071f03102168203608250340c000c0005200711000001d810113105040e24010030001150200c0c540603004448840c1d400d449180b45000f005014844628141c600140203008030598550070400011603914040d50040e0403201162040c5d4483c0361000d80c031102d00f404032030403480c0100111001e001d0580c407002d80351750f4842040a0000300442c500390041e0140e03d0950450801010094603170b070b40c04 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 694247104 1250 694245854 694245857
    0x60c060606070c0320100e01020703030f0905060f1308061915080307060914030a05220f08070303030f021213020f041e050106050705060a020702010905090a020c0c030c10 75
    0x22a02d6001c100c1058002d00103154021142003200d48901090400c3c402c04100e810300c20f41c0903d580c0c0c0d600ca44250b0030300458103070507801811118a19103040d00d0741b8002505100400218030700100d155198070b27009018508203203030703480da45651000c035240c006200d6070801105d5402c100c051143d140303401440e420914155001c001760100c0710320b62441d4040780550101100c0d01002c1484018407074140d02c985881c0d4040c2c2e012101146000120b19106d118224192020910500840200c405001c42c0804044503080e0441c02042e01e072011065103c0d41c50b80880b00e2580001d10038010180e050150380b80344809404194142413541a429480740c0c0004c0c802c015404100314854190b41d540b00d9809620203016100300101460361640003400e1400e116604c00c468141400010b91600c614215828030390800040d003c0307a100c10150101030743c4480426410000000700c003185640c3c429420307a0141c04181801640d990f0804e54007801c00306010081ea10076008040c2107182a00c0784840b5060b540d545 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 694248354 1250 694247104 694247107
    0xf070302180a0f06150806090c070b220507090c090f030b150909010e010b030d0c081324020607090e0106033201030203100c020c220f051005060c060606 67
    0x451840200405401640f84425030814100140250302d2042d00503082d60a0383c3d400756a45c0c1e40c0703c140204c200003076136011a80c800800c12407000c99003204e130560704090390250480c00802d013204a0480e002c0d21701c5c010343d85500003480c100b21900700c0b071003004e40b100c046d0704281c03102c05e2400c940174007881c5951201502883c16a400107034603064001c454416103500501407502c9046c02d6000034000d011600490180e5032030a100d06a287c6400101c01114148a03694030810b6000381e55404281c6c1c00880d600c0100c0d59a12070045002030380e40070180010101c040321814815901040207207004009041c05003030040c6160103003c14085000c600b410360702213090220741201012010082106100019215010342d0b410040f141c01c3c055a170503040720b0084040740d07581c103583c41c500c0040701c40e01c00101015a0000754019001c3c01c11601e445103a000c0003003d1811240206160b41c240d41c92100c4d04841290b44800b0401d6034030f440592003000d05402e481090621440400e140d41d81c84018080d10b114850 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 694249604 1250 694248354 694248361
    0x270902070237050301050105090601030b0120010507120b0a0e15090114011709060a0b0105091201060602010c0c020612330102010c030c0f1101020c0106170f07030218 73
    0x10740c509894000d403078040441010b4200c508401d001c004100000024a0118070700003d0103103014012141a83c000420f001c0d0161160001540180102041c5070306000f03001901c2c88600d8010950740e00382ca00c490001080d5440d06a400600c2c0c0c10291b40500b207003520744040c48242d502d0710705202043c0c600450007a080c0340c481c21148048034000c030180700c0d030201c2d01500125900700b010000c1c40c7c0e140b1080c2c80306401c1d28000380c0c3c000b4210380c0032940d10349140d204030000750205815400c40c1c01602c606062003450007000a0208045880014060846030b4440c20104840382d17091090240314003292401c074500c1c000660000380d05204903ca0121030070b45003c08203da920900c06004408502984210f805c0d006204112482c240302e088a54095440e0281500c08540030380521454200300e5900c04024817103d070002e580d41410301d00b08601c035650912003151095400d00c980c0c07001c0c0c850a400c0b1001010042c4285203003d40c201190600d41e00a1a001c10060702c60303135400900045c2c0c2d80c1d4417400340d58 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 694250854 1250 694249604 694249609
    0xb180304080a0609021c151a040207051c05090105121503010603050d0f050405090402060d113108030a1b170304020f04050403140706020d05010b03072709020702 71
    0x5941c0007160603028010801c02040442e6005006040c0b00b550b091400e0508a9031885001140103000b404081d50343c444140110703c036038020311048a0103a200044800b80402080403030f006440215075a9110644c80e00a4054108000415196525016260000b0b02000801d0340c003d41c0840080c02d2102c1010610743c0945886200780c8000150003004003581d81e0900580da100200126004a40100362001d10a80315070112001d8400c043e06810154980381c3c24820035a1040104203246a6a40310b07940e0f02002103802004000d40410030f45020315065089100035501c240301d82e107100300002004000503140401a02c0d01c8029070305182081c0342000c100310b003110180b084000c0c44820340d40414a029842880a5401360b030094bd11191034180c802d090000b01c900503113020340400c0410310f0045025000da130080c0042071080b24050304100c0c14000e954280c0e0000c0e089050f00400100401501d82e038407155405416126804c7c99058540680207008115680e00a00b201d09800060520564 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 694252104 1250 694250854 694250857
    0x22206080607030633050a050909012c06090106030c110307081905130e180712050c0105031b130b2b02040806062106010b030718030b1803 61
    0x101004419540c0c1c1e4503081500030010149030141941c00c0d0041702d0600d0000d1000b075111520200a01110304041d1781031355099540340c2050060303804103c01002801070589072418224000c241080200c2d8040001505680010040a410580c1131116004100b0380b80d590030750103811510141400a02d00350781940442d040c0f0800001d1180701c0c40000b5050007040341040081007803840d800d064006515802c074080702d05116821101a103100c000d0000d200450390070800c00c1d00024410040890f440c50446980e003455020740c8000b2880c0280003054040c00014040f2a00544c42440d08a18601c0d1600184809030303180380d005182c80801241700080300d040b4002c14005003407031001c0c19480b04503400078510209400c4106110f0004130000544107082d060081d6801d603000403016004550f112014012284445c602c040c0c13400721043c7e0520070704042484214081d0219071407240d524a000007025050101507050300d015811040720410100382040b141c6900300c55010120a00305c0320480441d81365 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 694253354 1250 694252104 694252109
    0x2040c0512090a030305070e22020405030f07080105070302040f03060908091e030d1409090a0b060f0409060b040f0608130212160b090604060f020a060c0c060f09022206 74
    0x1001c0c50344041c0400102c000800310700e414402d507010b2050b9a00d41c102100c2c2c0740390358500b19402850900c00e200d020600b040d20140244021074005060030381d188002450507010711400400c03a00180001e01008d103084c01203560100307050506524091802c40d80c0c01d03442c2828803000d01001d40e1030200707904001c064001c94041c3e4400801c0500d0744042415452100060b5110461007446800e1656140302c1c05900048a00e9021043d0075003004d140f502803050845004141c0c0d100183d8480320701032141e803603034040c0480d100c0d403052154441d81481410310480f0300e0790f0001584014180020031080f154514664107807086407a00c102241c42e0205038101c000c1d0300507002580910284030300100600c000844031441d0002c466028045682d81c02c2d20086403041b080c0164020000704400e2207000c2c02541c4403140603a03184116041d61000c1d07100c3e44c04039a54009d030310000a141124101c240314043c018165905000c41e0f08000403643c0b030b4005a00d0a00340c0c401c08280d4051255a061940040e5012200 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 694254604 1250 694253354 694253377
    0x40501050a0923031009050d23030403020c131b2007090506130e15190f020d060503012d061206020705160b030f04140d0c050c030309060702040c05 65
    0x441c0409910803c84038441041454024440d0590761104490a4010000d100b5080070117409072880b081c404a0f1030a4000000044060422034203045020384000290302c1030b4081e502400c007040d2240d0030000f04d400d485002498003820303c1400e58142a140040d40f42902c0c0a0810700c42100ba551415407078081481c0e100a000e00a2030000188001281c000c03030321441d0111a40c04003c02d452900008036038001ca0344594561014040709a0a652602c403d900108441259044500c1031513148044d10044281c60507610b4005c035061611244500443d0094001200240840c400100c200d407502a440c0c6583c010000d09000701d0a08030300da075403007a00580750b40114184401c1d05c600304500a075005a1003204c482c4580700b103108401203501c9204060b9111160340500d951034180c40300e1010b8602030700980d2189250102d4400100c800c21502200c8082c60f00e900a260125003403032814009100c95060080d00104040c0711241e462004030303007026038100d800003003d00e0110011685405981d24441 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 694255854 1250 694254604 694254629
    0xc19030213081c090504180206090315070e010f08012103111203060a05030105100b0d0b10120509010216140304080d17151e0d08030705041404090305040501050a09 72
    0x80e2842c595100c08140e00c40d5904e5100b241542d0f8002c1c13000b192100b500a809260005030540014030f010401401d0407000101120395400100c181e2120b55882501c0900115a10079980400f950b00040e444410508508020784a0340c54008003103c0030860142c05401305070100c015108160081c4c080e4a807100860045440d1030b442850307001010790090701c05034413480d04082c001611f46414060342d4800d408aa37010001680743c8555101d2030707001031075202c1d00c0755101c03404140c2584880c03039500c09000e02c07036840d481e80c0ca060101e500102c400c054036104150b40100030707045800f01020a9911320307990101840410410282c4840e096010319009900240140c1c603184d0b6072268842124181c081440030a40d00d16140c2c40340c400c09105a200e00140c02c0702c091150000c0c440f4445541c03c011100c0907085c008040800c1d9510307081d80e80200c4142010440c0890184807860048c103104406c608107031410004110140c40c042c12a0045100e107504003e800079500907000d2090200718014a4040300f2807 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 694257104 1250 694255854 694255873
    0x81609052a0a080a0204290405060d0b0111011a4e010c090e062202030901060e01030510051f030302070303030516082710090501050c1903021308 64
    0x240415440b040500c0c1c001080c202c08900224524403c54088412220201040001c06d00103078000310765072030404041940502c000141511880c1c0100306400e0f40d002c002541e0200b03c8000b4108910900d44804241c1c5811480d103010f1407501050101c9420032503202003062001170110304040c0e034002e003000c0403010700c20401c42200c10700d80100d40946040850800e244908070750389401c07100d6071400b4200050010b6410094920407008940d004500a030002c0120f600c2c00c0c0c4807941d107084519042d51119030000801442120a12a2034003400251034011b4965145444059a4200101c004500701d96079801149451031818042104d020103c140030b0300a03552814013130b49865140c84250042414800001c12100c00c4840400b1581c1c0d580e110400b040d1a02c0b40c0115040019541e501c49140c2042d10300d81012000304100041d02e0308001d40031401412924055027592030181c041c079200c21040c400c03130501c03c40e66041000c0b425014680180c45e120450046101d83c8100d61101100340035000a1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 694258354 1250 694257104 694257181
    0x1503050607020d0c0507271a01090f06170c0714210306061803010b0a030b09100c05250b040f1b080a0b0a0b04020408100608160905 58
    0x406101e401e880c0c0a850542005007030581d58440504070040164010f684144400c000c2a4410090401850b4107800c4211255020008850400c1c200c3c031410000c4480180c95980d011035070502030550303640400d80d0340c3d00e03008016000c05400b1080b00c841595850024802c0703124101614885a00715000d07602100c00e00003155110550401a070065a1035200e248171040b1188040324064100904110303d440d0404040010038000c0d4441c00382d041d52603507803040703096885031072013030107035006400c011003038181200d21b1031900780d0301001012090b040404192510760000b040e0b50700074201c0d400380804071202080c10400c0d109020360041146043c80144001d000c14244102d48440c46601c486900c0110401c9110b01c28420303100320b411561164803800300044041400c1c64000b10b00c40e5021881c00b003c10000380a03070304582c0003108141d000c42404a001d00d202d006450080c00f45001801244103620140c09000105014401c0315a8684001c51008080b0003500c03051140c40c0000e20032006d110391036 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 694259604 1250 694258354 694258363
    0x60a0801080d081b030925060e0a0f030b10081c020105070216090e01140411130b061602060c0a0506010f0b03010b031b04090c03020306090a090c0b030604150305 71
    0x14088107225081071120320b00d000308001400743c1040c04c160085400229601e416991000301500c12900403075001c00c44c00d081441c92103403050b007001e18050a003800c00b070000b441f20140c0e03d00244201052042041041424202d8500f625041103200c5030507910101e07840c02e04680359204802501c901800204103000f41c480b00203507000194020711282c1c85a0f9006c0740da540000c64098800c08010b03400308020001e030391281105144d40400418180e400d034940e0707800e400003120305540304c0b403109610103918a0a02616180010030810420071488104080b0721301c0d0084000d0560061110907101c415540c0341d00550b50032140c01001c550180b40c2130b02d01103448581c00c0c41640030003440e000010801008001c00d0301c0c10703203603901c0c070f12425030f51501c0c14044141c4103028510001041000042420b100c10300650100000c42e40340035a80741442001d110034603400406040502c3d20f00f016900000380180c041d4021a14a4000301c1d4a0303031122000200100404c2441441a0a0b50f200000c2003280104 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 694260854 1250 694259604 694259609
    0xb09150c030a03390e04090b0702060705190c0812151c08190e0a2c071d010e12010504260304062a02011b030c02030720060a0801 57
    0xc0d010f0114002da200b13148084000c4110415000141040d04050510551512640d0001900d807a10007005694003160444401207000c1d0340fa1500e00c000c02c01c43c15010000d480d00801d06140c254542055450b0110001c0081070941003040038180e060024005014113131a0302c00b07441c01c0c0003221810030208201c10b02c4e042000540c003130240720314445110100d440720034419a402c11080344c600004000c2400003182880c2c0c2007414030910032000c81c0183ca54008500c003800e1103410903400303948110f1001e5038400c0040c600c0c4000c135901e0020400141d83c000341c1c842040c4039010b4558074031000c0400680b107032010100d441e81c0025144d0b000900b00c410541120f0b01450049150242c401d12030f810701550108031000803e00441c0410210780002c00c182d021108841e80b540080c1e80c10350382200c0107002c03480c80c0400400141c0d10340c0d4040e0030380300d01080c01ca482c0e0720090404020800842c04003035101e001e11540601094490305100c90100111149000194001400c840d564025824080c080c0e80d402e0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 694262104 1250 694260854 694260857
    0x30b070f0207090513021216050904061b020a03080a0605060409022107030c0e040c0504030803090a120e040c08040b07030b0f031606230f160f060c17010b040b09150c030a 75
    0x50543c01f282c00c00070403840e000366135407945001118105404c0c4004850094411183c19a4441d0411601484c1d60040c0a0801103607020305078525260400504024019006034540c030f2400e0420406a6038203001c50301110585400941c032185103c14540f40a91841e0210305d503103040408100d2015803540c40410320a00700d0f1580fa0365221284284811985c03148503c001040341040240046940b2001a541c0030040c0c104484800525584a0810f0600c030700382c2901003080c80f0a42c0c2d40919090003201002440f52820300d00c41c3c030b400d890341d031010b05015100500741680c412504100343c175001d070343c9071284401a00300c070300056a05c00040a16015841594005010607009540040c1c201901d045031030a40d440184c20a0824102d509481d406404108032003e5076100302000544803549911116015050005911900803405001c2c030f0460b2210140d40c050000041c40403040110542d02924511100640c48055010208002549020450034010000718401d000600300000500340740005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 694263354 1250 694262104 694262119
    0x30506120732210a300305040b15030a0c0f060810080d0807090e1302030606120a0f11030a1203060902120a151203050c0d020304030b070f020709051302 67
    0x4125107028940486101d07070303900641e2100050150303122854500f10b5403103120141c442d03200f6140e8440c01d03054000c101d21501c00d440e1041c8405181454624040d00600500301409103207090703607600003510300c0140a56045051124401d043d03860070050309007110f9015460b044210b841c1e225010b60301140d0f205510006e1300e01c00c00201c4010840000c1812911040024504500e07120782c10303584081c005003800d040284040d800110fa010044031580944002212503d59007800d0040c1402c00b80000d082600440492442802c0043c0005802e100d10743c00c0b010540759411546043c8280f04e82d00c00c0741d55898411003201a05125129205001001c0c054804111442d5140c0c0800103030300407034080da11803948800010310724401d26000803210308040b2882180454a90000c3d104150104400f0360002e10b022555002d00c4000300101c00c0b0810060009500b020b02d56a1207205062005060408000c5420304002506000f0400e50380035180c0e200f428896031500c40d110b968071032000c01050384610f00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 694264604 1250 694263354 694263419
    0x40213090314030403030f0906021809101802090603040b0708161e0c05070b0a09050a03240b06040e1510050301061110020a0302030714040b0306010305061207 70
    0x15206400304941d054440c034006030b0071099640000d4000400507801e050b16400c1c2c401c8000035620440301c829204050050322202480032004020280800041c012882c10086c08a06030f6460101d50031103001e0044405800203803540131010380100244d00c2d070011000b00c10f200401881c00082d500c50015590754441983d14000703c280c440c0f401504000105005842c540c00c00c4094100d0482c2c407600c0ca0030089018021640c91501e0031401d075111016401d004101b9101c13107903000d400080244070071103a910200b81140c03500e800c24011511107541e034140301841d00c2031030344058020700c0319898001d1402d44c50f01c1d914035402d8690741045a00c1100300c0d04620415181d8a41602180c858180c25a52103007943c0c01c000c011303030384040980200b4040d0301c107003992403404200c1800101001c45030381da0056281c0c101158007511404814801251000c0b09000901203101c0e088240d991200f424a40400c05864110100c0c82101d810407c010990140b5000890040c005503150035011160070109001c100d07 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 694265854 1250 694264604 694264639
    0xf070204090b06030610150503040201180f06021002070c051c141e0d020705010e060f0403050d0e0a1206020f04030f03091806050f060a14042408090d120b0a08060402 73
    0x2c0c0c07901a0300c2818254028601f8100d200e4006142d1051040c1000b062121402201c250000c4907a071184502040b6154240a0107505103c1d841d0003180c0c9602c150705109403955440034061071030054600910100c05110410300390002a05106a0403001e5015244122070b2501d0b150a0440b0a4030b01e20500d07070b44030f04041680040c00404144041c0e000c0c10380c1500300001110303841801c1034802d0340104140615104804540d0061000b103200754000c1101c01d5440c64094078426410703c1070742c41207082d40000c000c520004c0c950400b00d075a0050300169212123604000c0c81d5030042c0c0d08050001d10420401c0d40800d90401025425a0b1074072580000b017902c0794013004107907a0b1f94020f41c4e4000c80c03812030307910071414000041e1203614440e0501000c0c07a50b4100601c20140c10a5201d24205c0e900824201800b00030028808001c00c03452520a03201d01d44040c125942c0c2e000100c100c030401440303034100181a80540d002d06134120005125090469581201907039800d000d50701607100d1451440484041c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 694267104 1250 694265854 694265881
    0xc0c060405090f0c04051309050c030d080c0a021f140a0b06270402160309090510051e03010509030901030e030703080402010f030e1f20030c0f070204090b060306 71
    0x4407801400c1c400b03030395584843c0310610403003d00703141490b4005100c04600c660381c12032120004403e81d0800507444480c1c1c00d005262008100507a400387c2c1048040c003031080d034000c4c0e04507480503c030f41d10107580c1c40303010108038500020080b0440c2004840802070001d10841e402c0340604003060008400f203070b02c0e04c142c20400c844000144681c00301003001102005002407034403002404040400191844015000c5005c0e0b90100e442d088440c542c15442c8c1c4205600034250700e0142640a41c00c000515000c1441010a910b90141c0b510540d400d244000c0c100c880300d075005060500250082c0f0490806411040c1c0d60341162008038080b03420000d20440781e00340002510300141d015625000306880e10b80040d62201d12400d0804100341d20b90f050080314003820030038803400310b202e00000c4070111240440802240e00d140c1c00b04100b982a08014001c04225005a80c1c001c4070b21440c03166a054612104040da204121009401c1030070035111500f4024003541d014071425040d8107988417036030380744554a41c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 694268354 1250 694267104 694267109
    0xa030809061b0405010e040f0501260114060f060705070608011505090901150c0803040804061101020a0806210f100b090408030408070212012412030c0b091c050c0c0604 74
    0x2c940050004012a42c0f10300b51040320b851000d000001c0c58105211440284c5100340c12602a000d0b05203510041c111a0481d032002c2d042c4c8420080240c04100e5422901200703000e091584100354641005269076149000c039107801d6031100403034801c0b55070346c074001d8401c101c00d02c10f074128811806110340103580201c08940c04100b00038503103941b0381c2c20866850a0301e05866114420040910440000142600001d50245000310318950322a032a0840040c504464141804016401400302c440c4031500054075070307002441120082403024504010081c00e042e48131132200c80b031043c9008171080001c080b442c1d0b40c25100c0c1200c103015000058090040400702510002c2245404000250100b05c0d01c60291400e107200520205141d000e0844140c00d5907103019030a0f6042c104130040f140d86015803881c050080441c850140c020703450541340030f0003406100601400311908507000400d8264144502c0200116100f20303201181030b1414010203940111036008498483c9640c0c4010300d10341502035a08 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 694269604 1250 694268354 694268401
    0x40c030506010f1a31030b0a1407031a0a030c051f0807030e030405060414210d0e03100518060901060b22031211060c0408060f1003050a03080906 64
    0x81008108649a104d9071182603048003000300b044010074401c1400d5989030450040105072515907046050a01c0da015000c2c00200016103003540341c00c0041403100e215980f08800d402c0c0080d569003a510542c0c3e86040c51150254409540c250220410482d90701d500700b51202502e40d4010302030034000c02d1542c0c40200c8180c101049402e03002a0900f03110b9048070a1039a00f01080c0c0341060f60700c6c0d0108070650040d40048600780f0b0a21002c040c90f04203010341da15a0303100941d451200c01010f00c001e0351140c0a01c008002002081e4040d08619241040741c0741f51007910b590100007610340a464a0f0b45200c608035a070126018010100740d441e4014041c52041c0c0d5000c4101602d401e03000002d030003002c81035210407d0b280c0c104a40001c0859125400340da50310f5040c1c1c45103442540b96078255070400d0802010142c0302c032000c0c441440b207113000160f1541d125081440280d1a52165404856000c68070740c0300400c5ca11800e00c43c84109544000d80354090403103c000c589150b11894040c030300c1402c0c40740d031522 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 694270854 1250 694269604 694269629
    0x917070b060d320a060605091b040510180b19021c201b0a08011415120703080711010e011e051e22060c151103040c030506010f 56
    0x1000d1003d810032200202100e06401c000f00080a81d604d0404140020558005130748a6080106091000c4200e510030380701010000307000080349008a00c0d00550041a01450f90f91840c0400345004001d00075602e40021146a010b543d1386030b4213119030744125806c4440203594040a090b0900018034510620f044d6034014969810703904045407000c0c01d900760000905030003641c08400c1c6000340200780750441c880120f00c0403110354005001008140368841142c81c3e03d840c01c050b00e500004034485030042c4041400e0030403e0f05550008002c0310040d15100e400f40135601f400003c11104100820f0040d03c03580780c0050301c07103010006680e002d41c40100b050205004201409100c5101010f002e0000382d00e0a01c0b42c102035014200c20840401010507140060002a00052042d5000d100c80100608540702c640d500f800e04000411500300b080300104402001e01d5038003840401c43c0c0010201740030090480e6141e24041c20a000014a0f0b4482920640120400451303050001d100380400d4036400c0c030b10030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 694272104 1250 694270854 694270883
    0x40c1103120406020d021315020a0b010509060a271a01050702040b040e1506130605060d09030c0f0b0406050604111602030a050a0b010e0112020a0302040207060917070b060d 76
    0x21009898010b0040341c511340c0c00c01c84501d0401407480601210308100205454543c1000302d442e01100d8180c00302025136008400880005440d004641d041d00d10941c2d007035003030703071941008203080f802941c01c006c0c590103000704d20040c909030029000004006208060080340c1d0050940c040d44d1003c0203051f4005001084080d025082c190810b1004000c090800504c00019905507410172031a402100d242100010520075103182120b0400e5401d4206c010400550f8a801e000810a105005411080a46612020b018140500480044240c004140407404c20040c982145044070031034003100c01c240b810003c80d010742040d00c12911020050070480e49812050b403c0c0c0c401d1079a9648040f83d040c807881c00142e00082c1c0510844410b00e1044d404100e507541032245400d141e42058105103841341d245134006015a540380304890440750140c1e401a95000f850074200e0141448010250040c60141ca540545801070310003028802d001b6801204d131500c52404218040400002c080e05031600080c86 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 694273354 1250 694272104 694272127
    0x712050c1213150c030b09061020011b050702030d0903050705010e0307091d2418210d0b0103060b030c03130b0a0501150e0d03140904060311040c1103 66
    0x34010101e0241520010184400702c0c44000d0f101d0343d0884e01d000a40b144585000da003440e040140d0090b42c1110041048004013100401a0502018001711008075015030201140b00791710010780c640b0304028240000005075405442540100812402441441d0b40450200c1c81031501c0c4090b03a5100003d440503500e400011215008024101941402150400200ca51443c4070303224849603070024554030250340c00c0015003001e140c60410b21043d0030031601030f101c08840d985465884070316140110002603040040c80d01c0c102103000192441c2c9240c0400900c008182400340c10b1024210005109100c0030320011415107107140300305a0b0344003003400403800742070048005d5548010403e002e5040d4004d151201e4084540507556a01032598032001442102e000641010154040e41041200d9540b242c02085441400010240070803d4502000002c07092110846051581c010014070400740c4a0803c1d181c90fa024024240c455460261324080d0305016142018510301204081c50402180d081d1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 694274604 1250 694273354 694273381
    0x41403071515080f280804090c030b040e1c090e01051c020306010b0409050a06081b01110706180608041703060310050a020318030315010e13050712050c12 68
    0x85a80c850b401c5040007089580040105220701d0b10400010507401d44032041840003019940740d021000110507034402c01007503501c000c443c05c41d10584000905130010f40d5045006080c040c074200d038014100158540641c2001a400e101e9607100c0e60407201d040c16149040e141040540b0844000756480c600412540c40c10349410b032052001c0d00c03000340e900d0406600083c10007509030019a41c00c0d1000c9000d204982d036511a02d0340c06289220b040000178107149420b5030394502d4402460035540c5003410020541d00c50312507809207103100d000b200c02ca540c0750907019112a1000c0c02040342d501041c1000030304280300c0d030500360060340c00a001034a10501210070106039400106096018814010074402c1c141e017510416100380c200010047e12802e00c0d0280700c2e00c3340702000c3d8509050744184244800e581c00c401c070101c2c2400003428610650071040b00456a1012a101c40001c040c0c0380408203e0000d0700004050100c12101c1420000d50f030310300c80155428024070305040740c00000c4200040c50804500e2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 694275854 1250 694274604 694274621
    0x140f0706230a050c071514090d08030a021c110319060803040b192c01090810050105150a020d0809010e1e100b0306040b060607050a0b0414030715 64
    0x1986039400050910754091641c058112000000e00025034419505028810140a40742c41100c2001340002e00100802d04030384400c0c020300c46980002c1c403401660302c2c07038000e4150550000040c0d44901c0d01481074402500900c040545508000a03002c1145880d03100b43c108140c4204245800c40c3c43c0c681446d44600500c1e0304034000266261b2001c03c407000c0c00c201030300c010b0407440c48499a2740301c45010050100e080103c00e40600807140c0c56800d034440c426140381140e4a07000003d0405400d07400040f20151075640c45251240a00e900c803448200141c0c0119060765020307103401c10b13203a8040035a10f160307121b0340d0840300050f0090758600100a00c1003000340c1c0c010030303048008180303400c00142c0c10341041510300c00e080990190912400c1101400e01015031041c070a02010410007440c00c1c086910f5050050000300507143c4800054195680c0c1c1c0207480e421500902103c00745090345c504800b031107205860985100c1082c40080500c40e100200f2525903540c441d2034003002c191841c00800c094060007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 694277104 1250 694275854 694275887
    0xa09020a050c0601030f020109080c0d060f0f0f06090501122a1512050c13140102070f170c100f1d12070e0705040e0c0307170103050307140f0706 64
    0x100500b504103401086958040c50007614168804242c9200141c11249150b01c10041600f0250f003031013641e03841c600061006500a100070809500200f200380051047c49a01c4c400c0d5450808660070048940d0320040c16039020b50b004102a90b220f03204001c0f00320001c00003c00310002103021108490981c0c050712100300560f50080806626485144250070403400148009002031207a121009014082e00d034010721303803440c001d14155002000d60000d0700c03240910882010703800c00030100ca91003000110014140e842100180740e40f0741d0421080d2210b030b100d13600c080f8422032054002030b103405540d000c40c4455944801003542d0301d800d4280c1e6000b84000300c40084a00c01c5c1d541d00100e4403101d0203001c0400d002c60140c01c0d96820941541c4000602500500c1040005d200030b0101d5400d0802ca03540021740e11110f00d449030f940c0181168900a10f50104440b400500000800c03c08008080c2035054441c12200596045003a000e0340d40d9400f03003a191070154041d08081180c10301500c0d4200360700f0680b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 694278354 1250 694277104 694277107
    0x1409040f080d051302011805010e040e030d0509030d060504020909011202130c111560090c040612090b181203071d010c1502091206060a09020a05 64
    0x41481c1804582c003c031810700d01244c800c00e400b4115a4081101e42d29000710700f040007105400d02c400280b24000b6030052038001e40d5500f1181d01044020400c0d100d10b45110394080c006803500f9070f907403a2250800e40d540070445040a0740400d46240c01d00a03540003050190604c0c0c80340c1e1a00145030003a441c403010982c0c00c40c6a10302520200758207402403003922072442e00e41000c42c8040c4150070340742c0301242d82030450324000030082c01840880c141400405450f00d88000c490368602c1030344e00f0303550080a41040119400c1da490700d1080140b40b1a282000091501c51210400715081840311116085440d0260400c00300170a1001d87e0240041107a0030b00c41910004d2030b140280d40d070081001003a1742a08249907035056001d60a6030402100140941e00172038a0f0035400c0c80400600150711402d080b880c1e09540142c920042c1e407003500b030a0981038203c00146200688080084025401496903c0c02035144a102c0b15007450000b640c6402407030050b04a00940c0c1c9420300840081d04000520802c0220 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 694279604 1250 694278354 694278367
    0x70b041202010e1f0905130501031223031e0604091110020c060c062203090e0402120d030e0106050d021804020607020a03140c0a032415060c0204061409040f08 70
    0x1203004e0050854281da15102c1c003071030402c01000a452841880c0c602d226040000500c00215408208124105d80d414111100038800403501260000d2101d0b0b00f0429074003104112400701002c60000034024108011030594031802c0910040d80d4601d0000341080042080700c0001e4100401c1c500a6480988180c0703485008060014402d54049122042158401000d22410340c600810a50310390140503040c0c55010740c941e03009441000144110803000c900e9000082c15502c0305080f07401c08945843c1925082001944040c4c010042c03c80f00c80000e42c6040804a91070030013a0007034070405d0b001004800700d62008500004454402401280c21600901031000140c4a0702c80c80300c0030b548640208010544074842c107901d8102842150341c030403203001304200081020341c04052903244c0e00c10f82c1d0741d80f4000f60003a010701408400f8440c02c02d0094010380050625804504800c00901c21942402005e5079102d40903440074420300040d40c0800001c0100c0c001400303203004005900c1c411110b0030700704003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 694280854 1250 694279604 694279639
    0x21f030f020a030e010b0109051c030207120605040c06022a040b040905060114040612020906030c03030a0e0f06180603070c12031a090108071a04030b011403070b041202010e 76
    0x308041d02c0d030800303c1d0715941c48000010b002c3c094030305240310a2900d2401c803031500000901040402e041090143e4260b569a810b00d8030900c00322000c0c040c030309100c40b80c80f02036142c298028207046a042c1c504042c5580003041040c8081007122203aa0728414034130040103501100403d6507070508000b50f020365581c0c200c00050700c440c0205d4544034003030000781c0f00540c5085001c0c04808041010341e0720880c0b070072100f4807000340d0001c0140500354065900c1440b95884101291410305140d90840e40742c440854807106095012000d14070340c1006441c0603060b00c03888000c1c042c00c5e000e081080340214604800d20360041c01d00401841e4025854a4605880314407a203030b10f05400e005062440002c0e40b62003000e9a5810441c00000005e201a40c042a1540c508101c50340c5648080c0500074070644846a488400b011640c140d8000d15041200060f407941d440c440c5038040300c4031403090341c06402155800120744a40d1001e0320704555101500342c07d417000303a900440d40e1100c540d081541c440b0640021241d4170 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 694282104 1250 694280854 694280857
    0x10f0c02120d02061302031e100501030803070905061c0b13061d0c0903060a0f1d0309032401062f0a1412040e090f100b0406090504021f030f02 63
    0x81ca00d140a03202800c001c102c004d080103801846800c000d11503c114800588001495550188001c0c60803810110031003100742c24000d031f65041c0980c0350704000010040c484284011070058900340c9450341c0c407595a43c180000f6020fa6018507050040040380d0b155140a81e070000022882c004142d080700d6140c90040400b01c58070350b000520802500030a00301301060505800350812060044603042c4402000007030380c0d611004107542411500c07140e1489141c481500003504190f511446080c0703003643d00fa141542c903044030380d91511a02c219001038010190648040440c22041d14510700303c0d80c2480010f50780d1504810b00c8228034298134410502019041da08001c0000014014201096444c1000b9906243c5800c806034960069080c2d0111010703900111401c0312400700b00003035556241410035042ca007100a00c00041e00403450303048400312250307112929a403000c903003c00c803e580b40d9402604850341110029040000c1c07003409000b035460400392140044451802068425205072504243e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 694283354 1250 694282104 694282129
    0xc10093803160201381203040605220f030f020d0206030117060f092d0601151403060a03030c061d0307050105090f06130809101110060311010f0c02 65
    0x90b040305a01c500000758280a10310304010700c8a1a8140142c00c242242e9054140c00141c3e40540000d14002400340c4541014044461002068980f100d031f80b00005405a8000181f11191074211505034510600f800080c2c8283c40c44d5410007c0d580b4155034646800144582c0240d034000701003100180141d41c1c502c01180642411007d0302543d003c205c100c64076003500a00840d01012900e420071200c4800051038a510940004e46c4c0900c040c4010400034065003481480300450003040004200102400d1751603441601a40c1d400c1000009a5001030503800f090321581d0b031003043c0c90030800120b440342450154030b500951001405101c0c203d1076071000e4000b810062159000480c81c0300c103211080c481c0d030ba0701032003a5025004180c28005a03d840b40401440b01e401e18034040e240c6000c0c04910310540c0c61a04000d0a51220148150b40103003140344048025000d912070251040c0c4522036a000f220106c90340302032804229003107c8c005443c102d148aa45504210b40d841180e0701590751090803034032 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 694284604 1250 694283354 694283371
    0x80a05130f1d3715120210030e061303090302040515150f0a200a0b07020c030606031e12120a060b0a0905040b03160306090302010e160519090507020c10093803 70
    0x10038820f51b03c144003d04105901e80c00606182c125030100101021440d690311002c038121610310340090385019200c2c5901508083d40013807800381001750f4040665040b450540040b2880020608850400c2c1d800c1d00c104201010047d001b4880c4030328072400f845d0343d85203140c0e510700c07518101c40b44901030900d840b500403010760351008030409202e621501481045c00000342030b03000d400146800b2011a40e13544d0302c404250110b003081c07103281159441c01d00403052501c56200a5075651881c98000c4c0d400800c0c103440d0502c0182c5014400140780b000d40044480c1e45c0000c0d120300700150710340743c100030040a542103150f405001790414510382c40036954000000d144205000600440380d410b0023030844021000598407039203c0351b00c20500c0d0600343c1c4400115030b401c480301c4502c11415500008004202d034441902d0600b884240420a5008108402c51020580d24940d2070407051500302c500712480e10880f0906060980c01076000f0f4181c0b0603600c60380c0f215002490b002c41000d100c1e03c0080e44200c50465 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 694285854 1250 694284604 694284629
    0x3010903020604031202040b031b0f0c061f0e0a0b06090607150b092202010c1e1202071202011404050306042001050304080a05130f1d3715 61
    0x4050700a62083d4017401050780c218202800c1c518808558440a0f0000320301c0e07012040c10445a020940803a159800c0c0c5000302c81d01c52452520b025924001990003110780808a012298a610840314060840340141c40001c11901c404480c400107010740101c103500320b60204160000c684841c0002e0051394810500c0384d410305443c0c4000c800f110711891015104104100074002907003080103000c401e003109203900e1010b034178440c4016100b0914085c0014522000109149124400d800c02030710054010140e0321682400d04a00300c1c1c0326007407400f400444400c00071629015500c20041d1010345030502680900d0140c90f200000d1828008440c2242d403ca009030710701c5502c510388d01d8240703000d42083c00d01c5419070a283e40c82e04040d00820b24103104218000c1200944040960b42a80c01090401d940000300e607211002c1c2e00b01c075005200008100f42004000c5403030100c0c41d40d042e0864000e1050180130804031040840e490422005401801d0707621205440403170644a03042038010001d000303120 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 694287104 1250 694285854 694285861
    0x19051002070e060a060c0305161a090c030a38090304060915020703080702040b0a08010e070509090307060504080d05090304151701151103180102010b06040f090c0905030109030206 79
    0x600040b0082c8803600407540507000304079050f04180a040c005500d8285240c840c40c0364000907100b188200d802804c0c4896440e810a212a44801064000c5406034141c507090f4540c0418107a80c0c15141c01c00510f000039a100e010f1190507200b80642c000d101040d142c00c0c00705546800140014010740d08404a6000060301b0000c5070b4202c64040018845020b1a03031529030480c4019443d007681d840090500d080c0000c0803000c641c2e642d44280f03144040208080c441c20349600c0c606008108617110325486214a90000c1003502d003030710a6a1041c2048401146007894a07a100809040040c0048890100034003481605008900a00f0720030755100c0001c58440f494a8400040c0070301c45d040740320510140d1079070720075002520b40c04141502e03000807048080031a180c80440e481ca41100c4480001e000100e0a03075011525100d0f1507038950001da000744845a00d0f6001c01c00079114502c42c520008207081010000c51280341c2202c0c500b01450b081181081d07590740046820345106000c100d00580200c02003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 694288354 1250 694287104 694287119
    0x60c12072a231f080403030b0612160203071703070801060f0e010c02010e0d0311010e030a081306090803070f09140d030c1506080a060c0c080301051905100207 70
    0x442400c00c0008070720180e09441e0502900c00c1d44007565480b2104455070709000c20645444410283ea8400381c03a0410a460860100501320f11055508400090801c90440c0c42c40c07404c10305861026006101505007a20343c440d11086a01c455618201580028080301c0086411041c00000380c1500091080d500c0c600762000500084e01600b040e41400700c2d095040840d1903000308211070b21542030030304452000045c0010380d40d03544481941d580c040030b00c3c80c520b0101980030783c2c941d41c1481d900009001c1440b60003801030700c2c1c3c00b510b5920400a80900c0000f0080544444513280c41030244000048200e0541c983c0811036008442840100e010840d00c80b0110768080341102c0101040500144006c807000d0005603121078030b48016080000f40042d2000b0300000f88040e0303929140d0a502005045e58804042d5220303002e1105c00d0743e5052422280f901803901440c2e4004045a00c41c0059145a0134042017100307000d25403114011022800740040f07142c0e1030309007400c5000c00382e0350002e04825140544 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 694289604 1250 694288354 694288403
    0xb0604020301030f020d060e03040603020912070806060d0615030807030e010201140a09080405061602010f030605090c0d1e0608070503121b0307060207060506040f050f06060c1207 79
    0x55401584100010404503c41e040301501480c0d041781c949070307800038508001000c2d01d5452444070203800005000032315190561b000701240f6906a40c43d0040320f007080e40f503644809c454820f00c00e0030b4011000280da80d2506134100c40342e041c0708040015000302c808003c50540390f0303a034108544620300001d90320306240c2c12288203603041500b44001d004000134000c0c141c10708040a070104e144036480700180300812040d40140d5024060240030162194501c0e00b58140301c50320076000340d0102d880b00801c1c05000d8424002e1400707030b070400b0700003858545030744400614075030082c543c00c0401075490030401c403401071004000d102c000541c0c9001c251711f41032034900c0b41009880e07407144d0310030350110b08200c01d00440f15041e02e2070b045000214072402c94040421078110b21072090010b00c0c90b440010080100280303584158043e29040d18108224400422200e044035002d8920340710320410a000a80e89180203001001402d0381c0c0c0e000c0e5281080c4a80d01e2035401e40020350110750b004180001c50100440055 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 694290854 1250 694289604 694289611
    0x2120f191503150e0a06050c07020301090507060810060e01051804050a0f050a0905060f10080307050d0206010e060d060b0310020d05040204050c09091501090e0114090c0436020f070b 80
    0x1040248540100140b65581c5c176004009060340e484500080540504d40161940580c0250081c0062041840c040d9181c030060b0254001160401010407080a0446448015243c082d1200d8140c0c0d60b6400c01510b00340c002c0941c040402c080441078203030988036401028010940000c000c02c601100030301d140181d400c0100407004480c54103880c040890800107855400c006150b5200300030380c45e511500e800e011029000000184000135214040180010f00901d00107143d0f800d468540e43c0b111840654001c3c00d48142e64015140100c3c0c002149440d80941c120120003011100c0b1a0300000703c243c01d0340c2103c21883d03600350340c2e01c0810082d81010302816503c150170710083c5c0d2400241c0400524040400303450321480c00028129a009a40203400010180c01c0e0781c988400d09680da02503031410344145000c024040c19552011078841c035605001c1e18191196516480c0390303408040b40e039800400c8120080282c1003076110f80005813103501d1006252020001c1c220550301c244504002880c404040c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 694292104 1250 694290854 694290893
    0x151602041d0709050901020c1213060e09270f0f0c090601170405100908040503010b0108071d24070c23040e0a060606020105010f0902120f191503 64
    0x2900c0004040310040b4200066482940000900b030b2280b071a0320b8024010542220614400c005010081ca091203014102d041c9140fa42805c1c0c41e13880700c2003200e06051514907550482d44410101da403420b19103441c0718807500c503414080b06040c041900c032460141100c040030950b410070058114403d00034000315850782015510428107003401c000003010300c0c0c00c110740141004a00008901000300a01241c0860075218030203000007a4282489034555220f8410a031080d8a45681d540803540103070300452041806071510f80b0543c244d1700c4020142000401601e62000014072481226809284c444c1034400365108a151940c1c45807074409505030307103608905c8424045107440120905a40c0d80c0b0240c40f00161170200d480000000110710309480d80c00002e15080c102417000c16410360541c003841c1203520000180b641c1ca40da68240004034814880e1211036400d8034000540641c0480205a0300051b10560006c0c8001011041c6011290090040c50008031400c108100788000d102e09011410b0740c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 694293354 1250 694292104 694292141
    0xd0302090d0f14010203281a061308071e0e25030b18040506070c05100c02070f0e01050f01110c01120609020d021b06040c1415160204 59
    0x84100040910103407400050504811002c0001008080d8150018402110000f5510307420400040c4030031136408080c00c504180c01c40d10000d158000d500910320000c40b45050303284070400d00001e0007072035031065038180080309021400007000401017084000614070310151501a1807003c9004000c03620340c0c0d110031400480c103800d00407078001c0703160502c44490110080060080c0c03007081c194003925900d054035070f00003e0407101c04150f1581104040c4140d01c50429118036a8450708140c07008624100041c000d076104580500b2442000d0384800800c0c00c16004550380641c2d90b81c070400c4024a41e400c81c8131100c0d05c0e000100441c5c1000d41c810480d82000342000c07541e590609100c6540c0368038081c0d00350704220364000306c80d451101d01e5000c0400350400a030290f5441c6001303444031002c1d40c01403404c0402c0d090b803401e03161021040840d070341e40120b40c000d510200c083d180c21074281841c19102085988029440b11000d241c84034100284500c509a081d2103041c0841401004200c0e0030807880000070021 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 694294604 1250 694293354 694293367
    0x30406141902070510240b0a0909090206040510020d11060402010c030315090f0603051b06031902210402010807020724050c0102040303050403021c03050a0c060207020a030809030d0302 81
    0x9485880d000c00301d249600050b1651000c2c104986050180c8a0020309545020503441c108001507000743d2401c0a01c6240c078a80079692181c1810600c904141080010003480040c4011a80341e00a0103829000408413802d080e10f036000a44030505081083c00541d110946216100341c03c0000c0e00948805140604064130b020740010b41034880000005003011347d41c0000c4441c402e2010144800b4100301f070301c20428141801c55910041c091400244e80c1403050104030042c002d08071080071041c0c3d1020306194103584031142c0d641d8050301441401245a6028807a80481501040d00d111204101d0000302c019030400d40000746c00e25101074541421500700110a204107550b00f10000300d40f900c0300710343c5000e400e8400c100311550b0240015000255000150010905a00402030029207000329691514107240781035001c0311502080005000c00c2c014019285024010320541003610301808000d45803c000d9030004140000a4004071580000414400d8050604122110301034006040441c903121 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 694295854 1250 694294604 694294621
    0x90f020325050d050a18051e060c0909040302120309012c07031712040c050907020312010504090204061806230f061e030a0606141c110c0a0803040614 66
    0x20885031001941c1d034130f920204105000c2c80d4040b100c246032020500c10f043e8000d16000340c58105d040c6901c410050000240b0784a1180414450301a1001004591400035114240202e129000b0816030550050034004802117294030021482020080000500f407150410340c1800c000c0c0c100c030b101ca9014901505421280c4002440034107483c1c03c002c0b139002c0e820600850741d0003403081043c81002003103142c0070b2004100300783d41c080c0c0983c0c4003256001100d90382e0390022a035a001c2c400b03482413900f2141c8010011030a0690004000e1030000e1f2000c5105078640c0b00c152019050458905e03041556240b081105620005404c1340d92811202d180c8154011030002070200f502e2014054401c03040040d1025840e050208030b010a6005040a96242e2034024680c900801862241401141d00078000c0540308040000302c1e10000c104240983d80000b80403200f5004085070513000001d0b81c0100640066100c0800018200a20681e01d041d92407030b240c5042401d48030080000c410440d8100144818030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 694297104 1250 694295854 694295857
    0x10f0303051b010216030215010e0f04121206060c150509030d2a0c03180b03070f03090c120212010614100203131410090e011e090f02032505 62
    0x10002c00044090745145050300c1070092140590b58000c00541583e0201016000328909074001e40200c18030f1311680e07032400c0c80c8591541c211000d0031482e101c0400200010400190403030741ea505490603684186108200c0c0c02110055040800482d0381c024080040000b0b50403070104008810f0414403081c20642252a90707400b820612505040d10307070000b0f2413888401c02480000082240d4954044502d41e007026000ea1201c00702600022144100e00100400c004404001c82c1c5150245514658464a04a4580c0405101c0f0000c058550205002144400a1500141032003501a14480c280351040080b0039540011004451741000303c10020f514100652004411080e0742ea4114018046070480c114418203d02000001344183e020076003d05109510046110a80303201003a074600b207034151540d0010303100d000658505c050040c0040019400c1c07000025641c1c0b0f80c400d11140d201d800301800d07190441e510b50b44441e4040100301030011201e150002241c000c0b62100c442c44003020004226 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 694298354 1250 694297104 694297117
    0x70e0a1a0f221806020405031009230f100b030708160504020a0903050f0303061e0d080d0207060f2f040b03190203160e010f020a2a060314010f030305 66
    0x404070482c400100e40c0301a000f10030711600080c0d8880420f401840c1c5080290450f0080324000c1c4a80c02d07200d401101c8900c00d4002d19500f06c800044a60104411a01002d0049075802418060702da00b02c4e80b000c80c00c01651090000d00c05020032400040d1041c10301d001000d0f408a403851340581ca50500c205800800502a107806071030241e40d840f1021420394500e00950f0009007203224880310071800380e4000c4051401684110303407400e24a08481c3c241c03840828140c1405174800786401c280c00001300803500030034a5509020001d4203001141d152482120101e071540354800380c075082c0111883c0307030f10141051038182d1704074030100c1c40350407603080041809103000b044d00141e00000410b2401c3c050441d00c0408580c40182903603a07160040041e48908101201800425020030f500070403507002d070826030080d2415600400c1d035603003551947c0400350500518040d520191020042c00c0c8080c2c054000d0160405480c00308228804a18082c6aa8816405603007100c1203910140002903201b000c60300d4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 694299604 1250 694298354 694298389
    0x91c02030412120309080f071b0302090604200c0f07090203010b03011809120f03050c040602100207020406030203061303080121200a06090e090703050a03050c070e0a1a0f 75
    0x406043c00d038000d41c028400702001411060000c100301e901d80d0701200040c80d49600c81c2208240c078030070f841c215515004403400002d502c00c070310034005106820030780d00c4070414032581c00140f120401c2000c4144860f031701c44240003503141c0000b45e889018210800280740286094441145190302d020070304d80d0b02c1d02040c0903825900c0f151220004210340030380c109803c41c94000e20150503089403400c003c0c100011965034000881d040c1800240d000c05500141c1c0d0460344142c02900c10000340d441c1400080d0b01009c0101e07840796881d1004409a02c2c10420184255501e650342c40c0d10000e5810098202041640000c0b03108031008401407404001602c01850f0541c0300d0900716016885804c0103100d1810150220303040032500100145550b440b44c001c104540c1943c401204503107841134415160859408040d0059116000543c0042d115600401483e055801070b59a000d45500340c1508001c0291410548a6102c2211076851100e01003135000d4004200d484522041441001c244201c0440c0403040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 694300854 1250 694299604 694299623
    0x6030a020f1207090204060809060a0c1409040219020c150703021902131e0612260c060a09110301050402090f0c130f0807050603220c030b091c02030412 67
    0x240e000b0410484000d02444401952101d454001c01069110100c41e00203451040c5800729601402a104203c50b26070700c0e940390301d8654082c9550503003d03030001000c2a0416820072190514030b152001c0391a15036150317805451008030700c0080004410303180c038403001034240c10002d45c400207400286406d00054481c51030b043e9186107000181c080c0060071200d0070410305142511140c503022405d0041e1002c00000104145030700c900d00d400110f03240c904028a02521410702c025402d40481c120442449000c41e124541825a00c06a08000060300d13040c18040d1034480520070448040c11003903480710203400070060751410790001105400050884498102100040b42e40188603a04036240300e2400001d03541080da030b448803896050b140d0300c0390f44800e0242d0301000c60039242c0181100d0090a0388125003c0380001c0d0b441c0e501111001a80449405110000000000d0481040386204038514406002c3e041b04642c0140041d20080c8880021500b04000c01e01400c4045066074100d103407c245d116 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 694302104 1250 694300854 694300879
    0x20405061c050a02031c021b060702030a1101081b0a030b040f150509010801112710050d0f0216061a09040b10050102030406050f0d06030c0f0e06030a020f 68
    0x1d2010003041c240001c0c59a40d000c20300d09001e4000703500c214141c425411201480c02420306082407403016000d41005800c17620b95011791441c00e007505003800400503c001d00d03101407540024503240801c002120010f0414401c1c0d5403d61f00042d801d68006a0001610521880c451505003540f00d110550001d160352002c40da04141c40d241c1c40700d1400301066100300456030300c9580e101a411418468075203d00207940011503485018000d40b40b9030b0796110141801c00703044410a00ca001d292044040115001a040d001c1607a100030014585d2a280d840d03040c0c1c0c908a41c1000320540f0003111121041500410545603c2d000c1c143e8402035454200c070000031040b644000702c1d5190460303101c0d203076031094110b41407100b44410b14514038000c035445489102c1c0ba41d9a24016600c030f00407403240801150062000c2540e044007c002403442140b03e900001c1c0542c2c982ea01c002c032820b81d507008140c00c084510000e101040b00302d5032140c0c0201e0110002c08a001413070340011180c100c0300542030300807900b80a55 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 694303354 1250 694302104 694302109
    0xa050d090605090c120708071502030f0f0301170705131503020303070b0702071e09020f0d0903020f16050913030504080a06050a050f0f04031b060f0608121602040506 73
    0x10030340998444824495030500940d4140d075202e500321000d100b030036100059130301e43d00c0020300740d81140c1c82e0401401001c2d03e000845000d440011018a0541c0000c10040c0b03800d51200004020181c5030420080e1a541010b0f4170041c00c3c0c52044079564980e00c01e42c424412562200c1040309107148090001c6032850500509038207001e20b50340029054840030440350f0401200d046520710840c2c00380c0c2286e00050f078030f2610300c09a0800082c0b1000740f2b40091420302ca03c03003040c1c009040081203108460315080c10203d03c4821504400c80503401a00074582d800c0120718140f0400d120f10144500403025a8100f00004010b0280607044102a40b81e1108480405010390142c400804501055034000313501428214098001290911005482c0100003462070f809504d40602810013800c44c0111980c4076078058800c00f82c00d014840c0c0720404168000b00003403e0303003d0104224480c41010602320315000043d4036000c400140c916079000140641105028101c65400c44250110340104107a20740002 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 694304604 1250 694303354 694303361
    0x40510090501091a090c0405060702040e160519050a090c0306080d0e030d081e27370605150409050c010f030b060a0809101e0b0a03080a050d 62
    0x8040c81d08200000882040c0b56114640301d0a0b20412403104c600700c0003c10040d4142191445980304040c04148440d04025010340032103071000d000040c000446200e003a00c1c0646100e00342e510360031101810300c8a07062604000e0140300d00481d41d0b044c0b85040000207400c1da01740c3d001da14465a034070051001294400d0b08240700034110b040956911005407007004014102c0101043e009100304190744041901c01c920440c81040140d041c00e14050307143e451350b0842800540221001c0220200046407220f00303400781051580b10b840102000503808501038109681e03d1100004500c40d080500030203031812001070744159115000281d141c1c2d529000d03600501070000d10641040c58100984200080000e50004070482620303946403c07200320304210141c1d03150341401c0350855028844090f595008219054001042900b6102190016000c07181250800402121100c090304128852445144600d4921180c00e4072541c0c089411034448501c02e204094220041020004030a000580e0550 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 694305854 1250 694304604 694304609
    0x904020604030b0708070e09060d0206130b0d020901110d0819020c0a06020c1506130f0e100204050a0b130308160f050327030a020f130f05010e01170c040510 69
    0x1200f41c2c3c035042101004103918803c449000124034800da103c215481d008050600c110301c01401c01d08000d81da80d080c00701d160071809884240061440c4081103c0003a80040c1042d042000300040e11000c00c0400149040c4502d8a00030340c0e0303080f40701c1c80e590f0254025940e07644003515000785012142071894502c02485600141000e41c06113030702030020004c164000f84440384000d0102c40e082407503140c6000f0850320a440d9189d022018000301040c1e00f9554021002c003911a40b0001103900a0b050392600b00001044410401980001d040c000d6250a081b02c2001d03003400c4c4a00f070b040c10704840b07810141c42040e00004c1d1882d0030201c2c40c2c503c000c91099924011680c00001404d44186d42c0c5016543c0f0b03007095010300b00c51144502c10f0424601c0c20752100c0c1c28548000c0045c090744485800f0700c604c9190079080550000c003400c2e400f1140742da60b809103402c000080c6000141d01d614001207042090010f0b0400d0810b00345100d0205211200000d10302c2101c003086a0004554465034a070003480303200365 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 694307104 1250 694305854 694305863
    0x10050607111c0c0f0e0a020309060414010623100c030836060103050601140a0504091703040b041104020c0a0219050409030201060f0602010e060a0209040b060301082d0c090402060403 80
    0x43d000c2a801c03018400741080f0344a104580d0200d071030f03112031401640400c41d80044140e10540000e80810f46081d11107455200c00b4000103115615070b0b2048411001c100d9103480d0400089071303203802a040c09101c60511440500d07003206442d0f02a1350040802002170184040c00400302040a8480c071503090340d1991039079001c03141419213055607007d91240e0003480181c640303010b450f000149000b4402a130103c500d4000701410348250500c8100302c02456262010f541604280355007611101c0c81000030b6008034041d40705110549440c1c60460f5402d108032001e94000c03801400044100b11001662012003641191009440d0300404005500760815900280d030041c100488a0249901036100e181030b140744c0888803030100d8a809060f030076582802ca8090b0194003020000d009546154003620050000034000b203080002e01001441680080e042582c05420058000c06140d415903458072480030070003040c0c45403800c007109080d12800c00c0154103001e102101d001400310342c1c5080c02c4402544d4030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 694308354 1250 694307104 694307123
    0x24060405100c0b0a0606231207020703050f07050f0907020c03100e0615030d050a020102040b0703030e011a0306071b0210030519140a1806050702030310050607111c 72
    0x400001d0400410b03070710035251a00f699000c281511541c0c015681540e1440c5c88040b9010a0702c454550320482c60120004105014003108505181c81c1408500030b40056004100c01801c1d4140603081c403242107014031982c0e202c0c0070100043d40764060341c49120303281250b4a03511a6076604083c1e00b0b004102e01119818051b120018801c01800e03130104d584502c85100303d070b0041e950200340e8107946038129051035240e4080305107a00c07105e20840003400c854a10b44005800d0a035503a50ba0b610700c1d0000901200030903150050320002c40800d01c0782484076528225001080320f040c1001c00c1d19120040e00b00c204000e00b40b680c4080c1c0300083c4a1116019a000d04285a1440c60b60f41c000e0040c1019240003115444680e4000201c0c40301d0b028841001c004112108080e450703150800008140e040c218010b02102c140c907002c040780c811f1051a02c1b400c102e401a69492914403d1590030710580d400c601c1c031420080c002080411050032140703454003025202103055000713040c00243d084a0300d10004110098 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 694309604 1250 694308354 694308379
    0x126030c0a061a01030504050a06150b0d06061202070c030210024b0c0d030e060a0305060312040b030f0705040302121c03060e04030f0504180204081524060405 70
    0x80c5039100c241007008407540703d20b01d040020011400d9800035607000d4495844002d00c840800d5980d401950031200100c1405ca1647e900c05601300543c002c00c2c80e071b0440d641d9500d030801034541c2050918000e1010360b842103207855515a5450030614075804003074003078074481040280f0300e4000c120309800b0244500b8601000c0b000e039421840075122002d20034102980404600700032006500d00d0740759030070004001d41007032140502849200f8800342c0c401c2c0e0130040d166450707071015200d000050000c461203580104043c94088180b500e404840020300c268000100003c004c0707030702e1034800d40341c0203155030f024400319890310030007280c10303010300d80010358000e880004034100801d000440c003840400d2080c00e00c0a03180c40070001c0d81201d45612504c42c1580b80f0000050000c2e00c2403114600f618020304103242042c1e19140c1d242c803888801c18018a4056000409005009003000685540031141c080c01c1e01a16110000070003800f079400320711544014168908560755140d0050b10701814000e055080c0446 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 694310854 1250 694309604 694309613
    0x2010c0b151507050106060206070525061d0106080706021b13060b0703030c05031003020121060602150f04030e01080c070b1611010b0619020a02040905030a02060703050126030c0a 79
    0x6100725012181580b0380807000411f10300209860303101d00015120241000c10a595107418480c0c12072110b9500c0c40c40a5020740000d049114440c02c10044e80c08800541d08211281821030b04242c00c0264181d000c100304004155000506110100c904150030100d40c000e000807400014810301100205400e103200810107040c0c10380613041850084c1e42c24402e000351040e00740c2d43c500c02624032104850b81d180742400954000d440c500c4107560050341c0d04050300070992013a400c070f8900d50003c100503048004034240305200070103180c3e0000e0244910501c541041e40d0040c042240031036900d410300207054005424001c0030010b59001c150040e01d1002c06103440e01a2490751420900d9940108100e02e40c80b100c1840144184004d040021b441c0c5881c2540c040e01c40081e44503011180c00840c4200c00c20b040041e00e9a00815010f01e00c510300440d11803112402c0a41400d074000c3c40c1c1000c05181400401c0080c1c421410503040c4082c00040380130b8452004803507402c610402201030194424000c8800420 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 694312104 1250 694310854 694310857
    0xf0d030807140405010f0c05031b1b032d0708030d06061e0c060510050d0b09060c0c1209012d030e0f0604142b090e0402010c0b1515 58
    0x201842d940328805000003a00a04290041d8010640041e004405030180180a2002c0050450092045a091070b1680200400e0403101d0100c00304141c0294440500c2c4240c1c00d8400c0e0f604001c120050400d454200040560b10f40740e042c2c0c5030890600e5048065010721050003104040d000540640b650360340250805030142c0550700c140360000d011460601c4400380d006404218101d180c2c1d54450f40349256444e1280a0500a41180e110039840701d0300043c590f46007020790801c0c40c481c0595011918021001c5800c10000030540c1d42c5010080040a042c84008140070640d131000c124081e41303540703000004803440303c4c100041d500360240d045001d50880726084000d004002c5190380070300600d41c8248146403589103e040c4424140c1c0300030b0214000038807403200f60004da003880003102c540e20a14800e00b0440140c0100340215206031019224000fa804102800034224504c48200c1c10b080039800240325a402e21009080c504513003000c100c1024200c6188104a000109a2031404959007c1560305 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 694313354 1250 694312104 694312111
    0xd090213020702100905060a031109030f010b0a140901060c1a07030902032e0e10020a122a03020a031508031216080103030f090518011d0c0d02090f0d0308 68
    0x241309107100042c2c002d104e620301c0b00a40c4ca0180c0704a08013012214103401a084041c000440b4107014040d200554500700040c0e5000380b003a1002040000242d024881354141c41e4000c2c8a100b818400d100c2a00e460b034150b500c1c1141c2c0c1515113074010700d50900f080341400c4d40140b070b50752107040c1000620041642c1a000610424001c5040c1c403204a03220410301c14070034a540b50804204844106c1305800c00040e800421204d048400b51040004042181400c0740e0202c210500407442060000301010014442c0c051900788810091060031040c0c42040300c9144032800b01d01c100354001601c03c64251182d04032440703c4c0c102809401c40c0a0300d802d2443e440340c0000a031034801c03600d094001002c012081003c0b40c91b480c001e495648040c0d00b591811102400d941000c072080c04140900058241c50702c02c108600c1c0c0d8252800101c45504200e00f00c0b01c80b880340300380b010050310000280083d0311460b200305c070b41030601d00000580d10240f2002090041421900481c2d1180300e203001c04c7c0a150b00080390300c0c403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 694314604 1250 694313354 694313359
    0x6080a0f030923030c040b030714011e051312170d141503010c170402010c02060c07080703030e010c021005090301060e0a02070b060114031314030a0f080901020f0f0d090213020702 79
    0xb261701508184003c03602180084e6600d5845410100942003007803a200c3d5560302c0600d001510342038004040e0314a82205140e0000003003002520b401c003040b94105400251680b0b803000c81e0401c181d034803500c00203041442c2044404500160307040c0c3e00c0340203612003100518000b128034098a001c00014030f8030320900b0415400380d428400d884504034818413840412090b4034040f116640c8658004540380450f001080740c001404001140c01e1000800c0400001d024100090220750304619004094052070300d40b943c14042008c41040060340e400300466520403803480c1c89521090354100184c0035000b90340c0280d1800440e07201344014011136400400950f80079103003210b11511410700444241e070388600201003c60082c004500b104518582ea6020305004001014441808056150565000726036000110354801c4100c0340e56504000e50542c007000903002103051030f06003035221700346106401c0400e144000010705807e803d24142c1c000003055401500c0240b04030400c1c102d1100950000d8030503403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 694315854 1250 694314604 694314613
    0xf1509061b0207120507091107150e0c0105210402150a0914060c060103150f0513140613020d0f1b0906090614040b010e280906080a0f03092303 63
    0xca544411150201c050351000003020350078a04000440181100704110301e0500d001c110410102b84400d20740e04441c4140300d00095906c0003104c8440c41c11426044180c184030080c04240c8000008030400c071080c055503604048290f4603840040ca081040305410007103c0c0000c01d4504040d64440c00520aa0f4100c0d070308110791144010800c010b900508040c00510703440180140001400d548800c003d11140340b90200341515210400e0081c2d076012520600f551250040500074440720302c0e4404072004c03c14024225904286420560090170502d02a00880095130300f2810026045044180160000d018441302540c0303d10b0b404860174203204240030b5074280744000c541d102141c4030b040101e824012341201009810300c02d01020b0403103103d40506100f400c51419440f5201e091800007000100e011620301000b1701143c80c481800c0329044000304911744074060003003031000100b100c1155001001140d11070381518088030400e0b11038202d102014410300c071682030302181130000200000102d085d04c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 694317104 1250 694315854 694315859
    0xc080a2f070e1e0c16080711130e1902010c08030f090708010506060d09080d1d10060f0605031008010606050d050c0a0905091806041515030f1509061b0207 68
    0x4004100d56503c0c03412080e0f00d480d004c03641d00480031006044429035015005c0243c031142d00c84c604250401d60040e02c40c01a101c100c0031191401c0000900b80c0d16041500f08841d0183c60309180da02c105810a900e01108161020801e581c01440b52060495012203010769070b140c02004808044010b4560b079003944200c5a021451801c1070048074480d0601425507400c10180c0f82c40b50340035010030ba1041d0307401c00b000c10002c01c03040c5580c000c031114211040740c1c081d21081166500c40c60040e41e000048400345c50700c80c05000c05800c01050000325600c03890169103e4a822100c000302449950141645601c4c1c004006240c2d80c0101c00ba04541c005c0d800c04000d503581d001186403080c071605007000001040441c00b4007252401c0c008041d004400141d02c48105124017024a24142c1c0588040d90140c0b06a1000d14a1012038043c29081200185410003003c0c515550141100a0703540004c01c007400d400171000b0012803a60101d6041508100144000310a95900310491003041690900500803080c01 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 694318354 1250 694317104 694317121
    0x80a110a21140a1808030d0903140a091406040509040f020310060b09120c0d1506060905011b061503061a030c01120207020613080708010c0c080a2f070e 67
    0x5103841c0303440c0001075803408042c0c003001c0712a1130240000030000c1c0c01100d8042440203003080a4550400c0701000050703a03010b40d04002c2c0441d000c20740c001442c01030800804c001c440d803110921003200c030005800d403c10240000082d03e50701440c1c00c29a0000401700401085c421180501d8880c50700982c16a01440c107800b034030200752209800b070009082820011b103400d508044443c808110400ca00340d41008400c60002041040b2a000560f511105001c06201110891281d41d0080c0504c0c00c01c00201c51070000081c1044640204104215007214034050601c10380c0e800c2004c204800304841d00031a07849240200080020b15107509002461100e68003090a0000e951256464140c4544180c2034030148010081e601015040f604584188a00ca0801842940400240100c0c101400c0701c142840941402c407000c0d441c00c07408000d16015100d012600001c01c4828400c40c5243ca000e440c4a0180d40c44c103040e041c070b8062000a490031200c01400040482c154058480007100341040c0d80b50203c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 694319604 1250 694318354 694318367
    0x52e1e05010e010e030a080c010e07050a0e22050604030c0506070e03060c0d021608091c150b010318030504050a060c0203030f1b12120112050703080a110a21 69
    0x28807400700e00701c54030064a0307600a440d440c0d032200004084802444043c1d6400000344c014400c00c4050340e45490800d46c002a007800300d04050181540d1446241d45000340c001c1d030281000d0203220405e662030354510f4420000e18420104183c02c242111232908007494000c010f42d910f00c40546280c05041c022441842c4a000310f40d200e448002d0041c20251a544092986075000f9104c41180650130040c0440e440488190f081d01940100300c21030f10b51a44cc004d01051141154221070284408603500b00081c0044016100b0303c544001c0028610380c035030f40140d0007071040406c440140081640b6100406a028009106484064450404182e61a24241c0f1584403a81000354036400601030500301034240d8003e044001d80c0c14507030001c1c41c20407200140c1048000900e6403002c50000a02e06000b001d85c019050040041c1044500c0d88500c1d520307a161074440c00c0c04010001040055080d000c2c034810110401c2e855a2003059444040b100e203802e8891182c034240c4950782055003400000368500808 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 694320854 1250 694319604 694319609
    0x1020c07090c0e0418120908030d021606090c0f0504020f070f020118060c0b06010e01020307060b040f0f0e010c080c120c040f090c08012304052e1e 65
    0x4018040e00e410150510080d0682142810800100445010301a03aa600910305480044480c03101101c80034140340780700c8a441d203a0241885070074503003000044c000004031a00c6144d050401030b1221614410008a02403001014028a040004040c01d002c181c041c10021249a8071441107002d81d038109210503400f485441100b111400e0041101140741d01201440803441450032071903000c0c210420954041e295080b060028011040703041c2045004078600c0d170400400d0030411448200320000035a43d21400100030809521110b6062054840d500700e1111354101c04014000c6c640e81f95480001041c2c1c110340d111186d030070465001085405a404c00d80a20034074204949810f4003075a40c00004c90000e4108c50360884100400120306111001d00c034060444005c02203002c08160100511207041a003005a1001284020002d071042c561850440000190380214044d6030705030804129014400c0c4078041c0c0700d50008145c104800d990146070656550b035035011491000d8140d0540d0114590 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 694322104 1250 694320854 694320877
    0x140f1605061219051e07142a0105180705040203060a0e100b27031c1107030c0303020c03120408060f150d050120070503160302150f04060605030102 65
    0x300071001c00410800ca240340d1092952075010320f84814480c0120444038122421030b410080c8804801452050201043d088801841c00c0002c01c2d0751241000c10601c42c0b10100e00320110b00308000101250b030f20043e034042c0390900c0020040c4c1e01d02a101c03040e00d00160340c1a40024042e461001c0780310320b40740c426240035a002901600d55a814401364010440000d0320014000303045440019168041c08001c0c50300da044203401480804100c1c405001d041c82c04c2048900c40c1d00302102092030802040900e136801d80c1e1900d00034a003503004002250a005664001130034603046c610021040c9500001c01c480c040f4810740444003082d10b00520060b450041d400307403010507040540881c0c0e02203900002e035034008503410210103c82624800258400020040444250351113004401150180c01140384040c600e03480150328203255907444688034829161401146400034841e441851b10820400107812074800c0c5140260400100010517400110303402c0700d115042141c0450542018025a01e084c40350 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 694323354 1250 694322104 694322107
    0x120c1803030c020102120a050405360604090807050303100f080a0305030c120a090302060702240912030a1a0a0602060402010f18031a0f0601020a080f07140f160506 72
    0x35540e0484a1002c400400e0381140b060140011001100300024007034078815413200b81d5180c1c984014031400c3c031080d041240b081c0c00c07403000e0703d8070f001c03038950450b50401c00000ca0b810032642c6200001d0020403910002401960011130f0103810420700100850040c10f00c43c04080c0c03166502e100070015000b40e4014800590400c80007030f000280104051500b0038840d490880c14065002e0342040c80b0301c01190340d40c08280c0c5400022090503010f00c00c941d004803103071004d444100300c01c00304200350b134030041411244400c4d40c0c40002c001c450140a000190a49520b0642e601c2c10000600005003c09141351082202210806000303407609516039422140b1304e40151031555540c0d0019619200c260061506104540d141180c0f010203002004000d03502c10000c040f640858036100c9061004005d00c1074650414280c18440c00780c4e000a210380920b0b52110f07000d543c6103e0350002489034050303200010326200d0101114003136800003007881c3c9000035a21049407407140d00310501c031403810054490140c00c22320 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 694324604 1250 694323354 694323359
    0x140106060c031206090e0d090b04060c141908040801060f0f0314160f0303020c06250303020c152d07050c16030b100b030603030a0503060f030d120c18 66
    0x140da0f101c50040f2802c1000920315580c03030040c0700351003445a45030800e82001c1070015103e5040044813025001d0300298a007060705100015107891210040606246408605440c1d001c004100c1c120560302d000100303942c991100d02e0308101d08d40060007611525401c01c800400e40c6590b076903e5800302e804005a56107503030700d10307110340410280030002c00c0c1ca80d001d8090400d40103028841d18100030308050449000c51459400e00a04001c8006500c611401c010032042039400e00305503042e0543e0f420701c5240800c41e030091505900a02c130340c0c4030501150140e020152601030405d80c40303503c90015407000c2e00c1d0900c1d04984200c031940807014800cc28000070000300c0d5000c0d01c80c40161203400e5a003022a144510140d0150041311400c0c2d20450780121042c04009040d03200480740801801864055401e40c14402c0c0000d850380600500c0104102020000032002da071401115448920003400f1b40e510070106e048001c111b01001d10007190418248625511071901c40c2c404018124815104601c0150 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 694325854 1250 694324604 694324607
    0x10e061302010e0a0b030a0b011404060302030c070f05010b01090b0702011d1503150f011b0f020d0b0a050a0b0607031b05012009011b02060d050604060b16140106060c03 74
    0x25940c4001d904100c51044040c0c001d899968848018001c5001d11544901c1d05000d840281c4001c1c14600341080410a00b6200a07010742040d5020799000341030258582d55451a03a042c1d600a442c805803941403024008020f100d01940311901019080e690043c000f503d4080c031000e248034442000703002800501c482851004a00350008100340010030741850300b03402c2030400015401c2a1a6017800e83d400b240503185e545002c2510a03203480003801d00a60a81100d80c49005203014040064500c0b00e00c180c100c01190740380c074200d801e19503000d41000140d090100d03482004220858072440b2091800d1600407903498600141c2c0c800780e5042d030b100030220444d207140c5224000c0c1c848080b0781d159292504e06031b00081f00036800b4950245592074540703500c0d024000415500c0e0108117007054041404106000d604d03100115140b04000600200d102c0e2680360214000300171540c48249010b002150821a51441d00b0f4410b40700c901a5850034122608100303401c0c04c8510521908000caa041078501002a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 694327104 1250 694325854 694325881
    0xf070b040c09090b060f0315070e03010f091505060406150c15020a080717040b01151707090306051e010e1f0f0501030507020115090e0f030706020714010e06 69
    0xc0c400c00c854405507684403032400c00e40785003030800c850300b2a450713003040150704201d07007a0751030010120020032350084c0c1c403160740c100000c01400600400482c0040c0c040303680c40c07d4000e15a03543d16241d0403c03541d2191308081079481010840011401e0503c3c000c28007e2805006100965140403020300c500030080c0d2003552020340302841112140c005080b10403d0a01c9440901030181030b81e11803030201e1030208402040d81c030813040c4d14900e404c500014400464041115181503403c2d51001d00da84910b00c51080e501d501107160190720340e41e100801c0204a0354060451000c90f032007150b040c0040c2c1c0301e1002c404035220f8490604020311030307920010007500b05541e2409820442c1c4000d018005010007000011071016500904c01d103020600c1c0820030b03940d261164035030001c0f8601c020000c0d203529100c07001003000d2512800308070301d4a542020701203400c184059203860204000b140e50f1a00b0314507050300070750410300c000d985040700c00451031814807040c001c080c00500344c480902072694503a0002c0001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 694328354 1250 694327104 694327111
    0x819020d14070c03140705120d02031e0909071e02010b0d1e1202030301031101020c0a050907020f010216030e0901061b060b0d03030504050618210c1b10050f070b 71
    0x200105164000040350140c2485e908008a480140440c58202014822104080f2004540a078483c1c040001060f5010099840d940e5141c0300c1c1081c641071010700000103004906403554040d410304103218005402401c0da2114034200788140c42e41110701d080c1030b0b080f035001c0d030360158025107881840340014010042c940e0000049116040300c0c66019140d07008801c0c01900203401591000005205000310000a010f5043c0c0074030040080c2000d21000c5440d404503031040e140207841003404642c0c12030003480343c24100c40182c3c00031034483c0300703040001d04007400680081d8041034042900110a007060f100150680c2c0f00c544429840884038183e4000c0240ca1007002e581e0950343c0e00381402c099880004516000c0d009580c0440c0380d00b0030741041411b10b18090b0030500b02c503111f04864840c4d5100481c0a1645a111615204040e9103200e1806011f00c1003007650100390140c007515100e6400d60513000601e011095400421244480304140c0c0c00e88a82900c4060781a401d03c003560010b0742071928251b0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 694329604 1250 694328354 694328363
    0xc1202030c070806190501180b0312161e051506040213091e0e07060c0c03120c0506090313180b060f0d0f091a220819020d1407 56
    0x5007800800c040c81c148a6150000407043d0006410701c032402006505204003103041c81010419945024003045140709600f1480e000d441e1641c00c140850b0342c0071b202c0c0b55450018401201c1e525540400d03030f98103403007004100303d402079140c042c4c00d100c07040d040000b50405d9601c40300420b0b82140c0c40b42171107040c800041c81298820b03020801140e8590500158500600903800080758041058240086050032000c1c805401c03480c081541042050011391202120103a040540c85c100301030420280407140c5810103440158442541c0510590100c2100841030058040ea8825201d00b4001d42e01c030700c42e0b40d00400001036241814000090f10083d40e06c50304608920001c0e0800f45200803404541040c1001c2441d80b901117119880c2010502650900c240d80701d804201d40d1056990b8041320502820070843c6515105000502d40516141064200c150b0b548a62200305590b01c0c01c2032a5a00000f000d01144007a011175038501400040c00030b8503200c0342d03210260450702450004245070885201a103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 694330854 1250 694329604 694329607
    0x11010c080d020f04090f0b010f0e1302041712120c2101060518032a06070609050102190c0323091e092409040204020405130515030d0c120203 62
    0x5036000750078070003860320829011407141c07503c2c50305504e00c04941001c110981d005017001e5012040340e078480d2080c500034549041c0905201d1a000c0400d441003006418242440d100242c0031480c422160145004501d02d07500f1103802e1190407021038010302820018001502180010800b00400800680500c10071040d6490302440762405421072041c013a44002c2c04114001118440b030714640720040c410040590050515000f020103103000c80c5070704042c0500c40c7c104015001c03001e66a440448619079000300042c40885000c0c00c00794000d500c039280748039614000c8030b440c100050107506034115440d01615000f00c443c802082288640e0384038201454811410008050280d440c50481940700c07110000c07450241102c00144058450301800310010150380441d80261950340030702c0c080c8248010341f54006261038900c0414007070f00887d00319030740c40455448201a800c4860b80940c0c852038290388091401c15814042c552509074441f5658001001010318001080c0724a420044043d002d01c1245e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 694332104 1250 694330854 694330867
    0x190b040b031308070308090c2713140102030718080307060b030f0d0908070801062723060a0512030a05130f0b07060f022a0c1e04060b0711010c08 64
    0xc1c00e10b83c444c0400320041951a820320000030010405601d5080081d900441e50412049a52042441d2528034406c0001c9200020700600f0451000702074407a448901c030300d4a07180010b543c134041e4000301e98000000b900b851403460201050fc850304200c41120001d545028410780703c42010b030004010f41e0f1380500c40c0e580c0c2d1b0348042208210080320720742d0030394a940034613042000130b90404681e030b44803003023036810803906100c842650004410a840e14080d002c00b0740b021204084054081c07014400c105c1840d82103e80c03030029455884c00e01c10402201e4505050380c46008102801d00c41051000c600e9006000424441d40540e00509102c0001d59400c0e668a60710720b01c58041d61031a03000310a00640110b00c0c0001c0100601441001e220101d0040d400c041038203207030300440c4030f00e20741d45010714030b070030741e1030300d1114000d0081140c0400041c0842042d08102c070f940c030200c035200440c900d010b40c1c900940020424100c0c01a00c80455001584014550413200111081031501c3d1060300c0c0c000c1e003000300c0c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 694333354 1250 694332104 694332113
    0x4090f090206030108011a0406062a08040b09100c1e0503040b1809150d03030507110105070504060215010e0412090b0c0c0103060608091c050408030408010902190b040b0313 76
    0x614000c001042c000308402d19142102c7e010480781c404028011400c2800c18440250012406440c1c1d501d081c2800d010603000b404521605000d02501814818000a0120300760b400c80f80240b40c1503105035202c40107690341300320440308400701000240801d005101c0081c1d8842d94003007030185150240c4100ea04264498600d040503501254408006000c05904c80a03503080144805074001000640c405907258043c01241c0c10758001f400003010103030344000003100740b802051b02080048080008000c40e2070440c10240495009001300400340c4188107640f000350000700c129505907030106554099070748540c1d031402180b00410711140d00b4018121000b20315054a20b019016040c0142c000304540e015240000d0101c074416044201089060420840b400c0b8000903140902140d00200e0400c0b6a41d4500c200d81034003958201200c03500000a0000d011281508030b1420320f4000ca607242e04045e050b2840701064202c0d40f080441c0d0b00c4082c007007001403841403005941d101609205184da81001c56a5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 694334604 1250 694333354 694333357
    0xe012f03090315010306050906131203020d0507080103020102101e020d06081f050c040e060907020f03133605060307180507080906100e15040509061b0f04090f090206 73
    0x11009400c3e10710010030a010f040e00172103030042c00001c00780086050045c0c402640e02048000500161030f90501414898031907411220329109010041200b81461100281402c000788001c1e0b006108040e44080706420520450a10351404408a107160505010602c0079401c15401d040007281c1d168030001d8080414403500c0d010084141941003148040d40b51003045a001808858560400703210900003401403000b0b075600711004556840702030352150780491034001c40714104000b0740004621011045248488502510217050b01c1e40c0c0030a02820f2082015130410031890724517400080c84000348629540483c1e042240070b0306840249440d2101c5a100712486000404001c0c0e4805c05c01130004d9002812039002503081d0083d141d64109500204100303c41406a00049865a000b2546504010424180c0503002800510980c0f5110020329101d440c03ca40c0e4041c0703d001d09004010511081007101c41420300260030314145030a0080c5440200b090011807420269141852009030f0745000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 694335854 1250 694334604 694334623
    0x41502030408150402060904020c1e031c2a09050418031704022101060306151a040f031203020702130b01260705030403051303060b010e012f030903 65
    0x2002036030348528018580c0d240454160701c5003041d400030710500006076150812140c0c01901100e001da115903014481f2170500700300400c00c01440805a80040c11601c002c00981600400b250950207003000e900e00c804151601a03815100c00d0340e40c80c010900c4801151220104c9082e139290800d26071b629400842d040368081d04a803448440301d060f01c0030405038400c044d102c6640f00061407080a0802d0b90104600c4460003d00e480300369940c0210009801c825032100f0011608440d0900940e42440b908803410b0480d4007406074000081314144900000c408111801c60707070744170900d6081030b240d03482c0c950700c030002c2d0200300341010f4003080183c0159442280c0c0300141c8003803c100290a4078030740005068400c510202c40c1c0040a05100c40c81000c641c07241d00c83c0c1c001c00c14200740382d07030783d0301c51030220b805100d415a04524640c60040120902606da84442c3d00e042d070a803248120b00415400540d20a0f40d00c664080c601030780300c060035983c21007403541d4903041492101113034200300812001909180552 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 694337104 1250 694335854 694335857
    0x60305030423030a020103020c160306050f0601021506090703381e060d021b0a020a090905031b070503120319150303050327010c030509011802090c0415 67
    0xc9020710898100101c0c51007081c2d10200510036210010707001caa200d01e080500030741410750101e080b4045150900000e5981c5600c80342880c181e81c0c40e841e0441c010f01c07040d100d03100001d4034000020041d5000140c01183da0741c90001c0c26203d5034922042155140c0001c2c4110200364036a80440c0803a01c1d0311a5654004c5172014008240e451501c1c0060038200400c2c049a10482c0c0a151504004014060080c0388410030354800741d4400c00c021485020b481b03003030850280c02c002c1400300404171401080004005100b2940502c90541c0c400c8000152002082c0280c1180c00810100c480801514000040201071034196040e21b030340d4500103400d210346012b2100c3c9810001007007002d1075503200342c00d00c1c1c0f103070200004100100000c88000030140c45030100034240038001010549d10182c50040d940c0c0040301c071441c02030001041e032043c2c0c040d00303440c28180013003402d1102080c4902418080c81001c01d6210074a4202d00c2410b80811131010707005088842c40b02401c0002290450052540d641e0741d000e035 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 694338354 1250 694337104 694337107
    0x409050109020c0f120406050310080d0207080f06060a12030207050603191b02070621060909060c0c170d0207021003090302060f04030f0c1e0c050a05030102070c0e1906030503 77
    0x3543d02044c1003524621441c4010b8000e038841010040c0c11a09803815107441c1c1c0b4080c0e0700e03561800300c000c2c008845900050214460b00c0240014540d000541100707850000056a204020074070403266034800582d5120360150038643d0511002400701443c1e9581703170083c03044607090b0b6074400106410354030980301d403a908805014440014441402084285403c90248005003400004001d4071009140183c608024958183c940c2401031446400600313801e01e40c081001d070b0f683c2c0700c60200520040c1d40884099040481c0e18941d24002d41034004007680010b0a04004144e40d09000d581ea40003514140c1641c0c2e091040c0c1016072100e2a00c0541801c4507100082c0d1300c1d440d410041d00c1c100b8000c2c0481d400b040741408010019601c92100c00080d4141d04014030307408a02d180401c00069200340c01c510f640036440351902444420751503001154070540b21184034540f03840505084c1d124102e0090071b090b215403070030031842c1c00c4030320301c00d6200541d40400005185402c80f120180d0f1001c0d030081d030700c0340d20 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 694339604 1250 694338354 694338367
    0x80724021305090f040605270109030e0d12210203010b0a02010b220b0105070f061a0f030a080702060c03040603060303170603061326030103291308040905010902 71
    0x1800325054024240848443c007082ca00080900f1205000402c003d02803030f155000300d09800404504000002181441001c000c151200b15a00030441860141d00052100b50109100c1c1030070040b800d16940c21518580601100c00002e5035030803c4501030302c002500c100031543c2c80801c540301542c00390071941d128550714202d0309002030035a007411184503c2007801541003a0710307140031581d1607600760381d42d5004110103020f0b40041c1e41c0c07405200d601501c41054001110100b200036800f0700005800802036003004d0f0752a41c24000010b40360200e0f150550300580320000499801405091094402801c60349801e40d880800e0342150002d5020101182c0c485805100301a0003007a5440441060800141e40c1d28100c80000d969030b4001e000404c94070301c210301e094144440050a401000300220102c0703444148030b518400381d40d0092005903800200384680d10101c004040c0104043d485031111140251506a04408056410102110061000c0100159040044c000c83d070003000030180043c0c07200c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 694340854 1250 694339604 694339627
    0x90d0302100e011e0c0e040507020604020306070801060203180a0302040c0248011205010618080601030302150709050d060902130b01050307030f021303050f0d02030a020a08072402 79
    0x15450340340080e043c0d0402004034902c07030954018401c000711825021540400010013075802d42c02c2c13007480d1608507040c4002c01c10304513000501540124400e40c102c4102c1c0c0e80340c500c1100c51030303828000d41005800c10070500c000c0b4000c42e07502d2103001300c0c010320a0a8480c1d407a8000340480314015036003005600171002c0b0f071250034000d9408013034088100c400c40504000f2801c40c400825075400d40007010882d911100d24840e441001440b02001002d64100300341d5844140142c0411124001d1140307a81d2010000306424001141d1641260342c150000c1a042c40a03210400b0b10000003403842c81009504030000031150350307210340c1c82c0c44c841c040d40d0000748124680c014007603900d40c2190560740081c10640005250790340001282d038850544d25001a2030014107a003080030f03118003000d44451109588000c0188000455149800007120b02110f950841402d4185e03282e00070b800d000d10241e00000c501c00c0c0403034149002421907600c10b00e106a0b0f042401034556480c4480d0201041c2084e80c0419802d003001d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 694342104 1250 694340854 694340861
    0x3040b07120203040807020d03020102090901140a0b12070c02361303090306020a11030403081b0610030209181b03010c05121302060c060106080609010918021203090d030210 76
    0x8041c0003545035150585901000d0303c12500028000c0c170440700a83c090510070340c141d803c0185d008242d81d0396941d403080e40e49150400d181c0038510811414000041c026801c20803940c450100440920250707031a10010350f1103400c2c0410076a04001c0031244001c00d18003014030b0380c003e000c00007003032100c842d401582000801401001260007080400c41440072070340168400381240c1e44038030003580d10a00c1d80b82c115840d02003021629131510000c10040104035100780039000381c0d004031202803064012b011b03078103680380c8050703070715038030340b010b03540041c000340c2015140f0070744c4140360140f80e56640c90307130030f000901d03003101c113016020301e01700d45140710a81340b80c00c7c00b9024600e00300389095410400d45080d0b802c0e801d00c02409102c3c0c0441ca0402d17800440d2103104c15190900019000e4030960f42e07403400f001c0d004900844440e48100300c10b00000c5400c0540b4030900c15010302d101403010000d4010307070a00544541c081c2c01504140b006204c0f40718135a07660740b4002030f0280300307901500700014030f6244032041c0c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 694343354 1250 694342104 694342127
    0x9100e0c042315040605030604050f06090f04210206090706020718050a151203030e010203071202030702100501080c0a080601080a33091401050420120303040b07 71
    0x903504204010000603203071030b2106282a0b10316000101c1400c260000800b5080d01d10207000c0b20850210300018541d030002c024610401c403d0b00c0c148259540d0703440c0b01a0141d0102c0fa415803051842010445484400078110f0340284140603403a82124030a61141091801001004c01039001400704541c02109000483c020601e0380000d0000f9410800803901d842c000c800c13641c26180d86c540c001004500c0c0380e04008070240c0700511100430143c0300d400200d0011a100f00a90104c1d00700760700a120a03605108882c40344000d0790315071032001d807c05980030103548090010b000310711030740c196505501d01e03520500c0c0c000c1115000420684103030505014401069901c02c40854010400400000f02c2c0480c02440d0b0603030003010b25882d00304403006040b901d0300040d10950482007011848003013190641c005000a1b0240c5002c20021005107407080c260342c001c580c01007505206103040052460310348103800c400c001c010030240c06128018802443d41d041190243c82c54064107090010300c0703811000001e41c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 694344604 1250 694343354 694343371
    0x1502011407051602030c040e01020327030a0f0e030105090705040b040e0d080c1903270309051311030f160206010f06050d020412030905030d180909020103060509100e 73
    0x1020701d030050000d88140121041000c0c6150361003007443c1150303002c3c02244c0001e203001b04100700710030303803281e529000b5001242d1804103240060223000100c009180c206402c40c0c5400011444e001d9040303422030341450301044e0340c000c0c4131455226130207590b002e00a16101d4000e100050000c0c624240412040c6e8100e00e0585009604e4192440503d15012400e42c1d09000207003403091954440d5520f1401a108140c1540700107002c0c00c0d00e0042e04e44d41030b0402c1c4030072043c181001c070200d5810300035032071040120003000340410323003907001003003181454141500a107105820000380c2299204c80c00050b175200311614007440750507104216803082c00ca07001c02162403441c4018406517050198200d1800038600540083c0031000c40c10310b601380c546804503030242c03642000d410303502c40140c90080c1c0050154018207200e402003240d100300782c0d403158810300c00f4914030907285c40c513481ca0151800f00a105854003a8101901e07200d010030551504e82807540102c0c0000c030040c03080c9107030109142c0000c0b4040c0c85183e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 694345854 1250 694344604 694344641
    0x618091805071d0f040305270108100b0d050405161e0b16061104050a0612050108120403020d050a02150403060b030604030f050a02070e0c0406020f0304081906110301150201 76
    0x407040028003180030f130311684010640c0b41c9910790f81402e883c6030264120b00340c4c0403490000c6503000d080c52060180812082070325403030b0280d140e24a00b180c41c400540103840381d2003400d10120101c405640c104a802c2030144050300c4480d80c1d060700807811015613421400343c140404181501d40e001c403680707207030003002400280b5040c0150724126102c020429000504100d48529031702102042840844005150050000301020390300d20014080030441000a440303540b40070000244803002240c0a040216126881440c01e8115402c00c20b150007458015603291052165540058850038507696500d03c41030402502c8500c1d40c500380003940c60705203049001e41c01c11000c0c880020341024400410200b0741c1017854650030004012440c00c0042d6020b5288400440f061200c030f40f040c4c2c0c2c0103200b50744050b8240c0d4407042030441001d03582d216920810807140c0c481010315a900b01e42d0042d12440a100b580085011079010070392410581082e00314400c860f032003128001d240c540910520f516016055140c4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 694347104 1250 694345854 694345889
    0xe0705030601174308160302030607050a0207080d0c0c0b0901090311061317010b0a030b0a0914060405160510120c030207170403030908030310061809180507 69
    0x29168500a000d0300c03107120000050b825214800c1c1c030540c41044c0500c252000b2010992110040c060b0548101c60560041ca9140f44031061003003d248140e82c0c02038001d2502d07440d2040300312020342c00341e0f60102c21070082950109201805001300b6401810a035138900c181480c1d0300b13040b1901e042c50351081244210070030449025036000301488003125085030300f04441013500030110790340307100d0811580290f04800300c000c2109440307607030410400303080c0400070805800760100707104015005020260042a2000001e900000b00d60811016540701c0d5140401044001c007442d85802d1040d20202c50130b8000d42c55004c41a020441e900c1c00601301203d902e84105081c81d40980300c0c100c4095507203641c6440e1404000600e000b90100e65482d540011f900c444040740004262468105000441c002100040001480c2d0000010b403401a2502c0c4007601069281000541b51098600544400c016025030001101001441040901c1c002d9001c2040000024a0708030705215040d009003203a000030380d0b84d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 694348354 1250 694347104 694347149
    0x30212030415080601120212040b0a0903050f090343150c0309180f0e0a0803070302130512010509070501050a0905040209030a0f0c241205040f060e0705030601 70
    0xc511451036074245005544c45060040f10859070424900c62924000500c28650285ca5960326203e83e000d803480300002c0d19030807180b0003074903103020f4050000342c014030500c2402c144000c018811400001c045504007080400d400900c118001d000410002d5290541e0303400070300a500452042081d400c00b110242e041840d100c88500001c50700038100640c4014520400d4084c10a40f00507184103211809900b0350818404050b101c101c1100c10030a0800400c4211600005040500f0302d612441d07450a5030f40d8000214000e4019007a120306404182d1790004441d01d13511003403000003504400100d4545071105110746000f9460340014108041000805040381c0e00030402c0003503a0742258090b030388211880001c0d1502103500300c040c0c43c0050400700f1504201e401d40100d400c5844030000e1158080d501290551103181c00549040811107a103400c4190007025400359600134414242c00c24200d95540311041140c480c2319080909030b100c00005e11552500700902070040546240c3c00c1600e5001080 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 694349604 1250 694348354 694348379
    0x18140a0201140703031103340c0213090602031503010b0d12030c17090d09090b180705071a010f0e04021509060f0f0307030b091314250302120304 64
    0x190007502e6010521500701440398000c0c00c00500204c60481d200d08012207040180301041c4a0098041980341d1019260701040079032540400668481e21180c0c5145e030240581042a6202000017550341d101680000b40f441c409140180d00401c0c21001c0c00031030405060848440744c86880c1310381000210341c00000c6482d40c280b12001c50b1880d002c80d0100407078100b66001100c40303162450f0120300c0e00801c2441800002e80d208110429980c280203a903882101c0c0084803d4154107a800032042111300840301d003200d804540107031071031130f026250804907203e01e64054201d29030300e004a00346100400c0002d00b84400235028144500d003148150510703500003018900c0850601c0e101000100316001607958010503103881d40390010003140d03940904240b00c2c03540d0344110703905000300e4640101d8665505041c10400d1003500922070040840708262200d030000c0c200e0205808081c0300301d003a0001900c051480010988410403410f09820b07055204200506184c0303009110f00d41e0091104020031425540c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 694350854 1250 694349604 694349627
    0xf09060c13090501030f051501080a0618050a0317100501020a0210030605130912080402030c1509151e030603060f0c071709040c030e15061318140a0201 67
    0x542541e5900d12415915212035550741c0000c1c100b91500c0000010301003e2202908142d1045090312416007103401da003d0740d43c0080c0503c0009038048200d03080019a02d17031010700750706d16100c2030071101640d40d901c0625010101e0012800500150464445501e5a404003504100c100b4500c812503410640000d585002980c00640314141d0801e106042500aa0008025000c064040300d400d00c041a8500040c000410f01118601c01c1340c001141264803c00480f40510380c010003520400701c0180401515484e4110814581c580402040e8804e50300d070980c5030f0b019804101495154000700b84400103410740d05c3c1d11031000e14410420482c0f1540d0108a9507070265001c0081d80c10703521000b1030b01800c2c0c0583c07400200140a421070010100102c200030300ba589130110350a0240e400c04500c103e00f51184a030000200d5030050880c003140341101d074034459100340040e03c03001d50003506503004000d4800010103581c6420410846500b8403d0005082c400d0301c0000000342000d921640c0004c00003022007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 694352104 1250 694350854 694350871
    0x60306060c081c06032a05090c180a1514030105090103021207050402070602091f0203030a020a020c04140403020d0302071104050a090c030c051018092a05120f0906 72
    0x1407000d40020083c0d82a02c25210365003040006940b00c1c50100064240c000200d41c41100c400902d2101448043c65042502c4010302489550744034005850826044419299000c0a000e89250000e4480c411402e005010349805a50b2042070000041c120a14504510a142d2010001031110b03846548145044948c10384200b00c680101c000700d40d040034001c1d000940c1c0180001500018883d858001d0700014000f15888e4000403040d182d80038045040c01c1107030016802c01d000207404c00f0200d41c0544140c0040b80152a03920b8602c20024088500940e03040c40090b104800740002e2584c1044101c0301403a0030b0504614200e01c5450b880d80800070305640d2442540c44100046007882680c00817008640d100c00c032506042e4482c13a1a030007903109401780c103025011200701e0b01c07001445940204589101c54040365006030a15002d90060400501d20409405a40300582104030200d107000520042c140d842c10b49800400d0103100b942d06c0040d01c200034800c00344041c414103010101d0440e4000c02c41 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 694353354 1250 694352104 694352107
    0x5030f0c0f0409020f0d0e0d02060403030b030c2d0603070543060f02070c090c110f33070804170408070503010c08040c0303051617070c060306060c08 66
    0x4008120a940b150381c000c034003414000302d420541d401c49000540700f8001817403414814514450700307803a80e4038210446240164405004600840c0c000da200180c4803070050300791140d0000040109021000c0c41d441c0d5000304043c0000c01041c0c0c2c440350301080e0301e00800c4441514605110a0040040c0a01c0f4103011540c481107481c5040b0301207002c000a420f51034074070106207000803040706410700f03402c00f01e06540d0325081011000400f059031003215941517100b800c18450300d041c1020040213003204540c082c1808040c1450300c1c410704042080c0f090f000740c4230009000c0300001c408400042200c2508030040c03100c00c044040d01c221840b401c0716500142a01d0100090390366405c4ca201524655008132501c2a0006401705038030502241c60000c1ea038095000b4044000000030403200007000f240d01800c02171071440f050000912840003884400b207510303003907221280191201b9142c90842220300a14074800144141004070000070703040206501d0400300061894254080d01640904000a014400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 694354604 1250 694353354 694353367
    0x2060a0c090e0a0b030c0907090b0706061a0706061202180a061503020a08010f0518090a210e03010c02030f070f06050f06011106041208040807050d08010f0605030f0c 73
    0x45403181c03000402650107070381500d0034101d20b240020003041907810300070b024101c140070f12800c005a4040c09410903a0b01d20001c985000341d15842034200b01400c489407034440b040001e524042a0301500c90192002100d41d6038015490080304a0305203902038801350725410754210150362042c415845280540b05218490b598000e0407100a00c01c44d000070307200da60140140901e0300e030715501904691596495403c1541d0729000310091000b1240720300da40c0000e529041c6012a405064201e4009004408036038180d030490780c90402c010880054603064495015101120a030710070003420050f5800da000300a00c0b48034a000a407240305500c400321200100091043c10080144104d02d001c0e500400d04000604013400f20008000056468600181042005484030303080464000c0c02240d2040688440a00c083c40544910074002d20a4508086c2480010003290052084801c002900e42c1c4a2850350704201d0f04100d0909075030032640810101b4410040d61440040c2000d801c4040b800d000d588540 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 694355854 1250 694354604 694354607
    0x6160e01030522030503100602120702010c0213020706021306050903070e060d020603090c030115060509040906020d0c08180307030804021242090604020d02060f070b090d020a0302060a0c 82
    0x10040c00500e43c018280001620a0607801406140a08211950304a030b081d5150300407a69590129101140e2140401c5800700540c001c005262820344084c0100d5140c0c40f500c0d081c90120303004080b00303480982d000078803940045200b00b501c0018203101e0070034908110144011a0390f442207805440c40d40c01100000c80d805945101c0c0d0510070310b9006100d0ba64903c2c20084450f10755050300d4506000390b0801e0030404958540682c8401a584030355551402d007440c140c1040043c103d000d1707041d0b40717103075081002100101d01070144034954110354591101c01d06041c0c0a543c3c440c200e86e003407244a41c00c1032003800002603102c4091070b00503804440504840080c1d40025050001c0403d1701c6249003049000f100d402180050f04c440146040c88407103003055001d060081c0c4400c4c0841b007202c1582c01150000e0b005242c85040d20301000c0c00503100504007032440d1903200329a032004078141c5140d08613004001c5201810400c1c030710300168900c0a0302e101859550081c5d61000060711402d00a510345402e40b0310107 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 694357104 1250 694355854 694355881
    0x5010333090c0302090c0403030c0816150b010905010302090d030c06020c032106031b0907020c1306030605061c0308090109052d010501050a1406090604140306160e010305 75
    0x103000d403242045003841c1880d10ba140102c580c03008a0080000b00e0004c1d0641d034400094508403509031302c1f080c070318858580c0c4100c4145e014060941c00b40982100c0035000c180103448074070f600d2a1414000803007011800c00034000c4038240d8011410117004105900c01621100c0036101691b40c0360900c4e51081b000d920f0300c01c02074015091510741500c8049411a251a415207413070a40c13a10021111303000ea15514181522440c0c0d8000a401601d41c18126103014101480b0707043d80080240306075025440c141c00014204001c3c4056581100d8851400b4000c1c425103200e0b03075400006c00c4508407004d8a0340d840903c04c00756500d4015050206200001d4107088080d04039001030f980c004180c0303000003040c3c203d800f074101c54908500d04e1510000d0a20450100c1445954113843e00100908940341c6403c5c803009148108a80721900301009000848041e22103001810151648002c507208a109000a25290807001002e070070170800400d81c4090030745c0c4c021107030154024085c42e01240036660214000a50b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 694358354 1250 694357104 694357193
    0x3090f0301060b030f060a0b1206210f0601060908160b03070c080c01020301030b06011106180a05010f020c0d02030315210f0c0a0f141e03030a0302040807050103050103 74
    0x1503c400800c02201014103803200e4072510017100c91031049911420850207038082c40800500224040303003c1042441e10b8805c01120203202c410007144040101072a81c2011008540070071030f627006100500c0896040580c00c80a0000c0b40020719030344d180c0314980003c11502d4860010322400010204034114400c20801c4801030700850201d81d509904403d1034000d52003480140c44036000d15000c41c00c1d075841190000340b81500027004141303540319503036134030704c2400b002c0800150381c8155a55000001c00a0203100600d5100b001c00503100c81c2050030640c2050601d01800003150800c10801c03404901014202c07890090603150003e000c44521034080102c4e0b031201400703005125210905461305d0001841220a507803c0d2a189945682d83e8003c01031407000d0f01443e500c8410780b400540050905089045420b000818440e92154454000c40c2c00e5038885050b6800080e0001b030244075250041140000402c0d003864100169171542d00e50743e2442d00615501c0f000b1000c0001101d880000c0781000808 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 694359604 1250 694358354 694358369
    0xb0a02030405100903060c030e0c09060f0310140f07050d0e16140f06160b220507062601090c0903080406050c19050a030c050f0a0804090b090903090f030106 69
    0x45000070f01005080541c0d5488204d0f40c1c41e00704101c04410503c24082d2410f40310001c0300901c5880c1c58001000241907002305900e03000b082e40a04104955020840c42c0d14443c0724070307000601e1050a00308500c05000040015035070b41814030620048075070050488103e0110320b4800244101e80c42c1c542805d00d0244024800241107140700410500c034000900c1c40d901030101d0740d86408440040c1405141e018100c84008081c03010388800707000ca4a40d00c0403551042e14141010908414520541c03038081c1c207204103940c01d1b400400140403007034001c89180c0540d49101d0064030308040683d000c210110050042c8d40401d910389050050587c06503008074013440d031100801751155240c540050403030700074040410710b03481003002a9100a4000076030b00907664004000e80031203c00307900d00b542c909074410001c8070b040c45190064000b03420309014007070000b440384001594440c90044d512054442295015214110110510a40c8107000048401c4c201c8213a46c4151619900c01c000b9005101c1c55021340c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 694360854 1250 694359604 694359619
    0x161704030602030a0c030e0c0d060204030c0f06080906061e041409031c02040b07170c03030c13060f020d0f0509030f280b010b160609061a010512010b0a02030405 71
    0x108072a03078000e10320402943d0010000d19015184c12000e5078850326031118580c1000b0000707104c905080c2203680d8510b004080240c94a680ca50b284082c1c940d040d4030428499624410a0011175480314a440e00008070074012b1100e400c2040004041c4403141c004210032090141810a581d102c50300030101010541c030340205145003d00c41c0c6901c075401202902040c11032400c44c40f80c42e645520070369054450b8003d1107401c0c40040d6071003801d40c180309400326000100c24404480d0f10541040218810340a2550036a00c03984003602d100c1d0321403001e40266081c4611140e02a0703a0542c0003070814284031a91402c4004032000d1901074640e4070410044540600841000071720040c1d000501081c0c05000308400c8594101003520700004106100004002211a000401140307090b00090003c001c01c141e440030756a8140c5c0c2e6a10102c0390900002c58509448400810790000746500b4849101c200f03080a40c64060300c070000d030904001c14015401620760100b4090f4150723100300180c401030000500500e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 694362104 1250 694360854 694360859
    0xb153709081006030803060618060418061a0d0b01031d0606091f0b1305060a0c020a06030209010e090411030304030507080d0306031a090c090a290303161704 69
    0x500c030000602803541d8600c501100384440811511903402140d800040a6045849510800c01c3e43c0d40304251101d140713405440481d14039515440104000c21220104039001d8078400c550500343c980c944d2048050309a403031032901d2202c0510041300d13905501c00360700140d407404d800010f8009202c4111003252078480d0381803141c2281d00001d0758500801c801c0300c4000096941c00101040200c510f0310849042810040401c84a91100d02401d04041003160000b1240d07100e5001c24181d8000c000d00d071700020340070036000040d401c1920303c0034042c1c280740c90b080d45082c01c000c0020b003803040041c481c0707409901c5100c00201804400c2c050010000c00c000c1c140c1c0d940302ea5905080d03a0b03c00890042c5039160260005080b81d07240a8070410003242ea00820980c4c3d40d0504d00127680303201100031701c64007040c0520a03000c8600d5948049151080d4a00301c000070f401746203401c00740607420391482d10380100031410b2415500ca41d00081580c0c1d406d194580800000242c51810b07505400c0c20020000e80e4034000b0a01 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 694363354 1250 694362104 694362107
    0x70201090b0a0b1c08040b0a0c02120c0603011a040b07110909010e100915050a0e0d181401110a03021005150a030611040b0d0204090b1537 61
    0x2024400e00940101000c0d0300ca41900310229403110910680c400c0441106058130003212000c0c1d000d4038024051182456a01d40d100000790748082405800114960704820842c81c001c0b4000145800307000050030a0030700440441c000d0320041c000ca0350007548014021400314855021030f0064213091204544450403840d089440110901d01c0a110381034000001d81d003604140b103820307200c0000400030510400a030320171200a01c003039402620807031407070300c01001882c4c62070142c10f000744500140059031981c41c1b80903a084c0109002c5010400007030303da00c11401075442c4202030507202898944017000160030010707951540e24050f038040324011200600241900446c00e0313007400350400c07401d000c550f036032664143c84c00310078802d0345d03900849002c82400468031030b5105500c1d11000407119803405440351608849a00030b4805c22005036000601031000101a0085000c000d400351680c4801d07a00c100e00409680c0511401c0401c409030410b40350072003680f1100600307201d401000310f481103194000f40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 694364604 1250 694363354 694363361
    0x703060614120604031e0c06050f1b0f1b07050901030b090c0609210705121c0309050d1409040509030304060b01020609250b030c0309010f06050906060706090803070201 74
    0x4a0601c00e0280301d0b002101414007180c01e510039941995480010f0019078402440320b100844403104002100868100140d203521409000e00d0316003251000501e031280c101840c00301c0c0c10900b41e51728070b0b0600c100920f281002c016078940721381c0c3c90061140c102070107918034905552540b0503584020400c0000040c0910100c0e041d0054256078241c400712034980060100610071000002e401c1045054074201d0700385103152283c00440c010782600c000d95507620000700c2040c0c443c10f6842850f08250700900102110700e0718401210410300f0248166203494440030b4484151902040502441544503c0b400d1031460448406200040081000d0300741440b04540d01d4008a030115005441e00f5039182d825030000542c9031240f02410300500760b10410700100610404098909080407206510116007016046c2c0a54802c1d200d240c469622443d010b90514207499403503035590b0142d4640402803010f52035115510780e020005a03042a500c05840c642100140000710340601811004020300003070503410340 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 694365854 1250 694364604 694364639
    0x60f0e12070b0d1b050301090519050a0b1201050f0408030c0d020d0c020c032109120f010902010207060908030301091d0d122003040b18030309060618100e0907030606 73
    0x3604100144c400c16000c40381c0d4000d1400711020a00c1800104441d91082e008241c0c030140c1c00007610105003042101c901610015920045a16111080c50381300c6d003841d00484012b040010000c0c0a10b041201240355100f0018201400c1a240000010150f01e030f0b0a086032100d805907001150740b0461340701c07004000e0a20101140042c060740c250322400b40703400a00607030403c0300030503100699050900784c9580b0358001820a030700400c801d000c0054014050142176043d00c240000400c1c500c409100080c1881e4594000d4424040050014407003d04008142e07415228800f0340040c1d20300c101e480307509030551810901c00c1e4600c6068003080b0500e034408015458540c4000e4140640303088104511012a91038620b540006800d00006001c203848030084c9400041e00300442007104034489040d411a40100c1c1d900d409036100d0420700c102d03418800624500030205002500c040c0c14422001603021a1501c110001690110003185c2d0083c0300b48510401140d00001c20808156210500c203850710801 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 694367104 1250 694365854 694365877
    0x3100e13051c111515012c03060601050a080f0402040b2d27340938040801020406030609050105060901090b0d020729090106060f0e12070b 61
    0x942080c4410fa0700040e1507200a034610210185a0f540010b99180ca0303000905050400c1400102c000000c1c40712a1a42c100480f80c5081840070b9011409051a0850182c0071504202003041095580e6510960351500010010031b684500e440b54000500a042075160301580078051590701040c2900508444003898104602c60b0304110000080206410421003088406031060003954040301c41946090340c0837504050900307000100c0c1000b142c4040e03555a0b1000e01c800700040040c400c0381c01550700002446e80441d5128151410204d4072402c1c100e8001d08080f50800c0b602c0e030006c00e104102610007509c0e030341c0021034840395141801809001c0c14410054031501d460004100d505101c421540140e4040c0c43c0c0101803890024118010350106401e55000e82e82032040c078001131041c1d0107001415600b0707080051501143e090750f11448030007501c407801e030f0383c50310404015041e00500628000c207064188000550301020108100e5405190503034024090020082501c80200e0058181000b20 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 694368354 1250 694367104 694367117
    0x20a0305010f080a0f0c2c010803040f0918080c0703021c02101b0f030503150d11060d0e0609061e011809140609010c0e0603100e13051c 60
    0x891602c40325107030040c014800c182c1c12902200e008103802c609080d829500c03403010703040c001e40e50300d415401c038819a20703094101500c0300e4880f00740c5224402200d80540001c40245252900d4801c0c0a000040988607a44845032038080b107954003035007043c000f070303071503810a41041d0745940c2110785a4440c56207000491046211205004001c01845135440080d64041c002040081d1800c1040d20340c444106441c200c0075590903201400584413940690601d44a40c94080e128100040240890119a685123000d9450b07001340001045c980008207008a800f0f680103030f540c001d191016030291000c1c8550a020380310f40810302c41c0003000024150f10a84030040c82101d002c2c500341b2140040e4800307200f50703981d400c008401d805141e031590b808408898840c1c200c003520310120420250a045040315000c059075560003100000340c0d00000d4182107154210b6000e031640c034000080b964281c406015104612744000001458030891000c031130052078000b02118641f5401c004141c1581c4910400786001861 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 694369604 1250 694368354 694368359
    0x90310021e07150203100f03030f09060201020c0c0609030316080c06091b09060d06050f061f02060415091b060e0a080c0f130f0204051009061202091f0201020a030501 73
    0x800000c1e40e8020343c1c401c040440c0c040f15a5503100203900040d2070742e01d400070071038000a5001c20004442c80150301c261104581940e5034080503041050980c071005c25640100515a0450306c0800e810410580c100c40d2380d0348038030b07094000c24514020004c042020124402030300c400d000b0180003030440d2081030380440c1c00c50303078a581c1c4080d10f411307c2e407400681400b00e01906070410b15254000c240c2c0240054203c5590034481c1e180da005451041e44c60940c0c4507003810601000e0300300702e004101e131001500300c84803400101510095403000010070180032002140c00d03080403060580c00000410b600a04c019800e1002141c0605034101d45215000100d43e01c1503a400f070904102410104480b90900603000300c3c06042d052000b0a18280350944c2d002044040a00000d081c9100302c410100c0440030050b01c603402d00f0244483c607a0681c07014400d01452080401c1000d620410110403e42d18040143c1c50f4005c00d00820140740500c5440c0b031a0316922103415003165070541c040c015000031b5950a00003a40d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 694370854 1250 694369604 694369657
    0x813060302040e22060c020a06050c0d0605030f0d03150504110a030f06050d120212030702010b3a0c030b044b050f07080a0b01060207230609031002 65
    0x404c0e03030f4070020b800c074007040001291850b030005c8108009401600d24280c5640c0e100401c480017203031002e42120300481c00401d0071a441c031031280540008c0c1c0090100c00d0034a9a01d503600e9410640150802d0349500f07140c081c2e021442c0b0391200503c0d02a0061024183c0c8442c11545500604d0101c00001d2408900b100400103500841c000c171100985640c3e001d440503100d4181101035038030000e0642c4035030502c4401084004d80103520882180e80006544c180c803c0c1007001000d54100948000150031505c50002a2010041500d00c41c0029010390100f00c039141421113403000b40d0001c1d14251141d002c020034031500001d0078090026181c02c91546800505500c403041a4000c1d1110103000b5511005850401c200c0349140c155024000b1a0342c24440060428503017120340d0400b4690b600b2100c086020400e820704a2400f41640740082c0a1060615000c003c101800391021400308501c4c04150b00181c541000300c0b1204800a02035400140440c000302d130103903202080c80444902301e240a40100c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 694372104 1250 694370854 694370881
    0x220b030103051507050703050306180103140d08040b0f0402030a08030405030d051303020604060b0a05190306110c1203190e0703020f0109080a080d33230d0813060302040e 75
    0x284ca4988503103040035000c0e241210950801403002d90442c02041800c1c00031900c00d9081402144540e07040f030f00743e00308071680c3c50400555203041c10a002008050000144040e81616072000e201e850950f2503a40320f000181c5094400680508041c0d0300105000601c440440141500100c22909214540324181150040b6803031280160041c0c104d800418002034058001542507200105003045285d100d0000940c901c0040d18a42a01000b04d4002c104101c032030301541201c0c15070507d030a41409056001c00347c4599001c500e125011800000003184d03245d040d406080f44002041081003149020700780c050740c403007042c00140e1080428040b81d004035807003014058180c8100138081d00c007080142e80c5400007900400c62a14036281c42e40440f0618032003080702038101c03940d080e07001544e120b2044e04800c1841002c1d0402864080d40c288450600a405032581d4042d00090b149082c241409042419046c0503c6161612a03050390038005207555041d0094030070784408090381c0c1a503440d83c56810400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 694373354 1250 694372104 694372111
    0x13210c1704053a0f140f0f010b040b0609130e03130602010914030309071208040e04121106040c030b310c170d052107081e0c0f220b0301030515 63
    0x10000015001000281e0407041040d901c05d0000c00c803a030741c0c442452940e050001c00c2e00041050ba65a0b907400003d468640a544000f24080e21070501e09103a600c04110028070b00726403282041d03103a03414449030100400441d4025000c10a068140a44400c00240079240347c5806507407185003040c0c1507191039004800c0700e0140d0280c2004203c4540f4160f42001d81b06071225090300c103e8014040040c1c1111900050b80c49a0310400074400c01d010604070107000c41c0c1066a00000d103500c07141c204800100840718078003e803504030b418403607503030303902c84101c1600060302042e156040801001407100b24404003040e13128a12640300400714a0701c0c1e49a503c03094407145001e0441d0348c09181070350070f940d000b0030003080d4445000300820354081e84000d400104110964180c030000e540141080075800d0329000c81d004048051007032941a041111080329240920b0000741e90821002030b05032317560f54116001c040382c084540c170b55900700d030f56840c0d00c0c98568009100a50b881e004100e004008024111207880c0f0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 694374604 1250 694373354 694373363
    0x50f150616170309070e150a05010e060c010e0106050f030606100f090f060504060f11060403120e060103060902030106080d0906080a0204080613210c1704053a 70
    0x10501000644003071504150000d0b100c801042031040c81c4000c07054000d51040c0b206400070075009140c0208a5000c1c1001419106c0310107010141c3d0361180c0c0c41042090071100240f03032402d0304a0301d03940000d5091007900b207030589a610b01964070010a406410020480707038100c0307440c00710103c00000d054480724101d0300303541d000898826041086e4010352440d1450b41040c580300c441c854840306101410710b0b6a404c07520104402040030800d00d42e0140d51034a0301001490545660200e0355405a903900d00076100605100f4450040000001d150b41320341c8940d441007040f2041544e483c2480b0f0001c1094001c140c0c00b035401c082c1b000c16a22000120002c1406c060381c2e070165240d1501d04110f441a4014240154141e000c02000550701030401407140140d01d40006500b0755061840e242c16600038133113420f100c007161b0f0440400ca50380c10080d40c1858a030031203541d8502407000c01911451744241c3d004190f100740103441240c0000300170f00c0c1100c0720416400344079203409000c6100c1d4050141c02d6074000c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 694375854 1250 694374604 694374607
    0x80a150b0703140703020610050d080316030b03160906140d42050109060f0513140f040501061a091201200c01110412120e0405010306050f1506 63
    0x8410040380004001440c00307894a4450540410441c01c03595201002c15401a40003805003d0001511400301340185412a6900000740503684c1d100b02d01e001c005e2508540c041c200c580d070080d641c005d0300a40a1524001c05491000300c00031180c1140c13000d18091200100d180c50130201d80366881d0141212510340042950103641000d40d107016181c100da525640081c10840c80c92102030000c102100f4401c6c000201c8281034182c1520130307404548050b0f11007e2501d041803000c00000e04100311000035500d042d203c00d0092414015610050901d004001c4454448002000340c200364802078240554030807002400381a40c2d80c05007400e80c03034001d50401054013041020004901c0e111842c0242a050900041400d000d1310404046240d180300341c00741c08801c0015000d200342d00078842c81090b00024800300b401c250610f140e040b51901581070082004410b010701d08851409801e1850055000410a00096851b454014080d0a00f5148640b44003044008522180d00040503980300b40c00c05030019 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 694377104 1250 694375854 694375859
    0xa091e060909020f1e0d030305060108090601030b011203110d0305010f0b1201050f0d021002030d0605040e190510050702010c030b041a0f13020310030c1212050a1b0302010b01080a15 80
    0x1250111000d0305ca6400b182480340c1200680e140c820740d1b900403034000d0320001564601500054540b04000b0300c141c0c007a0b00083c0051000821040515054928210f40c100100c1c1841ca8103454500d031552090321203101d03000305a40c803c0e5154000d1030580c0d50003803500d58403666a030890481c42c092510303000440c46403540117100300d00304180c440490344c0004022102211641c2c01141c0000c4844084000680001031088014540c0340204001007006079010001741030310801203a1074070200c84401308040c021284082c01d01c90100f0024006e8010312000300610704048801900070500c0c03110343d501180c148a44080c0e549082d2142c1071a441d514450000700c005100104140c130040b501010340d2040383d107402455080346900c051b611411052844c140c04500f582003501440707085074801503130011400c880200068800c04000d4800449050483e11080e02a1081c0c0d850303649038260b12146000b0f03d280400749581500b041d6404034013030321441101c1d00c940e80000300b5188140708149034145c01e00c508 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 694378354 1250 694377104 694377109
    0x90510080c0f22090605030f0316030306030506010f030302070b0406020c360612120a0309240f0e010516080a091e031202090907030504020a091e060909020f 69
    0x20000200d40e9a060707403508001403e0b0540046141d80030014950394814280318062031441280040d01e01100148242514601c2d940c5eaa4070070315000e01c0711261140c00f0001010b000340c004201440d03005054a559684824001e010041e80c0d200a800501c0790450004102c00e805045500366001e0b030703018101001e2200144000003401e02d0022440c038010310900b40c07900340d00d0508542c810982c107511030002d0425a04004451001c0c001ca480c0c140c200c41c61b0304104082c14402c4a601c810386081c0030031040c0c40781c1085184035a002ca0101e90b0702c02200d000c0103410081da88605500c81100c2c1041002080c030304100d900700da0302241c1030308080011000740303604030740941c041c00d40c40b5606650101d01c3c410349941d01c0c0c108004c0030480790180003000302500d0416270480b420f100031050b000c0d0114184009107000441b4688080c1c20f150505540302c0c01b1409546070091440c018041882c014004c0f1a41400a1281c4031400410324104520304480071800080da40501001d107a0001c043c248424540400c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 694379604 1250 694378354 694378357
    0x180303090e071211130807050a03020123160614040b06010507060e0a03020313090b060412020111010c020309030c061e090a0f090b130203040c0e09030c01020415090510080c 76
    0x9001803118121481c00d596400e40103190313411040300715080e1170761403182d03041032100c0380e0340c03c024041d41280782c042c406074582c1c011380c00c00c4030340902c0e00b0b0040c9100314848410b0b5100c111500e021102c0005102c280c1c2c00740c102c40740560750f840344008019000009101c01c10352802690001c140c080c084020601546c4640003414195004050002e00307204100409450602d55900071009a00003140c109000b00d11802840001c000304003051140780ba0500014926101f28026413590303008224a26080d0f92142502202403a51100200802c2071400350103903994000528047c424030a046103100a410480182c4948865030180080305008110040200c0e4218505a03034000418003c0011100c03d030542d400018440c110002032a0249142403004410b56803c2c2000024010414000000c0c041100c5d202298030841c190748154071420420381c110311810900c80000e600100e40480e2501160144c02260b050030b0310703943c1e9825a0391040c0201d8081d6411000302183d181e00008492050840 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 694380854 1250 694379604 694379611
    0x14010b0d08032e090e0f07150e0603100e0105030a0506240a0e09070909030f0e151b0d032c030d051e061207090b130219180303090e 58
    0x2811a0031814000d054004820700f41076200c4107001c1d90342010048128188a50001c1c2c0300307180d010704045c4c0381c0800e516940b40c151313104141241c120f40750b59001840c401d080740d82c1c0030706004040503581e00301852000141841800b6032403184800c1000083e141c50005050030146910002812036607844140d900c5000605440e045100410420003241c1d035034848012270b024240064429085041607a5000c3c905035003074000e00c104500e000c0b141c60200e60000801d03046003c451034520b070180e500c140881d120f00058080c550203000007249890034031141820151481d03003140c2c11038120a924100450030344041038004c8010200c0022482004082c0f032010a40ca024108116071a00d580c2080c400200c450455611840c800c100c11610140304400000c00d0304840c045030b03010001d070b01e40c10b0026185c0072180710300b1043d140d0301ca10f0300e1069180c26002c0d0612402d1240c0854940c8060100c50000c102292000c00004205002290907045070700120000e481d016518286481d05004c031102003001c0c040d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 694382104 1250 694380854 694380871
    0xe0f04050a1d060a05012c07090503060a0b040513080415020c0306191a06180f0d03031418060c160b01030507050a050303121b0f0d0914010b0d0803 65
    0x601d05110007029441100414200b0840200070314900710480408903001138002c110440f10301602d03d89105c203000014000b448039207619204076242c0c0395082c0c54100c002e40c001600750003410100400c0310201e92010121420944051000c1d0b580c00c040c0e400c40804149000b416007034140410b20002c1742c11a180300c0c4050807401100c9440c500b2400003440c200d0102c0700ea25140fa10000c10300202c80b07683c0144410002030500d5100600d403000001001c5002e58803503240011317044400d04120b940d490907010100c210250030710403c02d5041c00d0040280c02c208000004400b460307004286c2840d010f600809540c03000c10003604590319105c112860a60020042c0c2c00c00c25002e00307400c000700d040607c055000f18800c2005024561900041c800092902e501c0103120790014003907003030b0442c1d00100c2260b002041031540c46844e04106007000b550300a25059000c0b155000c1403403d00c2d10402d500c4001c10314001c60301580c502845c0c0040d2400c0e142803000298121010b00c0f4480e0001e00200061500284034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 694383354 1250 694382104 694382111
    0x150406030e19060b28050f120a032304080607090e0403051207121a10030b030a0b062202040612020703020d1d03010f050411061615020d020307020c040c0e0f04050a 72
    0x180003044403032543c17100700c0c001e0024218020459890701c100d44481b01001661044518040003e00c90384442c81c624000c0c0c20b1040c905a60410720100c010251950742d00b07501c5090300e036a2140200c0d580e41204688000c04940d0b070b080007003040850748507002d00c584e61690350170b850803038040d00d40c000c040300140940081c0b2001c0a000e2890080e0b900558000840e12254072140306070480800600064994041e400e05107062000b001c40e40707010a41d00d5000b03801c400100c03101d413165804540590800740040c02c441c010310200080c50010394000f003040b228030340d4074400380044901e10a001c0341f02e9104024050ba01030410600124010856414261113540c244c4d40d200c0d283c01c000c40d0944040300701002c0d0985e038410400c420002d031401e10121207541034801ca410b0000f803c1007142c050380f5809000d00b0003001c504408802d0b003042c0e01182e0414039003010541d26418080c1e8003a65501c020b044042c808da082400385012188035003c80654510020100c10300446004240001044058040390301d00c0e86 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 694384604 1250 694383354 694383379
    0xc03211e01060c0614070e0f010e0d0602030907050d080c1c170907080304120501180f0b090316060621150f0f0e0d080108070305060105040c050702150406030e19060b 73
    0x1c0c1d4800611a56190700c42038447d603000803c01481400485080f4144042e41440b080d158484070702ca44c0a0304c1c2e103d040140d40f0740f41c4003e014544480340d441710b54005d03e10410350381084a0680031f45060581c28045491031801410580c00500b4101c01500002d00c03007120082c40c07404a0381e03165030000d441105654080f07403621906429503005802901da01c5440e03d4100381049824810882000c20010000c118000d03640c1d5409649c02d004000609164143c902060b8040020b2044030b5224041c503c0e90113051070180383c01005007800d486400400d0b65100c4e062542c1a080114000032035174041030268203281c02c0f003455401440e2480c0444841030b0f9421800021f4034440c825035200c3c0300c584009014117280080010010300d0140c00126650b003007400100002280001c100e030640d84205d42c0820700c0e8400c0002100c1d01e029050000c0e41c0429a50301320816104068014410354950795400c1c050f45908003442c0307a5502e5032012403851150701c03080041c04182e00d680003921044004001404104 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 694385854 1250 694384604 694384631
    0x2010c021503150f060d090302150f042d03081504020c0115061b0204020d020c011514040204030f0b0601050c0607030c0f210e030c03211e01060c06 65
    0x585059841c281000000602000103070f941000d00d02d86600322400c4443d1244500410070900401c2a4802159120740c508000c150080c4085503000d80d01101251152030980c0121852030400c0c0c80a840e442c0c10656090081c0c00b0f614901c4404840c91310030240000301030b5500301c0d5130384401030099550144503403055411360f03128002401950140f100103d02c111042042280709401a07108000303104c5041142243c10000c0c1d20b280c11041d80450740161a9880d003603202010b842103514801141d403070403080c1c480740a01c902d074007400e88800710510700700d080d409030a0204911403400050000d6000c120008001030100c00100e50007041031500398185000075079458602074085d03072610003090301c0324654005c2d00c1d4270600d00320319260300e85413510491207004844001c0700d031a000428006911034030062500c5c2010011288148503403c2107940e80c3c110341218800100703c1a41444080c4e65480200b181d0465a0300341c00b60a40c040c8064003001d07460504255001000c080f41220b0198403008504983c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 694387104 1250 694385854 694385869
    0x308240d02031c050306040507021f050c07060204031208010609050f240433091205150903220f0512070e0106320a2105270102030108061302010c02 65
    0x280b4292200c9171203080100400c0281c2d08002c0a04007107602860440c88005082c068061200e40d0a83d030004050b19003d401d1401d910a9001c041d2829000140010801542600c00d0b810884039a882034142d90701c41c402281c26448070b110303450b4011a9480c800b0080d01c0e242c48089107040b201045003940c503030b40d04400d03a20303a005980314500e0401d0800e114464035120024840c036540d83c1c50f8200501151240c406000c16026014003452400403000c24020060208018000c103a8480703a0b2142c07503d4000e0140da601d070b00c400c281c2d0344020081d810702480341002c01d00c081c1c152100283c03890102401c003801d004100c0800c4210340220311800078001345607a501143c0c580680803580e54580e550a062010f121100000504003901203103048009100007085070a8500320203c9241c43c542c43c4e403c0c40c40d188a500492003c1050b074618000a0101c1180341a400e91401c1d552010000c03188500036110b00e00300c1c0401d1007503071565080b007030020b030b42c2007100110020b04901c1410f0440401c1591b8000c03c492 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 694388354 1250 694387104 694387153
    0xe1e0d14030909181e031605010e0c0102010b03030406030209011407030c02091620010f02030a091101020708300a0f020705030c060723100204030308240d0203 70
    0x554200003045005424580d10b4507078044c800340c103030000404207624000d0303403941074010040b580f170304122803072100d81006d004a600c2e8515291314024000c0e810b0070814000c00159036081d0040c480c00b1020445940107000f84450504001c025504152420009501945c44400e03001d041000018030b100b030441e04400079000c00f5000c0d5480d80d40c010a0b61040c041d0fa02c80251480150705071180e17846804a030302016240d012030708a052110514200d0403640d01410814072001e08007070000c4200701c654101503219000c1d80380185540c4801440040c016600c0703040c070b400794130280e801000e040c03210350341c1e82102c0f00300700300948102c03241c58034002c42c01700b0300e541000701c2942c002220740d00b450030856070400011000d49000c17400303084a03841d00c0d00021010310580f0f2006204e90105c0b0580d040e12500022400003c1003408240d44903c90900030f800025409400124080f816000c082010120080050f15808210104407403a08219004010200d4281a4100d034140701e191f0fa81455040d201818101 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 694389604 1250 694388354 694388393
    0x10e06031f020901030c0302161106090307080a0218010f09090c090204080d1101110703080603010f09081b0c060a1206150c060b040504050a021009150c060c0e1e0d 72
    0x840354020340004046c1c5d40d041443d2010140107002c0c100344025100c8000c9041c1da0701a100e800b8000e0340d000803072598016070214590500806800044081003c82c00c1001c0034400c4a8080d4580201d1444901000d0280108244c0416200003488103034066803084441070b014802c00c084242d034800b0380780c080c2d9003d03800806143e080940030020341900825001c4143c0c00c400001c1c0010741c241c00000b0842d000d04036016080001c100042111600c081d0311180142002080520104051703003010003c961000007490014209a01240c1c07400720040707800310b60b54030001e0140b8a40402800222065034003c5040c56150b503540c90002900200c82c1c48000d140503d540b20620000d8482c14a03400b113402e5510802d001d503080800300800248081100002c40741e0484403001c00c0c2250500c1202c00386182c0d00004201c4602c20050700003e60040460080c0c01d00c220703000e000e90b000c8030b8000c5440c000382c044010307081321a8201010380c64082c50584149081c000d0325100e850141d50b00c50b139420900d1908541c2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 694390854 1250 694389604 694389607
    0x30e04020d020a030c03140604110408060f180313032a060305010501020c03070308030403030230060a140d03030c030b040504060204090c0c03080a020a03020d0e06060301150806010e06031f02 84
    0x1456054054007420405c0c50404014070010075200403425000180003500c07035a95900e196000b80080300c240e030301802c0384404841091030310600d44601c1c0303501505c44000c601c141e203000e0007045600204884c40d1038108034008c5402072441e41c6d48080340d14103a60180f60428041c2a001c140c4000021841c020b1017150f030045503e5241c1000a4100f84100c41094026001003200b400030607820b9048070303000380d030501d4016950610700f80280f24009000200c07901c4242c0c040d044ca4400703245181d104d4010310b001c0b111601c100ea603030078020500082c0d01c48a150002c4c3c1035003904000c00e000c2c0c0d001b500d014549040228109104000140c00c480b070449040b00d4055000c42c0506c00540350b88a6204402c526050924851602d510080c050300c0d00241300c14400c0341c001440c031030100e2081c2c040d6403102140f4030341407001d0980040c9160711810125800da0003036180c10442c0c000c030210000c807801207862800c040c18a82e400c0080c0c050510b48018103d0342c162080103520f103480e4071000040500e080d0b9519006 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 694392104 1250 694390854 694390867
    0x210216260a0c24150f1a0d02131d0f090a0b070203090a0602070306050c09030a260d0506040c050f070605101509080c0f1309052b020c04050c0304020d030e04020d02 72
    0x6251103109401c40b00340d20800400511007110204540c15011b480300034000e132900000b41d1041c01903c61440e010746407100e0500c00068502100b0b6600032051f50301881a10382d0b075510320003900c6d0284100c2e0301c141c0691002c0303007503c08514102d640b20b800c2805441641e250204001c0864960091a03005000580c454202003050180a1191076040440c03d41040d281000c0480001e40d85c400c00e00c1302404c000d5501c903000c00b102c402e0419015030300d246e105205803036805080d0f00310700401003241c980b4045c9080c0705110f1502c5106204464140200518403418941e9a0f2521401008001d10981000c0c035140c2e00481e00f12035001d003816070780042c0d42e0b40801072401d0406003801c20441d070107014010356035056418900e0781d484501c410188804900000e074040181001c40c5000f4024103119804a02000007501c800c107a150b010205101c180c08580114006605200845e07000b101c80c0030f1064410b00c0800c005151404040d00e50034003a2403d0240207901500180032684107220480c2000d42c0040d44 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 694393354 1250 694392104 694392131
    0xb1c0602030a0917040e1e0c0d0e19030e0f032d010501030605040c060f0e0909010209190f140f040e030403061e0b03060610210216260a0c24 62
    0x751f03a1000359003213142c03605520b8503698120464042d0189617601000310300c62040c000036030301012440404c84110380c240d8140a600c3c20710320800110940000d1202c18039100726090840710810035441c003800820281c4203520300640290711880742104040810003245691180900606001c2d50103941c000885042603d0003181007007480e400402840030412800e40030360307080301c2e0304180ca22003910025040d0703031440813250082c410704134015480000d03023070745903d20a03011601da019104884c05052030992504c0a039850f04080c1180568050081044030040e4101508000032080c011802c076400c0c079440781c2da0f0300140c4000c810541e6a410100c21801c0401d044d60140101428054019040d2400d101011807110b00101c4c00c03590611110700400a00c5058007965044009600d081c00c40d210a1b0903050400c904040190968130b03008000c130081e0325480c400166004904141d609540340604c0d0340d80964843c421000195201e010743c0421448447c1016030ba01c9091800980000300400407000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 694394604 1250 694393354 694393379
    0x70305010806070504030830070917060103020607031701060c02150f0d09170d0f05010906121101030204090f02070308150f0d020f0301060303080a0b1c0602030a091704 74
    0x400000740d4000c1d414008503642010440b003e5a03000180f9030b540c1c800301c81012458641003030030f900211a540505180242101c4101030060141d07a071400304856036061002d450455045c2c03035140c641c100600400042c58500020701c81c0c18882e0804545500801c0000312160313100b41d10032070100d00c000b0070003400c601d800d02d810400d555001026034140301240001d400c5c54090059011a255030f02c0714028244040d61040c0d2680c50300207040d40307079035401d494080d00c0070b0480b030241200701074249800442d840c9a113002d54410f480307030003480f10300c4801c04d43c032181640d81e051021b85050503420040800c6188490042e40d0342c202e1180000350360b900c0240b4009001d201d004064010407100201040390317594441440d13981d460000c0318089010030190002841548a031948198558a407001c000209600001c6642c0701d0b61860078200101401c4000344031020a003003c1c01501c02107280c158400058070b0380d0140d50401540c40e800141d18660783c1e100e00011001140d14413031004080350400100d0042030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 694395854 1250 694394604 694394609
    0xd02010f0c09050906032b090e040803070c11030118031205010f0909020a080a030c210c12050c12180d08070209063d0c0c09050606070b0f07030501 65
    0x50040007004030018005140000c60b000d0548030f2080b0703d010660f180d900300700007074141c10407840800350404052801c61040c04071000407000b0480208000503200304440e6101d1180b82c01c440003c0c036590759648103e900030740f00d41781110010114007100060f902d00340701d07031082c0d00000d40031251010818100945140c031510b4070104114285070040c400d90a8030449803080ba01ca0010106415107144009529946650000c030b4491280c40008000d06a1126200542c00e0140c0901088000610008840c68580ca18401c020582c000380c80400141d4000400342c0074484c5207015424000c11425141c2400150206d0141070306c404620a403480a40300c003d440f1a003000c8803006044081c0c0da592901034044c04034041c0c4210136880000306581c44c2c040030800c4284846403249504409030762070209403030303c1070301415007002e00f0f2841040e49030007004141c0c592504842805201882c12900401805005040c50b13040724007403201d040014208241c0e030703000b5a00300040c40403d140c102c100908844050303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 694397104 1250 694395854 694395881
    0x903071209240c060b040209060706060e090706021f2d050105010302042904210606060f120c020c0a060905031c050a2a0b04061d0705210d020d0201 65
    0x500214100c1da0800740508420790700103004116500300c05c0014000780a4601c01701d420510014042c01002156442a01504c034804008500c0740c40c0e01c040d0f159030f0300079405a500540e002d5042c4140706c0d200c01d204a18001e41000d070215405036940700c5100d0005084148041001c4002c0c21101451801d002d03843c0904000c1c40e0443c145450040301400c1e402c089101c800002801740b40f42000e4101540849000d4414111a09900340d00203105680544460a05445240c070740440440d29030720071181d28903080d02c203039120742c3c0c920b0305802150020880c45034600700f0752050400b18042c6413a030020040081c441521218a020328001c01e1504001c1d11050103e0b000004c0202c0f10003036504101135959034060351403d030a03440091424209241c3c900007030409a450701c2d5250f10200b100304031045203ea48910000d1103203081c3c03804680c0170341c5030222210010780c00c008014405810302e01c03890320031505040300e42d02031509420009420203503920b40307440060f00003a03020320a480d02400794030201d0285 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 694398354 1250 694397104 694397159
    0x20105060f131d0d050c07090c2a0203161a040b030c0a020a1703070e04090209070e030c12010b030f030a2a0c0e01051806030d080903071209 62
    0x45800186038081101d91104181e0f945003400c0303604041030440880d0920501007252034801d901000a441c5400003444190544200708021482c42c0030f600941480d008030f40c4800c14484e4020355141c01001c90349000b801d00341882001c00e400742e9400c0040c04501c100044118203d01c1c00d18500d404c0310440e0300851a2018020002001802c60020031650300000700c801c203540b20030f0304840483c10324001d90030141c2074403035296205800640c107034010340c040c49290f26613140c4103404c1d000b880306440c0712100281d8009107000004c0c0c03441d4010320540c004814004c003a50003280e40d5100041c8010008009413210303a40d00d034650605804d0802c094230612426100960800340d000c07200504c045c07010a5401d041c110f02c10003c0251405690341c81a0b040d40c0040841070f903d0716101d002c3c0c900c840034482d00d44908403150042d59942a0b041e07000c0c4c09075601034003030980155100c00030780d048034021344521400e1104000310804518107601c500f058840680d0342e03139642442c00c40c0c50414002015001d0340c00c40c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 694399604 1250 694398354 694398379
    0x10e1501020718021b030301080616020f1b031009080403020306181c1b12020d090b0d09210915080601021b06040f0e01050307080105190504050c1f02010506 69
    0x3140c0b6601100280c1c3e080015035104103446190b00c8400c0341582005961001000108800002007100d510460102180d4034a00c0402c5c1400c0780c1d0b440039406030f4009900020f42c580300d0060f0b16540b038815104007070122100b0342d40c0829404200e446c120b00943d15014041018400c6140610407a90001c2582d50001d4600d0380280025440348120454415800d00441d4514682c80c01100c211a81d000c0010008090070098102a4900044000f40358018040c3d60304421b0b074a8083c14100003565000c8143e00e0400855098150044c81e16081c00d65155a40100c000c0b45130000890741182980300e40c0e61f003401c903403a1080045110f0030380d01050f428401c00908002042c2d0340020300c400076000d000070000000c00401c0100e00144201d0b004039102501aa0011621100c2e0b4550181244c509404585d0300a80c0c91a2540c200d42096890020104418810740e400007900c0d00150342140c058000c3c2d40b0400c608030001080016440c142101d0460110001c4510b1602031040a500c00c4065407030080010703 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 694400854 1250 694399604 694399619
    0x100306050a0b0a170f1006081003031803020604300206030f07031e0911060a02060105060706140a05061903050c12030d06030c0312020118080702030312010e15010207 73
    0x20350300480b019a20041840c2e0304040c4614654000503250501600003400e21064500c10520226600a07a02d44400c2000030b140e0301c10941c0c03921030b041144400b2065425580c08480441d40e0b40007111507000d000e4008405130b599400240000d00020800481030300c040c0c01440c0c00c619000351968040c0044685c01e41c05a19464100c1e5803241c03001041002a81d254001540104404009448205500541041d01c0882c4d5440068102d004d90080d0001740300c21000c20080b4440d04075900c0050300b002004220509104018103401d034854107000c26500d00140040c200301c2d40c110b51038528541c8440078402181003508011004c9509042541d49180c11621156900d490104041c0c0c054480895080310b254001e10650300300d04988402071061544d24200074214a50724002070b9480c548881a000d0070500501c21004201000c0101d450f01401c0d50300c410100c0d4000060a80c2c26000130030000c1000203141804501038910300c01d68070300504180050045030141058064155448401b0030f04c07446 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 694402104 1250 694400854 694400869
    0x12030d0b1219050d1b08220b0d112d0c060415180209070e0105090a030b060315150d0201120c0f1103070812090a21080703140403030c02031606020910030605 69
    0x40c2c10130b800940c0da00400d45025a442c05800c00c840070a0b0040c0c002050419620005007000300035849d0503c040c00000400011038482d1181c0100707054201e00012813560324040452012484a0070454101040c1180090800c0340490b01100d02c1110280b2501c14592a44504240303c0c21800ba0291400301c0c69011445405025010304107000713400c1c4500d00c50f68490340c1118648100a414900f08945e24504000010801d070741440c441c1c0207131440420300307400d000c0741c2600c40d151542440700e02c20a9101805041d00580e10140e04221640b0001400000780d8003511064440c41c1d50741d10110782c0620401080d004101001ca01d4a8200b04200800b18044001395002c0d0825a01040380c1c9440300e080983c54a100600007d0244114100c5688004010f00c1040001081a1550f280079a211042102186c192a42002ca13400070740c808038010138401c1c5d01841d25030107540112403400c0442e030180001420007000444080d500020191180c1c106010552506007440c02e00344841c600302800990315 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 694403354 1250 694402104 694402157
    0x20a0f050309010f0e130e0c03030c0312010b0f0703030903030906050f090607111b040f111e07230c150c011104080d1107030b040309090b12030d0b1219050d 69
    0x1b0940b58481a440c0346170900603100c103000000c007220b6039110000425903d9810410003c0f003880e000c00d0000490f2200e600071100c800d00500e010368901842070364164001c0000c00780a80c00c040d035820b910342c0010014400d482c02a10201c4404100e8582030101e5071900c00010000c1041140074601a00084000642050344400285145030420015230101d0024020741070358140380c500b050071001c03529100710000c00028213280140c8802801d6021004954400c1600c0240b40e0080b031071100c0d200321510904498501c10080c265540b19a004001803e84460300a031560074000014001072603960034803907900d207100032080c21810030740343c82411525140300c901040d041c080c0c9400024034981040c403014028540c0041075115a0900382070007007203181d01c0c0c09141030709880c01c0c0d03552002d840e048001030907031000c2000840c41d1407400b0b207550015090104556420480004a1801c862824001c030b40120464240800d90942d40782800c0745045c1e1001320358400d000a8100e0141840341c03d2498048 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 694404604 1250 694403354 694403389
    0x40e070c0c1419090c09060c02010834050c0c0901210510020c07050a090207020f12010605030604051c090b04030206180301020304050d02010b15030610020a0f050309010f0e 76
    0x1518864034041030075410151048020082e8903000800d40b403c0c4c581c0500c030051516a106034205448402c19142c5090300c10020340818200c00c0010005044441060340381e04500102c00d040c0c0e5a0012224484040e07084494041030000c039040101100c10801c0030400d45040750407078882d501d4240084002e91000b01c4401c41c014014540700c003404402c1004440c0aa00420110341d00e06d000d5a07100d8580d92640030f040d108010940300040d903542c0368020303a4449038004000342c0681c580602084200a211540085c4a540305c01000034170780e90a0284ae84101c0c040c9010b4103030440c4414202c4035a00348104500c0034042d13800402d005401201040c0d4003540c0e81510790300d50b140d00030a8140c0c21542c841c40300c2540342d80000304001c104400460520070003a400e400034410401c1c000c0400410803814440301042c039a0920008149180a075003a248140e51401540c0801c40c2a031a9014403110140065035140d100240c04130390b03942d1200414840c000e9916200343d02941180000d2a00c2841080012 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 694405854 1250 694404604 694404629
    0x50708240906030a0c120201080105222a0c06050916030303050406090c060507210f0c08090d0f050609070e0727060c030305100f030311010b0a0b040e070c0c 69
    0x2e4440c0c80802c0740c04c01c12a0042c50704080e080c0c0e0317102103044040784440100c0c0010328075030002a490900000f004000c105094003401041407642e403420080103485888040d8440c0c4200032031292903642840a20f80c941585d6134822190a4144041551806081c0700307500c1c1e201148490308100000d07001d45c26030b03625113004600f9441d0f90501501801c120b20020307102c00d603090310000c1d049c0d41040007800c08034814020b0300d50202c103140a10510308900b004081c0031034074424010500f41d00c91101120250711604200c0d0501c1140004156400e0080c04100c031101c002545102c00d01404201607a4490866402801e50900300000da1030a0100580303842c3c2480b4040e44c44070745106140c45550102100f0121080c4035030b0796400f0040c03042c1e0f01d810701070b0003180c50300022442804104003c00c080c0c44441d85444002803442c0c3d400c566041d4410a035944075507031140c02e070060360b5440c08040c00401454440949603030a202488104400140035901844080d138120f0f0005a090040c0004130b032440d05604 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 694407104 1250 694405854 694405861
    0x70501080a020f16021c0b150103110c060711070503072304050c03180105060a1a0c03030c0405010914220b120d020d02240a1e0507082409 61
    0x200182c0540c0c0215034040101007009882c2c80c100f114090b0078a4000c560000e2100350070b544000041b040c6d181c014020405100026900140580c0e114416102c18540040d0355000c000e001125500240c0c0c0d0301e840d45c2c12400a00c0401940011040e201580d110050141546402c00103541c0300064850250030800704402c524504006100c6c524bc1e1500c060014460b0b458002e00c0c00d11150f0048620503056040035404004c0c00380705110b0680700d9000070300446070b068205800c40b00205c450024134960b22204101c400b80080060010350f020301011342c540e58555003031000150001c85690040ea41464854105907480c1d5a641d400d48240c00030304840740f181c0c5000707601480c058504188015082111102d407440502000a8005245511075080e41c40014160704204c1c1c40eaa850003060b882c50303010450742e0500c03c504803803080d0080aa003000148011445140c8070a80150f09181c3c00c00c10307a10001c0000594200c017850754003440030040c0101201202c081000c609040d001401d01905d03101000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 694408354 1250 694407104 694407121
    0x1b02040908030702100509030703020c060f0705070b03060306010603110702100516030e0906040501050607111c0303020307110304060f1b1a0702120f030103060b1f050a2007050108 79
    0x58590141c00c00079880e901d18080e02d010b5a54402e2400f5004180c0c5400c00080350101c002c416a14030307591542c050f000d407822950800407141c10440422034103c1081204800089007042110000c0034003400c41512071400404150a01a05074400402d260078101c82c2000d100c205000c0302c4a20b40c0c105e82181a51001c2e2404882500505102a8160010b1100d4005142d000910382e600301c04112100001d90380d0b40300174001521020f20810340c00c8041402160005a80e0b0704c101c004403074018041c1042d43c00d81d52419605640000010f4022a90010a0108203948028502d200142c80c0000f180360900c1d1420050100501060000c10400c01d203040c0c1782445500c000d58070019800030f0880381c0400e050705c03400302d0031801555603202521400c0d1050718004604c0042ea8501e180354610181160b286803160806040d0841c00c50380d20160010350500d81c03d031404014141204245c0e02c554991800d518046d084403039002540d0b54002d0301c0081c0d01034290001640f041074407030a2a1030030403034480002 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 694409604 1250 694408354 694408361
    0xe15130303090b15030705040908040e09010e0d030c081f0b1c090515010e040b0f060102010f09060b01090819031107120501020901080a05040b01050f030c09010905070e010f1b0204 79
    0x51615070824244598004130480e5010460011000d4a061980d91010441144c0c01000300900b45103040c0001c0008120183c0300c160f11921a40011449001d07032102c40381051142094080460369031903c800400f580300c04d58960000da217071b201c103078980c89103548140040414400c2c0690080005151409082c08001038a4032440d07620742448581218070f080741e2100e88560f07090f14400200000098000311044a10b4026a00a10300101c2034595038140d03002c03182c00030403440c1076640782d00b50f128038144548100c2210502070500001c4407003c601c001440d69020b0380c040740c0b4681c090a045d501602071018039068039a85030038082c1d540d40e0b1021481e070910400b948880030901e0559080024400190000d00e0150001d0380c0d400c81545e01c0440c000c08980c8259400b610704034030880180040d00313000071012074912006049542003562000098421442604801c00258407401400b61032a0811a294805a001d003442d140e48a50448000d100c1000c401a00700c1d000d8005000341d040d03460740d50 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 694410854 1250 694409604 694409621
    0x90c0e1e072c0d111c0b16080106080a0207030e0607030c0618210207030206031006030609020c100b03030d180510110a08190509030c120c0307080306120313090e15130303 75
    0xe045c02d10980710b41004541110304071344510301000a044104050741c46600c4440c10780d40181c903501d0103070f164005482c0080d040b2020880a1003582040e406480c5d8035030000d000c0c850300c20b40e43d020f071000d00d42c0340c40410b0300c200071050354115051481c0c0b0303400140c0a201a9511b540c6118103040c4450803100d080345401c9007a48040e401c2500003042c02960503540704d10206540076034800f442199039a1105000701d10030700c504e10302ca42d009034807100c0e1280e5171070b04804002040102160300f000b4101c07080400710b40029a040d2192a8041c026000300f19083c000c080340007800b414100059403001a140507288070300c100c05010004030348009803421000032088401741c0d5080404101c685808088581d4035030003100039071054030401026240c4240d491045a441c00d1910014500380303919540c502c0555040034100d6540311501e000d00d109208000c0029250740f4012034001c120840c41d084450080750b03818940310600e074010710510340c1c2500351800e0003034100c42c003001903e81400b107a043c1100184040c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 694412104 1250 694410854 694410889
    0xc0518030c0d200a0b070b191b110309090c0307050c10020414031f0213080a0b041a0c0a050306221509090c0e1e072c0d11 54
    0x44501030001c01801050703860f0b0071965070003840030618100301614019105401103441c0030082c040001d803501ea18a50032060b01e45651002c1c10204c3c0744070003035480105841302980c600142c0412402d9109161a00804401000d1864038482c440880d400050041c030407500040e0000200d580c1030f10600481d400c030f03440e07101507860040341a9140c43c007035442031003524541401d1454200307140c40c0100312210701d0210041791107684a00d003848000690001070600c88410252100011a10424050101024030403140f003440d80c545032410201c12281011100e100c0c0d945401001000c0031040d0868103881c6440c108241c8030754038000069141000340c140da2441c50419601c403425240150040309048120403201c00d401a1114280c100b102e002c1c0801510314050240c04108038814610000d402000d410040c850100e5101c10350152034106070b0300d0b070300000c02201803111a41900b054282001140003e01174959003140000340b2280d402001c00743c100581400c0e01000c503034484841d2000f81008 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 694413354 1250 694412104 694412119
    0x509030a0c0f0e0f07020a030809010902190602150705250f110108060111071217040e15011b03080703231906031e05030f04080307060b01030c0518030c 67
    0x228450302c840301100344a020450101c50300468014150308040e44e10a05d0b441d401001030b0203142c2c90032a520f190242141440d0b5580c0c502c540c0168a031008030080c04001070044c8000c82d485e04c04001e180c405211a14030a43c00d642e81404000c990150440d040e1401c1d000d0a02c1d9141da1060f1002c01c00410407400424440c2080d82c26802c004091442c0c22010710242c8601c20b03d551040300646000e01108107801d12504100f0083c854074451a9441442d2030080c05244a14140c403440240c1507032142c3c10075040300700c018040190100c1c4401c0d04002c00354017841c11011855180d14440a9600000704c0101404000000503240038480c0e4006110407440f400d25900355042c14001300030986080e920050998000451491080c0715809400202d940c08070603420101d010118044034030018050417039040c08200078040c3c01080d0741c000352000e00701c01000b556071407c540c580a0212400781900906141c24504d031501500e40003025941d040daa5080400306d0400071100082c1041c0310200b840da8001c68 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 694414604 1250 694413354 694413359
    0x1c0b01080103083405010b01080118090809150310050a15120b03190201080a0207020d0209070512010f1811190e0a152705010e01031b020c0a0b04050904030509030a0c 73
    0x482d055001640250020842040721f034004403400c45090140c140002800005405034035600d51050582c030b0301904041e401c7c02d80f03010001c0c086010390100052378a101100780b040c0d2000041500c4014101141d588180d20715001080c0981c484013140a8240074079443c680358002c0f0181c02058a448000781a140329581c00f070380b55641c41c0607048080c0d000801410000702a480d144c800c039418190000c1c1522400300703681e801c00c64019030041680c0d080040601c020800602d02d0318566010701480304600c56042e0501091400c281103802480c0820383c10009801d024080e074500319102500148840048030400e50f00999100c02c100c04080d4001140810000e100440c082c030b00c041001884e65000030100ca54540901040e03c3c4c10000b1801041c0d0744010041580244a84400300c4818100030420440e00c2281010b00140d0989040152304400c040d0003032850301008480117400c03003009407800d242c102004220358060041000f400e0001c00a1130b0308866500b0048441c43c44e9000c15200701154 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 694415854 1250 694414604 694414687
    0x115080105070e0406080c0f0d15090303050f040228051305090d02030a090905100b03041103191e0212030c0309030c040b0102190204150b1c0b0108010308 68
    0xc200c800c440014182100f90a8503d403e0080348100ca00007402000761625010802098035805a40c10382d010b50010268400903c2c04e0848461019140c40b0004092010307080140a03148010403110792414500300700310040e90b86d44181505024820711100d0714070601020b00b40352982c05e81002d94803510306e800780031414140e038116901ca00c00d600103440c0d08004903e0182d03940d00400c2d0000c3d0205040c0c5505100a40d0103a000381d50100301800c640c40e03025a0b03050418440d03401910296400e18080120139805d0400300490f0303540d030703011407000003099201c2c4e191074240900304424001c000f0300281c418402d41d80c42007506132609020505503561034403400310b416074035444a82150b02078090800d0821240c94648604004a201a00a4140c840c0031001c407080c04032070141c040742d20079a9000b80070401d030403240b4000c010f071030004072550759010f01d2021800764103e03082e05100110709025504100b42d900044c03650441c1d500c98041d548640f85000f51b4224a04410f000d000d0041c19041100d1904 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 694417104 1250 694415854 694415861
    0xf021c061707030b2a040b3f04080c031b070504140c0904110d0b0a05040b0f0105030702070504110a2c0d03110115080709020915030901150801 63
    0x80320440440c01c9054000e116141c2c94007610300c8040d0803181214005800d079540407103800703201c85001c0320084101c0d000780c112401582061b009030100000116809602c1c0d101e08802805808000c4603840e11101c0b400341240301b041400c0089256040e15501080c2045080c01c05e51b83d01c0b440000540361900d03021039000d48456030a41c01e0f072070240f0541c5000602400d051083c000c03603a035020310b02c80300340da1100c203003881d0b0358054150240c00c9590b6003040e24030f003000d80000e020442c07981080860b08a002d002080701344070142d00041e1107146406c0d50a40d043d541e502200050003020300703080b5243e64480340264203202451384880c0d0080c1c00c2c2900d21560b10118001000400060384800109100c2c89540100a4619135000005d089042881000c1407910072160781e0118880d05d000150a60801103035802e50314845091003c518541030140003c47d02840f1510103014414000c500700b0b101240090080d10a0a0b4910a14000000460f200034003c0d0007a20304124260060440d850b034a240c0070f4000c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 694418354 1250 694417104 694417109
    0xf06180506070b061c0803041101120e01020315010215041704091e0c110c130f020c0d09050303120a020904091e020f01020a0c05040c090f15021005040f060f021c06 72
    0x4102801740000b0703080b9404082c0480c82c5d00104442d04580d156684c59042e01c003661307411414040381d1071259402c0e5059008900c4a040081c0015859080c544405a10050244002030554000a121035010311031100d41d140d000e6044001c64101c0b6141544108903441550001c0084e5401e140315040e5404810328040b0740700c1c958200801410454a4046400c8045060620029044100800311070b2406121400e00c3c00c84031b0800260000c41c0071420342c00c070b91161000d401c0b190018840c03401805c3d0002c4074040101810f8015514200d05419100d04440004010a60796075000c1083c45443e22140d1013485101e6010500328035a100c078001051800600c44003c03403203901065040c0d0780651011650800c07a56001c615a8801070800d1304202c00390010500200c200020501d0004101400444190041c004a49003910301407880c1402401c1501c0750301e11900842c1010309200000d90b00c4442120b400d5000f400008103100240d00e010064401c03e40d080511f010303035036000c1644400941c850707000c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 694419604 1250 694418354 694418359
    0x80408030408060c190f0201020c0106080616020d08010b03250339050c03250b0912180102010f150f0906140d0c03020a03030915090f06180506070b06 66
    0x6250313600e06000009200300d030b22080d40c000f07013590042d240c0381c0168000d03d190f04480c0009801c00012040072402c550a5501601c172650100060040000d40c0f6030114aa55401d40f0207840704040303509010301040300622030303200d000b8000000030f8000c60040e00220080070001e0500102c1c0303094820001c020f0120444091003154040b202c01d14001c0d0010300c03204001c0503883ca0b40d54034000362003046e5030a801c445002d0340580000c0111803605071100b881c022038200341d0104010088100d0038103050344030b001070006444d03500110302c10b40e2480d010815030700c510440d48200c0c0c004030000c0380100e002d00242e0300114641c504100c504440160112004410303201e080c410140016500c980d80015101c6a2180c596480341440c40002c0d103050060f42d001d40c550142d00819013896a0780c0c00310752403914952084d00015000102844841d29820802c46101c4c1c4500c1c15181203418802e51519090540c800c400c244100b400404103600b02e0001c1c0c903c0248001003a054641c3c0031750030301e1026000115403861 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 694420854 1250 694419604 694419613
    0x6020d0c0e030c1f0c0f030c030f08040f0b06060c010c12200f070503070b010602160801091a091002041202040c080106050d051005040f06090c0507020102150a0207080408030408 78
    0xd190a00151200041c3c000910302c109403000d140c1c0512514260b60041030800440340c02c4030001c90304940e140a942c134441d682e4030320103c281d400c1c000c0c200c5144c85922410070511005000202d946081041a0b1942044240d0090380b91400090030600c9400d00080303c03035003041a034184150300040c070009042c1c640c6d003050102c44a5001c0d41e0100ca2944200d140180d5800d00c106456000c0043c05002028400e9040340d142c034995032035a0500301801d0b40a000180c0c01903030240c41c4101c02d403845000030001c600003400840d5107540c400c03054542e1800303000c11400001000555001d405c200000080c4501042190303a5030b15902d401ca06450307400e0003030380641e0820400b650391030300c00c07900710f030484203280d99082c10719007115500b0014040c040c00303807030100807010b90110342d40c0d481d4451400040e8030860009884e170704c1d00074885c090341c1a00510383c060103c14410500540d03004076540100403c030101d503200307680d42c80200740024001c129024200ca1004680400c800000100030000d8503c00022074 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 694422104 1250 694420854 694420877
    0xc2c090619020a1d010e18071706060901080403181202040c0e09011202041b0e0a0e011802160b010e010e010f0b0a030f14090a02011b02032806020d0c 66
    0x10701070380300c0c070614038000600001083c003030400e4044414000102c145840c45244218100003007140c81d5607100140000003d0f400c3c00075958000000716441401414019182e260880000b0301030702075148640e0500c000f9000203400c1511483d40d00099150810840c010151654081940d203490035204900441c50a156851118003a4a0359245840000d24074441607085c0444414600b060341e204a802c2030719840106444981c2000c101035502c01c5a650400030341948040002d428010b03031002100c280c03500014800da040b000c0e05007440811884000da668031410402c0c8941c1c10951801034081040200042000e140b04030945040f078100400740e0340c00340d0700c803000040405243c3c03044015400e8201310300e4018034041d42104294000300d01c0b0004084506080e1070607005d0741181d5200c03154003e0f43c481c2d0115078004020b078420741c00b100140e5090a90780c0e03010035900c1c14600e03090420005026019a0009107082d030000820f5400a015034480501e001c120b00900009021403002c03440c2100320 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 694423354 1250 694422104 694422151
    0x30406030b1c12112e060303050d15030614160f022d0d05250c140616030c020103061205070b2508030601020c0d0c2c0906 54
    0x14030b0000c0408103042c28202505a903140035028101080d101070040e02c20400440503000e000300070b00210070007002907441e4401202640b5031003000001118a0b86000000e10200e94004240c1d4081141464001a8128803410038591285141c0c0014801414208144107283c8031440d40c81c0a05140408800c11582d4204103480385440044040c3c01a400403144e421410315920040302c0008000c0c5909118000c01404c1ca420b210202c18154013080001030b1602440710040c4a8010211110101251b80080c0d96103081c00c0c1c3c07440d40b0845c0038840c109036184070303d0ba41d1403044904815071401075840d5100c86240c05002200044800c2e03000c82d01d0501d000480311902748a5030081940310703010f060031030f0400c4411a010b802c85901c0c24010207414000c1c8440182079086000158020a142a22446c00b03500081c038104962a000380503005114401c000601e81e00c1d0f144040c0c0d1104201c261a440545420940242d28071f100380b56a417010605001d203078000401c906004641208512919031381ca26103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 694424460 1106 694423354 694423369
    0x29011d09070f20060a0c02070b03073203071d13020d1a060706020f07080706050f06040e030d0b12060408180a0302011403060f060c030406030b 63
    0x3088010315410240030b400c0c0101c640f21040b00300c1030b525071484d1035820140c580050291101903c059450013405440041d1003045486600c91a08000041c0040040802c580350b5031800b552403610810010040d00540c0c0c6009012031840e160780504132800404203010b03031403103030450b0803110169403010140390b07a00513055005a04e551102007120110b03800940440030345442070b244880540c599101751090550005001600c9407450565001188110320b001081c04400280780d2041000c29400103001c2e003180c403da0301d1541c0d101740601040702c6550504901c2c5510030b1080441c01c440d160001162a0005464502010040070005150001c10381d8102c0c1e41083c0410001891420015070154030f101c100c4000440600d9600040c0c0410468000c20b0305110000000800300e031109880c800a0801c040c00d25a96441030101040e141d0b0400e0050301c0005c1d0400a43c100140350421 = true := by decide +kernel

theorem cover : BRFrame.Cov 694244604 694424460 := by
  have h0 := BRFrame.cov_init 694244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 694244604 ≤ n) (h2 : n < 694424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
