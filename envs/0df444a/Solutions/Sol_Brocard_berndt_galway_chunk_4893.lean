-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4893
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:04:40.909998+00:00
-- url     : https://prove2.me/submissions/05775f75-88bd-4269-8cbf-98a1be9e3a5c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 879856115 ≤ n < 880035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 879857365 1250 879856115 879856139
    0x30f18040f050f16090905040609020d08031e060d031107170c0a1401020d050a0c2a0501080c0703032a050a120501050d03030509070f0801090c080c010f0f020a05030301030309 77
    0x8418010482640c4c1030710310f281d4111060004a8007400c40c0020f103960345003440c03806008106030080d48421076000c008200300341d0348051402802c40c40c03500604111100250309410f003040d00c000741d01c204e440480c140001e00c501a800a0001d141c4241c5070b01c2a0342d0b03100907080ca600340e00981e010740c010700e080e4003e0b8102046100d0040c03000e20102c0041c00e42c1800084e44800c81e900074070003000340000e41150303c00d025407001c590749503020700500003d19240d629003101072550501c80c107450030780460001d1036612071403d0b94090300401c64903900e001c0541c2e409034003d1124120707011010101c0c10101c400a9550001503910300075a80380d05a4400149200400002c00300c500000020b15040052200381c40380b145010290b40e060070002000d0320384040441c0b0381007803603006100422003142e000c210038006400c0511034900c502c82c83c0c404d041c0c40d0844152641c010824180c005034501001984083c42900d00040c455120b00642c0c4241e040d0b600c179103040d0350090f00141c4c01300340d6240e810069100302403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 879858615 1250 879857365 879857371
    0x4060e03010b040b011403070c170a020d0c0206161e0506090f210307030209041d0c0a18020f0d0c09060914090411060c0714150c030f18040f050f 64
    0x60b001c0107201c1030140042d01402500d400462071010100001b03030003e0142c0b040c05c400030b400516004110300c0308400c12b181c6e50301a50800005010700b00c0340301d003180d0050f079035000c5195008080074108428441000b010462450b401d0350f000054403a001d410864a110740b0b202140104007404e918a4041440c900c0c01615222500032030340020801c50581c2c1604d02e083c0b02c000c409100203540ca854015088000e4010080c140364424038100c08402c0100341e01165a0308a1003c0b015202288480c0e0108041325a240c483c040302801050a001500c004690081500250884009040c400358401c00300407034110f44d1050000c00d221100900210350009084001081510800004420181f003c1000c800001c1c000900c483e602410404166403000107841040c2004012944207130350303d2001c403118000029007035009c0c58280c4141c1483c05002000c85155001000c0214078006444160007100da11034841c000d0540c01304070300c00c50541d4807030203040c64400c4010300103e0030707040046000d184800d000d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 879859865 1250 879858615 879858619
    0x30604050903120c030a021909051906140c01062d0b03010305030a081005131e0501080d080c07060509010c030e0d020a060b12030f19020a1703070309060204060e03010b 74
    0x501590000411566183d07502291080c01d4944944030304a2000103402034401c81d480300340b1281d409640041e44a554501210b00490350010243c44e141c001d0510413000f0b0040c500000d44680c80702021009000c01401040003036000020041c2d500c0320a042001c2002d000811440d4202000121780d0001d0302021014018410328585135500d582d640e26601d01c40c4810940034001c10070002080e50a1404903a0f0003004098100b0540c840c484140400800000340084c0e0078100c45084207481c14030310b200b0603068170240c0d8014410712486490a440d102001000d01416070010085a00054424000d540c018403480e00080780084544001405480d4245000091940580900c0e19880d50000e109005580c01c104001600050500412058240c8401116036440b00040d102d601d81a144003d003c030302240326610f00c1034412228126103a0305603800c007410002c0081d828000e1800780300011034100100e401e00284002c1c241e5a10801e980142e0b0040c1b02107254810f401c803050a00b800307424080601 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 879861115 1250 879859865 879859867
    0xd05030309070f1e03030e1809160f0b0306120705040f0b0102150c0405060a020a0503030405031216140c011b09080d0c02030d03050712051005150307021c03021e030604050903 77
    0x200404c03021301c0022031001900f00700241494a40c2c40d243c1560321900400031255101c2c3c94030708414115a180c1040044510782582d1040c0000c0165203078903100251140410f4803443d60300c82e64104080e50034400348501c0580201c0c0c2001416550306e00c10107422580700c2001081448004002a05003000c54124403041150103003008010b056100444054a500b210243e40320304004d0400c0f81351a001e00c800810f05c0c8400030a00c030038442d00001814841c91b010f0348021040e600c02b06500005204010700b1004100c00040c02110f8114000140402c44945000050f4100c840360500a580400c825400e0100d142c1c0d85092001600620030003020742c00360b040c12014030803280d01003a82c40d110101d5032002c01d45e03100d010178180c6e48103000f00080254414403e11150a0940c0102410492445598030425030a010803070440622001d81b07103e0507080d00646686840f0100c0c0150480401c851041050780c00c00c10041040031a40d40300a44c0c102076503c09442c1d01c0c4c54002c0c03100312403002d810420307640c0c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 879862365 1250 879861115 879861149
    0x5041a15030604080c030c01020f090901120b0a0525080708010605041208030a06030b040b0f0115121a10030b0310020c070603270f0204050a0b1c020d05030309070f 72
    0x600007400b42d009540314992a9030b0300145010107040d40142c2d0840e01055000140b003584c19016500500955a011941940241d030303509040250300441c0d1310014801d842000005a0030b903c154001c650008448800851007405401c8910003428102800c0010488000503c41c1095100c4103113405004e69013011450181448100c680701034802c880102050000800a9140c400c0c0c5d07000078004550100030303008076041500d80a06035040031607800c03005034422800080c40c400701c030b10780311790019081c0c4035600344030400000c070405080002c1f2180301c2c0c42c3c8803449000094950b119200195450307a82e001803654800401c0600340211202d0f1840712600500104100714170106d949802c40300c2c14240050f103006001402100d8040c00044c1d03016641464201d14144030402c04200c4201d48203d5042000e50b035403207440000c4596000c0042e8020711070580c81c4404a041c0000c400340300380010401c01000101c0d03642c081c0f96501c1100c204c901500504400c00150a072068004040c1400c9400030362051 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 879863615 1250 879862365 879862369
    0xf0b01050724090302071401050304032f030f04030c12081b01060f030c03021c110d0f12110d0c0503090108040602070605040605070e120303060405061305041a15 71
    0x10086a0000d420500141d14120816a410010412402c1d03007101c140714014540c103019483d00000e110302c403028645021510300a41c400c2c82207038861a8152592804841d02c81c0941c0c0c0d492811100400d08501000c0c003441c0b40b0f802c20405000ca040298020607a25400d42c90300141031149540185541d01c8030f50808000210b070b02082d900700301c2103a10011307a040c0340308641502400195100e800350040400c00841405125031604040e40d0003954001003101c0340704401041040d250030090606070880340c08219510b000121034030a14054251055070824684811055003d20070103000400c000e100c8290072840207008580c0c41c1511824100d4882d6060746a2948038450062110b040005800c001010060183d041d2511540c000004100030314207860050020f22050318501e01083d0300d022040038030729154115004040c0c201020f9400d40e00c03034030240006000d001d0725080d4410a4843c01e02c0209c4428801d41c5c2c4610b00400082c41401c1301d19644441c140e0b8040c04000840740d512480480c15 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 879864865 1250 879863615 879863617
    0x1213060203040e061c0b131a040f0201230324010c1505180a03030e010e120403121b0303060e0a020a2001110a210e1203060409120507060f0b0105 64
    0x102c4143c400150030040100c0b414011201e090000309208041c5007844070907c0c902c0c100000300380c801c17640c85240045012241e0702034101214010586c07070001080c4001940b203004240298a01d104003004d2408612124040c1d40d041203a44410600000e00110244042001021010380c000e092003199504151500e003140510f00c40300d101d00c0c6460710041081c2c11042d50302c0c5920b020500b801c0d54980304140c0340050103000c01c556412447c0d800c0c840f8003034400c0e402250900b4010503000109140a00d55510b1240c2580411148070910080c6a0910201c2c03250001e1010142e2180d50300080c11818050428022030703014010210080c814820303c0740321238100020180110940420040c810300101400703002d8000100103042800340410381e21942c03a0010480c4031110000800654002c8291000c201115210345400519034000107d400c54081804011a080030b8050300c0032441419a46401d4448843c074100440081c000090200a1003014458442a01ca051000340500e4407620300080407 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 879866115 1250 879864865 879864871
    0xf020a080406110409020d0e060124110a060c050c100203041e02030c0316050a0803031b07060b040615081311060d1b05070c0806010b0406140c1213060203040e 70
    0x2095503108160441010b0320400e03030f030041c0800c5d10305560b2805a45460005081c005a102070b0605c034110010a01400950401d2202c112046005080121b00e000417100c071219030320340345164095000e088011a203a8006e1100e1002c554035800da0b00c0440080c0326180001000303161282620500900001980860255181c1881c008108950b032043d400024108800e1540c01541031081115601c40a42402c01460440e40200d400e02e522950ba0680c450310380c17004981403c40d8240c1002031040c400461005044500e0048400142040741d42000c01c0880d00b003500401600c03841c0b81d102c0c180190303000e00115070001c3c4000d442042a038840c0c0e128500e890480340c4080c46050003180070803055450780e000c0b030381d40700d00b110703041e1012124943c02074102d0344000c500b61580b00d02c0503c08074440b42c00181981c126922170b28030390b1070140f4180c8216544007925000000206082100600e030000810100d103440d0000c181c1103039150600c1841220713410700c55220320150b4005010403c000c9038040c903c154 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 879867365 1250 879866115 879866123
    0x309010e010201150905010503010b090603030712110607021e03120402040c050f03011d0f0411220e1e0f030912071701050420030606040f0f1a040f020a0804 69
    0xc540000e0300c0141e014007080c400011400f20310020000d00601d10303030404ca0403130f40140c1c000c0024a03940014030160b51011512503406500070040c00000030009918401031840e140b0b080074414505441e95414070f50181d0700305005a04c91a0000030170048000c1003a00428402c005515007001d10307400703c107102d00045c80603108030744d11004503040d540560b00700c4400f10f4516080e980d40313686131040102e13411141c40000c402c58150000203020700d400154202d000e503800449504260140c0c070201b1080e580303004581481d5100000c0c0c400c0300280b15004000c48a80550040c0c141080d500d5039620b810350452007400b2055100190308002e204000c0b080700c908607400d035045025444140c084500d001c10036444021001c00a11500000560641c8114041c1c1c3c405c0406881024045002c00c038211000c0c5901c0364103400110100f0941c0c50b1645c07162407071042066000c1201d81401343c80c082100c59098101c1c074031510720300c2c003440070f803621748101d56100d500381000710300784420180c00404800000704010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 879868615 1250 879867365 879867377
    0x71215030210032c0f07091e050c07021c031101051005010e18340f03090c1a0901021204290d06090e100b1005070c15020a0c090e030901 60
    0x98400b000080d0110413607207091146403880700c0c440301035550325454440c04617110702507114003264a0456001d0781503030609038100d00030341c644211600b02c02884040c0114040c08070801040e40140c039003641c050700340c6417190590721100c1d941d030030f02900c0c94440c442030403d141d152104001c62040104503002c181c072801c0ca1310034a2a510320700407607000082e0b1189a031042850001b0029103840c0041c09007001c1071300c03101024040e100c4425a10f0f101c801c0600600105412400c10a1420b200f41d1140821501078182d10801039075418905202c00e11132000b00c6925036000401c41190b58042080900d00c9904010251600f0310304101a401850400b40903202100010b04000400714a402a01e1080340c6040d030421040d1303580c5c04860001c092080444090b8040da07072500c8240c48e8948102e103c255030252401a0040d03103c00111035580c0b0500c011100f0110640c00480c25032182c641405030b20485800802180b40c1c1803d1544802c20a075101da003507181441e0707410f00558408410740d442d280c002e01b800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 879869865 1250 879868615 879868631
    0xa05160c05031201030b070f0203070507061b0b010308030106113d060602010b040b120c0103020f0c030309060609010e220c0806280b0a150c0b07121503021003 70
    0x1c40e080d442180480c02408204100200500c007140100358010070740303620b0b1a0310844c40380c003080e40c4a01501c0000340590b00031050400c2464040c7c00048140d054004203c80689110740e140220360380281c10031782c0c00200c0800188035051304560180c8400c40300720000c04000500ca418000c02080301a0983c80c008894030212251003084581020810300b031010a0100e01e440340c1c0000d000b070200350031039803190381411246640c5080044080301c1c000b000300068096000503600640107544054400c0040c804200300c0382a5000090010318042e0f410b904c080c10a5041960400200040c10b80003808182c0e060014050822290a10041e00d00880c8a11031308003183c0d418070103030440f01c0790300c900005d004500070800081e14a0001030502c48a2820101c2803004c840b407a14120b03148244a00e800c40c01c010400c5c05032201042040c07800240c070f4680446045120b07a1603c103103103800c2d03500e40042a20b180d08500e440040b4010070306010344041001b06003a2458000072540c003020715603042130554a0b000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 879871115 1250 879869865 879869873
    0x40c14091e1312030b0f420301090504030806010c11120c030102040914090c03030403060b011209030804031d01140903010e01090c08011a01050a20030406110c060304031e09030609080307080a05160c 87
    0x403800d641f4030343c640a15203e43c0e403007980a024010840d412000a07840500044666008601030210282c025490070003421060051080c04192200301e0075a901c240d000001c41da660900081014140020b800310306440b40244240c00d007503020b030683d041c44d00103598001c941e84000003a10102c90b042140403918000311001a07843d00b040c07805011a41c3d0901c04040c4c20b043c0c20982441c0a20322a50f80d0701042c00100c200e01c2c0c0c02d10141ca181174002040301d8001001440520003a10b412040100005003841c011a6118211220340c0740441d10501d84c804200403805d400c0c861070b807542441010912000c4071640c00200180304810f030100510400300c483c140740d51013859405440c41c000c101140e51b88c070b4980401502103840d60f07450400c20302c030b034022148144c14408207880c02642d04d602c4d9106d2003154403040945000c00712401c9410040041c04c00008100036000700c00300315028000c1e10b0703600c0c1402c04005040c10302c01040c0c206800c0c00e0100b4404200644c295801c4502400c0c80c00c2c3c1071030701403458 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 879872365 1250 879871115 879871219
    0xa02040516092c04170a0504050f0307060827010219090801140601050c03270a0807030b07030c11030d06030b01060c0f0209060f09040c14091e1312030b0f 68
    0xa4070038821080451190046c1d6084002030095820440311903200300c40d5102050341d180303041d008940004d101e12002c00c2d000034102c6016000d043c055241e101680e100c400141b82260450400380b0041b00307002020b04400da400c040c215018000300002444010001d60f035081c042c10000d010241006000140c000102d40c05106498016020b20410b0700042e4000074101c4124103a005001c0c030801c5044000202141c0005640007100d074080906980c554460000b03800030409006000b00f405288405106051002e200070025016480c0c0000744e03942c15400e0403076003810140c200600f4013580c41d0724107021407034821700489441c0e81215050f016507100c1c80890101541c1e03a140a030003007049810b0104100c4004007040c1641c0b9070b6007940b1011401c070000c00416a10540c0c407407883c12800210003489003400e44503946c1c465100d1900c075120f41019500c0b0450b5002d40d80b454000260f4030621030007549410181c05030031200c21103050840c045960400d043d44015889034050340c1c3d0b800c101f400360b0503a11034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 879873615 1250 879872365 879872393
    0xf05064b0906012c120a050c0108060a06090902130e0103080a08160e330304410c060d050a2d020304060f050c0a02100510060e030a02040516092c04 65
    0x20a9580d424014036015980d844a023001e02c0c0401c05560000c1c40307500340300b001d041c2150015503841042074030700f00c00c180080d806124440101c00d89000e01043c001061103415000754072440d8501d80c1c8038092200202046809094000105e41102c800c0d0240369001d10003074141c1e0011103074010003034018142d9a044550340415010a582d140c030f12900741c00d804402652080d03002e4035242d0a0344039080204050510091041403009010040e83c40c07030803000070704200c200e0b0440320032a981c20013003600280309a04001c10500440d1b444404020510b2070a00901d044140c020003003c09851100f44e2031041c13043d03181d07501e510303681c0e010001409210a03500203858070b20082a040219003040c03915401e0a600c254401710252048009160403100e8034803426104164580503480e105060000489a4040c44080958507206e0700c2054400b590ba240310312406002660103558403100d460901400c0c0a1440e070014807428a00000a054281c100070840c81d90b01c00c080c03100c403180c1e980f4502461641c00e41 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 879874865 1250 879873615 879873649
    0x6012007081006050906012f07090b100f050a030f1b0906091401120b01110115170a02150f1e03010501030f05064b0906012c 55
    0x10000000d07800c1404034080c2d100c03040041c002d01c4600d0301c0d00144201c107041621206e00041c450500b803000710035113000444c150a242e2103003001d03c1c00603074102172030000260050b1645960780d040c1c2911520b01f00e100314905005a04202844c0c000300c0502a04600410750b0040500d0384074140b0000c2c0000d1507002c1180391000d004055079004500e50001e110070000e00501012070210382c0b0101d0349494507002491580c005a4805180200c455005001b0b4103e164200e814412004102c4490403000e005e454158140300b400c8490f52458848580140d0b2244000c0c03180e1900247d0350500540c580000c0042003503804c840942e500c86000c80b02202c10700c50040c24400c1001121100c1c0d07840740080e00103604884090f603041c270001c0341e058110700071a60b007961030030b03440b036081e4240d20001403401c051840c001030210005280d9600010344076101004032503030040300a042d440003200d0740ca003004140d80c01500a2802131660f07941c40c03941070402402141c49210031800428007508039130310b2580d009001000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 879876115 1250 879874865 879874873
    0xe090f061302010906170a0903030b03030d0519020702131a10090303170114010305090705040e061e090601030f05070302060d051b27060d0c09030b06010c0b060120 72
    0x480c9040700707209490351008900040504d13030005001c600c103c01c0d680c0d0701c8070105035400031904c440034807070014025004c04500740342d210400005180c0d010b2001c0c0c03d00c6403d46801007001d180c03a02000841c1e1302030540d85440648148400d1004d80c4401e090b255000c1d03140c2000080f0501441100400c220140340c05a6103e614002000c0d042988514040c040324400d07120290311090745400100c00000034050404070b824100b14443c1150311941020b5001500303071061b204015241d00100c1e0681704240d1005000340c0c480e4080c0440c915914901c000110803000c076110f1203042400e04241c44190603c0043c00c00c2110321100e00c01c1c0030040c01045d00455006100c20394901c1200a45005008100e074a0751605c403009200c003460614440403036040d90585082d841b200c11b82c044801100c00540750344950070035010310840e90444840e02c107040340c9106541f10950600d24503d070240508400501040c100801d001c00309001400b5031000981040090030040102941107002540808440e8081e15203441 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 879877365 1250 879876115 879876121
    0x4180209030a051006080105191a030615130605010e09090c0913050c0f06030c161505090d03091104020309030705010c08090d030e0c040216080705100e0c03070e090f06 74
    0x9000203c0700350460850909001c40e56444171500d080703408c2180d6610004500f051200e188001d581d004d03083c000d00165a440360074183c400070074540319089074050300b50b0b100325040c06011319000a000d40c1070507600d0b90a014040c05c0c2800280003560100005000b14407240200d11444005c1c04020744061000e0003510107450805001c45100355065001e580e603002e1800001420b0400000b000c02c2150090009131858489a03ca402c403039000300400d02e2076044e103000e104009000781031400101e034019480411030b800c02c3e402080c240074030f01c10040141450b185654000404c00f642103242e80c04119001622547c0d400300313941c29032103441401001940f900b140001050707049444a40110810001c442010700c14030819070850754441145101d070360000c150236600345003580040940801d070740d0005082d000541e031058401d13001540112960380102d250507201c908688910001d84420f080205a5094201d000c00e484860601400d90300641000025120000c100100c1c80301d4580301046540a107 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 879878615 1250 879877365 879877373
    0x7120903060c050c0606010f0e03030304151104080709090305071a16020a0b01140609060f0d0b04060302010c031808100b100903031b150c03240b04180209030a 70
    0x62564001166154a8042004611031140044e1049080c040008003c1511440015a291460365840504000c00c11070358100c1d40e00d061001e180140d2180c0b040034151940361006005403a020040520600b0050008000260000520704103c403020600003030840c640c1d0404803580e11070003101901484203410145131021106601d60303c5800c0b1b1169400e07030b4560490041341c940941440161140e9000c00042c008115001000000e20000a140a01d0403007441c02050294200a110a0200e800801c1928404455019511400704100d804001e864155030018103c10441c0c0000340c2004080a01003081070f40c01034030b0340701815180044410072a403601038400075024031500341e8007602c41940d001c10041d028281c004140d0340d02d5110401c1040107900700300c4041d0102c101c181c0301c02e021600b02c0d040c0d45506100f0000d07003a4460780e001c954840481510017130811a45d03603070709000c44080c204100b40d00d16101980d05503844060164002042076000c1c50281c01559942036250140742c118030108 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 879879865 1250 879878615 879878627
    0x220303110c0f0f12092229010215041e142103010b16031803140f0708030901030b0414010e06011d0102030307110a0b010b0a02151003020d0302030712 66
    0x700b80080211608030110407165500e80f140c0c1c050304400c800e81400724600302d161040c3c21240c40303e01100c8043c2c034500c0405103401500c1020302009841c030300c5116220010b0a06100c00c00582c0400e000a1240c0003054014642c4010014009450201c411000c01c5a80c0803d0110400d4550802a803c0355804007030007a503103e80019242140c5040c00074500003a2003800310540e4100c1d41100045c90030703c1808807a400284031804401c07001c00100c03000001c01c030300440340408081c50141d407856244405c110100e81ca003100d10b54800045a00c420010810070b44e002048400c200350038640400d40c80d001c0804540502820710340c01c0d40c80da100c0d000100f403484100c04044d05c10381c3d003603848103050076401801c005e801008034007032401a001040020b1420b40a521034048403101041111040f4016440e20340302080280c003e040d090720005030181d45598100092411100c01c140d41140e2810f003c006004a2201e034070000b40101074914020041c94003d0090303d1999410440b880110313450b100c07008110b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 879881115 1250 879879865 879879883
    0x6070f02011503020604120f0602270d120323090102030601031808030a02070206040302060c0f0f0102120619030503030a0204030c09060b03040f02040b030f03071a220303110c 77
    0x41d071030007244088190380006101d0849801502c040e140030300388403050000b03081c03060040c3c404544003603003640081d2407440142001c803e010017807600b416200c5200030f242d041b0f0011942c802d010b8101c85001040b00c0701c1c0040c50010417410005226045216420301c4440a61a0440c03600d489000f0445684010340081d40704901c00d0f41d042107a001c4400a001142002020280008009100061200c5411390003801410300082440d4181607036640024020380c407552414101c1d8010020a9581d0f4504010f100c1c10304000704000e41c02c01c2c008501b80801e00e14000c02891099032100700250b16186200002c402560300721040e203540c1c3c0780500218001e507000748801c88841c4412913001821104903c2000c1c159084c40d81014550b8403a0b44804901401c2e514003640d2082d0354042c01030040e5010041d60520300c0940b400307140c50307080a00f230402032442d03504010301b0204060402c0010600210811441303516150f481845d001280d41000c1300148984501540f08100015040d08038a000082c20741d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 879882365 1250 879881115 879881117
    0x60d050c041d1207202d090105090108150606131e08030327011b0e0108010b0708030c0f0d060e24010504180e03030c13081b0405041406070f 62
    0x100e1012480029501e8881e0510145c07403c907195100b030340080c0f0316040081c1841402000e00c10404411082e041804416030442c1400e03045003c5280341034141031a80c1c5005040c1124400c10661421078030680f00c040c3d500110b0f84100841c000944140d441d403080d1103201904514500441da244d800720903911100b4056113030070b9421154000f690386000800c880c1320700b248005411502024501300404540850f030549d040795202c5600c525035101780c1c2407411480d40103540c0d080c0d0f03d0340f558001504465068005030721000c802c0203c0d4003c686920100c2c3d41107412049626551702c0071148001250060010010030f007400e240d4002480350340588c1181c0519070400190103180408141801c60280d0403840360701141c41400700300f044007584d1900300c83d5941a4040411200441041642507a01c210b42d406030030200803641c0008402411924005490014000c12044450300002d482c1c032091004880d1003180c44d18001400c00c142d004c8603411486150342102c11074104224061309514a00034518 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 879883615 1250 879882365 879882373
    0x6220f0f142401030507020c040c0306050a06030908040e06012604021003020903073606061b0c0e19021c0c0c020d0b18100603060b04060e060d050c041d 67
    0x41c68600000070540074110b4415a01080910340074015406000010a00420341c00355036810768541d20349000f840300031a01590300245581c1807000300704043c00b090300543c0c1014640501c160006151804583c1a25201012032415581d1000126001d00c988401a02d54400da41060032500c0e8000d0120340c041c80c403c440c0c40151800040b41101240503200503650b15500000e01000001c50008901d504008800c24840682c100a026680500904003101d640c0e50b507152000c00a0540c0805c9082c603402c0c0d200724807a241d00d0203031111011188140a42c00344501c1c007101203106512040044000e9040e8030400395140c0d104140d085550401c481103c1682c941040300b220360540c4100c840c903007420750040440c0010803068545c0014480c2c028002d00722034240039040042a101000072050301100680042442815494582c0c2a02c01001145010728100340e0180710712003440c0c1020b58031000c01d0f90a00303210740c81c605180c0d10348101c40662540051070b09941c44200310200c1100030049040d50219 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 879884865 1250 879883615 879883621
    0x30601050d0209070e041d0a020906031204060305060f0d050a020f04020f0a1803020904140f0c010c021228020f1f05210703090308070806220f0f14 65
    0x10014401c840140250b210410000160485016080a4202c1d1201410014003100c0d000307050020903a03401c0741414981d0100d03603480110700d0610340c01c0da40000b080d001b40c103409000e802010300d180a140a541c05150301c81c130000e0740c03039103d940603250056002413220806640c1410030070f80701c03c040501a801440700030401099070520340226100744074a00c141502d8a0360504003210200384104520b90042a80d000000250791208100f038066800b4022a50070014000c0c07903903240c540d00b07561041d001d4009a006456680c1c110741101c4180d501034460030164031100f041542022001f4448180300c0880e0032458117055034840c05e004d641d52096888000503c1032400f0080243c1911008a4007542c02c224411220347c402c4000e040c825901c003403903940c680300104940060342011150140001e0b40d8030504020306900295064000004c1d00304280203090410101345084012204205000126000d801c4204495844805601301046041100c80070076012500500041610426204081008 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 879886115 1250 879884865 879884869
    0x109050907030c090b011e020304080d030515010f21050108070b0403050a0f0507030501020a0201020d05010e0f04080f0f040305010902030127020f040f0f1b1b08031f031103060105 79
    0x410741981e810655002c4030354a01012030b005402e0425406041120180c50f40c0a0a10079980111008113141c0280d5207403400c02944078509162540200704043c01d1009010036aa040311007007403484000c0c80c000140320450601501d94000101088a0a6800e170f102c491080c6456030149043c0c41c400e506643c2603030b6861000c0d4459004500010306a604800c218100082808216403c4540b00c0c0081d00c016603600d40381c0c1800c9810071218540507035000101c034085140389214050150400056000312820031140c450b80303c24004000601c007400c0090300c200c0190398942690840d01c01c1d9a2002ea503180c13207261050281400420403402503080807448111007051460200d0405041c001c2110301c01c03956020418100e540d80e940a4011380e60300f48103c000d0390306014050b1109003408001c24107003d0360100903140810940c500e410811075101c40600380101444461820390400074154403034850807461805a941d11002c003103a240402c00000412503043c00b4400e06803c2101500e030355a0ba02c0c01 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 879887365 1250 879886115 879886123
    0xa201b0301140f090f160e06040e0307060b0102030912100c0306050312090f06040905240303070807140304031b080c0a051201090212070302090c070803270a0b01090509 74
    0x4951140e1200c0c8000144082529801240e1084511086540450f00c1407078640c1001c1b5070741c129001c4509116001e200703000c1220080f503000034054a041054101040c9100d403640503400c001054a620b811869216078800c200352040400c0082000c03400540500501c0d41c0c90310b018285c0611641091868900705020f407050001315440507001d000c00c45280d480c1040c2503030085035041e070b207c0b0104110081c10744451014001810703808070300191034100103541c0e10052a03000421208400104000700301510b010040e01c001139804500c254468445141c440303c900c4c0e15042e050103d200128001003449940c0a00065607800da0083c030000941724070002d03482c1c10000e8049600100b003c07000300a00e040600380c00700401090000001c2147c181c1e03002540011441541000c291b10141c810b001f989081c8820a03001040c0c0d0100f103142400035540c6214130b000045c903448501c1300c5055000e405001481010780d100003240d05694007040d15203022600000c023030043c060b0740d80c0740100044030083c00103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 879888615 1250 879887365 879887381
    0x10e06011d180303180f07051003021602030a0f0c08060c04050907050c0d0e1206010311040e15090d0f0c240b040204090203160c08030c0a201b0301 65
    0x301001c0e205184010310101c5480000c1c01e00c00212082d08181c0c4145901880654003510010076064042c0c504144044c1c9000001d4426410907040342904210300c6c0d45000c00ba03101c1194a0a0150701e9440d56100c1c620542d0032404040d405001e991251001c00c2000908040c00750b1007003144d200c909458100303280d0b4540b0704454000780c0200802c4113100900e48010b52030390110092a100c0d1a00c03a513a00d2050814540c60510f0000c01c0c52001c45071803916120306102d501c151100c0040020790314507103420031180303604001507000ea0b980d4401400d41c26001c0c07020300301502c850210021181006d608040d070f16030740d49200d000022204041581004d108500c0c1c4044c240e04000f0b507040e080d0361043d082c3c0d10700b03504103041c903580c550705c0700540700e03035100c078000380009100c0319170010784a00d041503500310100310140c50b1004000c495002d03003001074840740580340c104000000454441155000c10354a60410036000e52001c1543c02207142c5065000a03000d082c24402c072000c0100500c20401d141c00c0c0c483c2c00b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 879889865 1250 879888615 879888629
    0x30606140405010803072a0504090b070320042112210c2007181a010216030303020d090f0807031205060a120f0b0f090706050f0301090b010c0b010611010e0601 70
    0x60342015000c56000d5801f194124030005615180c3ca680d48002000c44100040c11100340307058008102c21036400d4458940a10300c5455084800b80304208014454816400b5880c410304c507c004070400b0301c20742008400c60a0b4410840c42d82d0385100b0174040c001c8064404200e147e096140c8100c29850240c0c0508425041c0b0f81d1030b1010702c12002c040c0b2520303000c83d00046051501c0303411400180241d0242414108a0b0072000016510011680001400074032080c40c0741590b02204542c91010003106002c03080303981500d00180c94450802858020b402c0c5041e0142a0038540401c490511003010300619081d4469116050705032403600010081c1d070000c03105140c2c002e440718801c000080c20a4a4400311130b106015031086010365588503030140005540020301140f0103402c22416400030051030002e01000d00b0418280458490081040e00c0b05000d40068191a0004114140d0281044001c495440b20f180302803513031942e000138168442224551003560034030200181a000100b04141a3354003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 879891115 1250 879889865 879889883
    0x3050f1b0f041b0f080a0608070e1005040906020d0b09041e060207060912021506030d0e03010b120609010f2003070c05030309060114032409030403060614040501080307 74
    0x24804000a050000c880960416101c6034402851a24403070002d41d0310701c030368640c80e0b202c8000110040041c0b000506d071480c000c1c40c160b0103001c48080051001c0c12586803c0780141107a0714a1541e541020b801c0c0e0000d50002e0038036140f10200400c5801805c0404039840007088140080c004028940d102a68040d180907076141001e030704120310346504103420380112405440c2221564929048988481c0305441c07541c5641e20011b440d40e410305c03001709088041e03150318a0a00380764000a803138400c5010b000090001c0380042c903c5684081d004240910002481203911911350100103482d600b08686896143d482d00551800b11126441005d00560841985049842c0711305500e490b0340c2d1015144205024820103a1000110308000a40c81039a12001034641e03540b410681942d00960f0442d010307c25041007031000030480001c0d03003450082c1200e0a2041c110746418640c68198461a04040c049034101100850705007071600326401040b0341500c0400aaaa0710180c990f00c0b4040c1d06d00040040c1c0c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 879892365 1250 879891115 879891163
    0xb040201141204020f040e06011202150408030d0b0f060a0903120c230102071709090f0f0a150f0f14010212030c130e011d060109080706050310090608060103050f 71
    0x1000500d60717150002c003600c00140019a01c0c4643d24095090307000142055000c0c0460b81141400382c00049004071181400e820281880c107102e80300c0c00303044000e2007602c2d5141c002511940e40c5020400c00c01601801c5290b172046905001040480c0c030740403c0d150700103042400e5030058824441c01c2200c03074100d030320108042032552800b0403e00ea4901c14040c40c0d90244104070200d0501d040154168a841010726507543c0d031603003884040c0d6030007030180075012900010840d010316051961640325100c030710002140240e0701040c01c0c0d2000150012000f5071007140380404c0c8250405880420350306000343c61b5900e09407103001260781c0d02c0324009070804881c00703002290360300e001c04000e06210324402c400b100040303480300b50780004804242e110609807120f4080d080044040340d031217640c00010030b18029001c0e0f41041006952480f60f441080c0400c1000000140c1022040c400e410240601c000140314040d624401a40c0e2542c0c00e00040d54640a0000740f51401100000c02042442c40008a45200e030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 879893615 1250 879892365 879892369
    0x10f14070819050a02011103070c1211120a030605060a02120d0603060c0801210b181005100f1d13050a1523400b04020114120402 57
    0x500540000c0315a0390041c8200e058929075054066080307685a51844d441d2241814000c0c00d40303140ca128030884032010003d010200b513000301c0010b9100c0d000b194104d088800c1c0391017240c0c51502003003000480d00a000e00c0d1140c004820000b07200d00d002560381400065142c008100d050300c640001000941c0c840100a00480c1040c80540301c038041509000a0a6a0700d80300d100642e686005000b0000c1c900c2070050003c0f00d46042221002020490001c400e035402c0d544d40e1041410181600810324540262a081c1c0e000402042d1002c400d400001c1c0000e040100d809071003409070740200e0810908405020032400d01c10303e00100034140600562409071034400d01c0c000b49000089041d00c050060900e42c1d0b0102c0d81c56070040803c1031858000140995611143e4101e0251281c201020300b1180b40c18090415800c000240204201a00140051160407419048088810300324042d03c52580c000d1014480c004080038801d074004e0300c40700070f5a20900c8107030b112486001902c4260204800104000d4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 879894865 1250 879893615 879893617
    0x12020904020d290108300412050102040528061b050102030403110106120c0b090604080f0706172205100e061501030b011209080d0204030b0702010b010f14 68
    0x81c00074045040c8005151940d6a50040c0005440d41c60102d20b2801e4004210300d540880c0106601400741c07040c50461860042105822200c41c01d110341c0f6030004170030300f502e030704222402041c00b60070300c0041405919205010b5003191042d1031007900d84101c001c001c0910194050408032200040d03142042c00d01c0019901604001c5506000e10103108584001400c24401540264000c0d2501c147d42d1800035141820356032135801c401104501d03010000d0025900200d00c0307054401865509072140e0f0b40c400807824502941c0d000c45a50700c58070310303008a90710b40815910305070b5269075284130352085d00080480381c100003600c1c880b40b9502d151076041840c01a2001009280344070b03809032101c1011010300c200584104c0078040d81c2c95002030041c44982e150b9032400c02260782e02801c00b032040d16440c1c0b002900c0711700d2110190001588540403081049584400c58100600c044000c40d203603900c9040c59078590301d08484004c0958030f440c44040b0150b000e02212400100c0c0c540d1030314814030b4110b0f00c81c262 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 879896115 1250 879894865 879894871
    0x603040f0f14010b09010605211f0b03041b181a0901060f0207170c01140f07060c080a0603080a050903031312021011210d0504150f0204120209 63
    0x1aa1403200c0400c0010308410b07122404211803800100e21040d1150410109003c180d00603418058108018103c02111400c0f030303004070054284450595845466054601d441c40700304c0485010103010100f440c00160b80610300440c007500081001410700d1071107084806883c02061540400b8032407468100e440340d00f204080b59541c081f41c50490303100f200403680c428000c0c0c00100100e16081803910480340d0401549004101c105107441242242e81c10154032070200d244032504004006110408000c1079400325941c8014a01c059540c44411b4102080100174200c090301c0014105000301e21215628020303c0f066035004104645020701e6003070705a44561000701c659030540030030701c4559440010119408010040440f0740003c40801d44108246000d000c050102407254240740700481c4000014040e200484100d0b41c095014001c604500301ca0041c2216000001e04040800003007000c1011444500c280454040c0210415104101d059010380d00450194400c03411901000d40751403541d2a0b0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 879897365 1250 879896115 879896123
    0x50405130b12100e0303190c0c050a111e01021213030605010b09010810080613140105090a11060f27091f0906050609040504060b040903020c040b010e0603040f 70
    0x48459210000c940c1034040c01c460b845468101c981c1d60550800940503502c400351003840954a140703070641d004504044052004c14a5640d140c090305103940c0205203000115400c8002c0718122112860014010044401c40034021600c4050506d0501d02c0344101d6200b0300016009000c200d4018002c184d0207801c00c10b40c0310302d07014904000101103410b40c030035117018000da4120199241191000500503050245c07641c200d0348100081002181c1020607070b10342211010f21070040040260078090350803d0000c501c0e078559441d2805000e05480f00050416545101c0e50741400c0c070004582c2000200d000d04034039110812002c0007481761503205c00c250840a407540c40505041ca40c0306002044a25104990b441c1708180040108100c14115034034010040503d500c01340082418140840ca2030301454181c0ca00494640b40031034104000c40e001f100d600c401c0039104100303c8415040003965494032101d000d0040386070102e0b00409500c107030344001280314098862844d640341c039514100790400da01c4c0162 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 879898615 1250 879897365 879897371
    0x8060a09090309050f0906060a0c02030c09090c1f17060307090c020a0c2102120f0d020304260607230301030602031f081209010c0506010602031c02030705040513 71
    0x411048400e110750456680260340c0c0c40b076520704010902c10b484c003d9041ca103120b0804802081a9a501d140440c0c441514a1408541610f03041c0f0210b86040c1680c407010380e20040d00d1082003108500040c1d12900c0003000c9035681d00581803c440e0303a0822a840d00300600050000d480c01a108009804054004a01030b089558039030780c500d41c440403a6007580c0c3c250300603005408441c2c01d21040c002401c001d400302d15655070742d42640d01003030145018103803030090151041b0001688002d80610018034101540b605681200102d094003d44982c001c0c02050494161141c40d4002c058461044110742e8108100a00c0251075401040c0e60750055070704600031a01010220707400301c0140038041c2d402584030706005612030a060350a40c0d8640d240703074a0f082501e030b6085e0040260f0b02c0700080810381c0103280400309983d07080b4100100c0d144450103601404500c20b43e0000908943c3c0003008040c00341c48901403a220f84a0070b0881c0f0107a101c01d0b22000c0000380300303200038411031824800c0500741c00c406034400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 879899865 1250 879898615 879898619
    0xe0f0913080f2a030c0a060c180e07021b03210f0406090f0b0307020a0b1902040305060f0f09070302041109120f19080d0c020705120109050c060c060708060a 69
    0x20109680c81080b900c3c4521081d00d90200741d8200d0b0611062805616501441c10800c0801640790344040c01c031405400144c0700c102c004542401202d90304081e00d0b80c42030402c042500e6032004200484250b814500511444111417400c40020b2068130746050020043d10100042c1440c21a24003140002d8a000e503504104806007100c01c1801440200f015864019649240c000c0920700000c5d69031011640c9401002040320345503011031007056403948401c800f24a07403103c0d07169a14940303144074041a940d10004012040c4440054224828166600d4400442c1c0d17500203d8400c80c43c3c240c0700b441c2c17103a00c400c005000518007600900f82540c50390b40c2ca242003000701c034000344400d54000c0b041c611580040c040034240580500001c404100c00e80c02c2483c03112020303a01d5032001d11464200c1c6048560b00d104410a141c424024480140780003068a00c0003481c070754083e4001e1103521801c81c0c00c0c2c030402121a120307041010543c0c03100f90261001c4c0c081551807002c143d51400e40108040d40c040182000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 879901115 1250 879899865 879899887
    0x30f081819030e09040f0c060f0e10090b071b08070f0612200c0d02030316030f020403060908040e09010920031f020a0e0307050a1811030a0207030e0f091308 69
    0x130b442c400d030700507000c1d8803610b1010704110601c11032640140003003084040c9411982c0307411205181e025181030301c20948103030140b402200d440e2120b400211081c180094503c0c14861821412307002d04c0c1089180d800368507070b1707501096a01c505603c070308881c1c80180c403820052103000701409907e010061001013114400000f600c08610f10f0100b101e8800f40c000304503140440000c01c03072421a020603000952070340c1482d20860912a0b6041d406901301a00d0b131559055461560701601d0007107a206500740072030040c9140030180d90300035014800c1442c0e03820001a0f02210140201d051064100a403000c1410484105a114181c0382c408941c1600c00e1948903002d403240c1541100340c40d04018001619030000c101c0083c051241e840d1483d100f980201c2c801e201c1680d40d0140f54040300c2c1c98844104040001400341d01c0907102c80c042458945101104108000340f5039001040002e20a54031042c1c0040340604110322406000c3e04503411440b2813000a058218490f646610b0500880c1c0040c1041e40c0440e03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 879902365 1250 879901115 879901129
    0xa060c08031503100f0b0109080c0d1b0f030519030c021c02120f010f23071e030912020a0b0f06010909020c0a0c05220f020d0207030f081819030e 64
    0x1848031385a81d8440b05400c401d0000d225240e810702c001d00e0003103601d601d001001a134409580011520519a60b0708000400c81030101d0703083c0d00c082510002050941d10840c00c08030707000901c016691070203001c1c1c0e0003030004440010740320090b5240c0c4880c10514131030b800340242103010a010b41304010300440034101599411601e00300300c01c00440101000725204080c40d0a5038146009940706905040501002603007400c400c240300c0c0001a0b19800ca039854101c0dc95a81d44589003902c02410060001884107525400040c1c0d85806580d8200b581c090691040fa903900403190050202d5403d40b000c51841c080d1404082e4100b20140341140c00c40c0c1d100c5036200102e9001040a40701e40e405109410200501c1c03040040013440304136824044119210103807402030b0f0900c02d118601c2c030b50b50400209007090541c180c3d80780c0003030b100046481d84420f240280000510000100108080c4c100203000042030101128140b2141c01c09045c0200403008138201c101c007040f00c103c0074011418030300140e40c2c546035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 879903615 1250 879902365 879902383
    0x161d0411040e0a14150a02090609090c040503070e01081f0b27090f031c060e011217040f0618091415030a02010f080613050a060501020c0a060c08031503 67
    0x20064001c503841450140c4d4540c040c082c42a1464004502403600c040c808003d0310f511020410f8050380d61104c5d1400203441b1f10440d0b0240da4000b4100040c000030b40b03d428054000c0c1c480a80448481c1a1186424a034680c4240300740b428952062a044241c003404554018100d40311600c085168a600d41c0021224410112a03846528034440004400260b4105c0c403500000820060148800b19a202a469204282e4070252550007940c6100c200c0209500510080207082d014401c0340d40c64659405070b2009104054900e01e840c0b0000f0340840d5892401c440c204d030045444204042d240000650790012020788407100c031145100c000440816900604003501030310715090081d450309090241c031040421038242e00a41c805604403006036004101c030f001410030390512035030640d03030301000a880220b10b1209400031030070a81841040e1105400c10740640d10260280d071070b00303246041803022448030761050000040c4d081c1d8001021508140040d9041410b03214041014910600402d142c140c0d50 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 879904865 1250 879903615 879903641
    0xc07090e0124030305030601081503010612201f0504050306090d0906080103020919020c0a03121a1f050f070c03060605010e2b020306090708161d041104 67
    0x2802c1039800700d001c85008280858000d69240801815500d0007481c1c0e0000401079030511024501280280c014001000c00c070040c02402800721030f483e8148201204004138003201c90014806d03558000d48240245a8602d03400038008910803049030329400e00510311101c120003800790412001c06c1e5600c0900c0105c1c810300c407081c000c085041003810300030420a1a03911540c10424484018030041c0e1f91116002c6c0c0051600d0044004c0d8003004c0300e0740c0c0003841400c00746190351260380c040f9020141c20061182d8007000b1a00108819408075130310100f09600e43d454154004180b51000c1c0c004902d40510502020107440c055080c0081d0344107545480d4460071003503c1500783c0d25420000c001e59401224040c0600b0728001c0a0300c0440800728030f013001c0c800c8007a03821034034200492841582d06250400c400c0e400504480e10b90401c0051240c80341068000e092260151420070368110b0f03001c494090031a841c03a130008a1592024800303101b06400030780300300e4880450300012300381d540c1c442c001c8050641034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 879906115 1250 879904865 879904871
    0x22d070b010803030c0906130909060b030f1b0d050f06281e0b0321030609060607261303122a022412040b0a05010e0c0c07090e01 57
    0x89040160003090140d1000c1c466920030820480c01e02440e60664031284004c2d103416031280c0c8011081840010903070880009146000c5180c03081c48243d4100d8000d205082d4207641240c81c800684039103d02d006051600040c802820440f25400d000c2900110b10f40958242d42ca107440000302503003494401d4800200a89100f40203507041c1600d00300da1401076106000402c609070382c3e540c2c1c00f03020100400e5928504c903910b804004407a10140050318100e44030080d03c0c1008002d0380000402034100b86c0301c842c050f42002001400b1030414104071051a0741109400f818855460f800080c0c20110218200c0b10010a01801d00340d854080240e03009107110300b000030039440115600030305084091502e81c41c29859443d100009103000c00003200165015210300c41d04120a101030f45098269208030451402c00082d03402c201f0303c400400e580114403c50758007825440d094815026102d081c000c1115954007580819450074407a40108050a00d0100b61454a0340e41c544071130443c6c115412400490351 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 879907365 1250 879906115 879906127
    0x30403020909030a020f060708180f01020f1c0902060f0d060b070c05010f1403010605090607120c0302210f0903010f05041101020c04050c0f360427020103022d 70
    0x207010b110f4a8046c924241c010a41c41c9081c41005040340f10141a0f242a80d040284c80c48581c14140054010355203001c00a41d0b917140244030320320013680000c00031285010f41501c00101c10145010b06441150000c202504107001e000b41100700350b001d04841c00b4202c3c3c0e2140000ba0b421500d40203005200d001d801d4110205261400243c08001040c64840c2080b10343d5016405000800c025641920424582641c03184581008121103215091002e0410155440100181c950219230354030007e1182d420303998201d401300a5849c0d8010380e5185c1206100080c05410850403502e0f014110608005002007245207078200c00d02d044420a540580b5911090070141010313580400c9055007030503080c1e400308450324250300140028001c0e42c110244a400000707020034001d0394408404d030f15000c2094020742d842c1c180040410710585580f01507008609280c5403040c40b405503c0901e205800210300852152040c2d0300443c0254050420070f100100400e103040e9804c54000c100d07281032070310780056540c0c4107 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 879908615 1250 879907365 879907367
    0xd1b0f06140610120f06080610170f0c010e0d060515010207060c030206010e0601051318060611030a1202210906180d0804051005090606100906021905030403020909030a 74
    0x1840100500e010390507110a0003c1c4035444a1502c22031401c0c020000759092401c0349820140120381e002e1507441c400c0b142804900328060010100f103620040e28400d20544804d42a0344582e603104144070389820191031442c0c9075015017042c001104008003180102404c9a6420301150019680c030280c000d440f000f81d0800b560104512406001c103403e082203040f0b141c0e54000c0d80c4c3da105015010b2002c00e254041105c41e4000d00a84008041181d60501d80c0c5465241031311200c64410000c0140307504104000031400e02070b00744482d44280f841c01075440c065a00720196414040e004144c09596401c10a20400c01100790300b810311342c464440a5645418050344141c5007820103054801c01104c81030100007103407000140c040c1d21000300d051000007595181022418103549540408055003020204030101d10042545c4e8840d40b070848001a020288040c2129001214050300c005641f01048013000f480804440714502440790045070301e413946a03400305402c904181c6894410f6400411013002d80c0b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 879909865 1250 879908615 879908651
    0x20c010507023016030c060b0d12110c0301150806061203030402010c1e061b0f080a02070f06060816080a022b0b0f06031b030d1b0f06 59
    0x4070140c8010201c80b205042c00700800c0340001034003a81440600c641e440400200300a8499051202010341220b4a9904000e0001c1746411001c480039458609010366030320303040911030700c0e00b50003010f480c1d0204c0a114055642c22809100c4080621075404595441c2da024010300d03a0801c0701d0125030004520b003d0300329141520283c08248070f0489030202c0488000000140d0b944140c092a06030800556030800741100b604004621105400c051280e07414450207802c10060604100304442d10f1a40c070207002c944100d01121400e00041494001ca030b05081d10350041d001c150f00600004041c900f0581d0b51000725500d5910070a4030780c000c8180104c004d03050b103483c4001040204041d1901035032590024540021130600350300c800302c032040581141d07449030030b07082da0840e48600704100742d04191030004403c6600715081e03031003449800011a0800c0b660703a80360100c03110240080002ca40c0004090b01c480c500390049601981121002d54003150318200c0f0b00784180d01803800041c624010003920504 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 879911115 1250 879909865 879909871
    0x15080313050d02060a230d05160305040201020d030b01050d0f1a0a0b0301030f03090305061302040f06050901171f0614040506060702240f0c010e062710060603020c0105 74
    0x11802511a000700075132110310803110090a11300c0c0160910800030122046050203c2c641103400f0408551030003034003542d900050080340b00b50000059000344000403415240101c0e40203006030040c13014410501d009070050720708900141480c43c02d00d4030050f0328008440c80c01000326801622112102044a614500d1300c02075003042e51416822420b020310040740e444181700003881c1c000c9a40304202403610811039140555440400d5408a06101d2040e654509801d0b0742688920324001d80480d0208940c03092104440024098206581c43e1504202203110605032030005402090030190f86001c003c5181400200240800110281411180d0580c43d45044081d07000318030745402d004841c0c0da54000d0f60051681180d80c1140c0c0380720702c4443c000281000503610a08a80440d480500304583d502410081d92460000c00643ca0140d032445c0e80e0301c0741a1445408056640300c01e40010202d4102c1c248034050741c901b00e601501d6940b2070712007180c203250b20510010781d01141001c6484001e00820350 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 879912365 1250 879911115 879911119
    0x507140111120f011203020622020d050307300e040b030a120801080a080418110c0c12191502040302150705100507081303020106050a0e01030b01091109060307031508031305 76
    0x3451760f1030783e41c0a1342c0c13000090b0840c480459007543c41c0321a904c14000140003545d02801000e240841c0385801c507601d0304080400c0791302c1412040d06d01c80d400204604442c50004140c0358a034a0442000c090324201d02c10b0780503981258841e480702c6031944041241182d514412201c18044034070743c00c1d00a05828042e003088a9580010102d580802c000070140c0d41a0f503003c5100d580701140110556000f050100b5000c1c1c01110b0205682040300c4000c1204182841c042e00c41c2d81e458661245650380303c50040030503c20341d03000c0e600243c002c039940300032102c1c04040340003006242c030742c590300080d000c140d4180d1864a400d4000500008114040c042e180c40894606010700442c1407142c80070340843d900406a101c2e8030b0305009443e00340b600c00d400a03001000054031031000c1035101c002c0207004a100340003c0d240d00e21401c0000416013164400c8208501d50707207801c01e090491040410407580c1c0701410800070035813034400703828558080c4004100241440c2e00115035407040c220320008801c0b00d5501c0b0324 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 879913615 1250 879912365 879912389
    0x2031612051c0c12120507020c0301110418020f0c100b01110c010c0210050f19031b0203070f0809090a0f05090729041205010e0601050d030507140111120f01 69
    0x1a0041e034000720b00c1002c480d84096030280c4281428000c40321700e0008070001c100542040240905250081081c1c408928250020711601072542c09402241c03040f44501c2c95003903107074460041c1011047d03010348481d020400d242881c0401c840e180a01e49520300c0c00703900c00705907620440451503070002c41c1c0746095122540a0000b01c6414400a0040b02d81202c0181c0248281c118048001c1e120348104d94050030705a40580e1980004640c2902d8a207080c2181d201091410f8050444640e21346010102c0c056541d000b14581141b43c1d60342c0980800c0924201c0d03000c3c40c03c0c001004117035180070101d4482d1900c0d40000a07401030241020040c1c03580640f1806041d0450001031250100c500400f0500243c103000760031071103010f840c2d061024441c80e0300c0078030300340e40411542e0100081908081d8200c0800d4040b101c0780e90f00e4808201008601c00e10090102e6001c0099900003060081302c00c074400c004000024400320014012009540112130215508528204010000c1e0226107414050b0100306484 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 879914865 1250 879913615 879913663
    0xc050a140615031c0e0604031b0e010308030705130b0d021c020412140a0615031209050603061315260c18090f10050a0507020f0c0402070203161205 65
    0x442c0c3c95006000034050304d104081c031443d902c940650391103064040c02170070007a503c0d50381e414107542c0e04035800400c01c50441554800507101d0924280c1070b06a82d0000212495512591815a9154090000080c8541883c82c2c001600e0100c00c0c0508810496024096520508084030004100c203180102e84203d10500040c4010030ba41c07610300a19580c059210060071541e2600c0c989441910100140b8450925610603048403c030f46022003100d10540d85040655485841600d010031107006090304550f040c00044c00da072404000307804000680410003e450f0300750360054103049000342c100114800703c2d6413004600c00042d203140003c00940101400001c00c1a00018110308140a0319550540781c841c0466599801403201410f2141d1007400c8505140601d850301c00581801c491007944640741c10001110240003003000b400c1c081711180601429440001080001d42003a401680c041c0700d2007044406003216855948041c1440c0303192040160f000c0d24007146810701600100e942079110390703d8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 879916115 1250 879914865 879914869
    0x2e050907031b0f120501030c05011e020c060325230c030711030f0304060e040e06070806060a230702091e0103022704061a0604030510020a0c050a140615 67
    0x410448410149008408008080e8003110381c201c13a0015101e042c0c1c60400000204040c500300001118020f8881c40f4014800407100003041007010322440150700a91184030340c43c03422800950b440b2002549805d001d444241c0408a280c4801491f84003040441220300c5107104410120350b01801c840c44003d04d03001400f030089407a80900e40004101c01148141c2d58507540c3c1c14440c09804ca1400d500f1030348c50301e5a50f50000c00b6600c80702c1e110b50265141c480074051545c008900c1910030350590301d58580c161985020b000340d80c0c0c803810844080180030b146021340f000c0c511407105a401c000b480d160361100788900410202d4a00945540300d0403c00109a02803024218001030440b901200c000d9010b60042803054440881c2c1482017038001404400c1004101c6141d020501d07a41b1100c00b40746c482007000090200c0e078400c0380405400c82d885900000035560075500144540441c6261042e1414000d03035816180040090084a902c0c1000da1140000502003140d02ea000500c4180b40c001184c40e580 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 879917365 1250 879916115 879916151
    0x30c1a0d020d0e0a030315210f031b150509060609150f0a030605040506010b04060e0918120c01050709031205092404030311030a0509092e05090703 65
    0x46510041500820b1964001c00350fa030000000c00800ca041e140c1d400c5140c0f8008009000e034411074548040440c201140014141c02070000e0071031010489030032146903441e229080404840124104214899a0b01d146541e00780d1100140384600504480005140c000e0382c10b071745005180403c582d10400802a580ea510842240c0200c15424000300701c481c444041180c07051001c03600d039040003056000204008142e40070600c1a4099421b139841e41e600d80b8a1001c0a100f288244c100084065883d00d8041c9000384c1034035040003940d542c40002c40807240186060095034402884c2c10388001c548000e070751100707003c0d0139131111451809580b03ca0841d80c400209020f10602881000b5020503152100c0e11107111801c4e0700c882050301081000b8521400b04215409400100c00180d101d500d4050101e07000019128104240c0e19407904108541c401c0c4044034000402403100000c00314601c01d002104040c505240c1d541c1506c2341e41386541413800b8000b21400151000d410107140c42481800108920 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 879918615 1250 879917365 879917377
    0xd0302180925020304081204140103062d120503130e010b030703020c1624030b0d14190506240d0b0c07020619020618060f04020105160c030c1a 63
    0x42204141d41d150042d003240382d4020b070341021580f03214100f2020507a040242c09081101d003152448d850500320000110b060f20340501c10115088030f545124070a0b0410140c09245e0040e100c09540d00b183c0e968000fa8400c5180008243c82c0c54000044414901c1c5c071814108001d460041d2201c500341d498640418442d200c010424001c055000c10301c904240e1052207080069054000100345950700c95140b6242c1000380e40a038504421054000c41445e8000d000394560468004d120006036541c81d180c1034080e10b09031203288000e0041c00849600c00a102030704200242c000c4005110b286809100b40c1c4052807500c0100144854280805c44243e554694600b50117901124115442c2c403903181c180401d000791200298048004100c0001c0030f4410000c0403445002079007201c8003612008035008100d40b10400503589a0058000034100000e00c0400a400c18418035045140c42c1d40c851101d08140f606030400c0b603c1418070a8100280b1003040c0802003d8241c81160040c2c5c96038204100f10207100307403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 879919865 1250 879918615 879918661
    0x140103080a0311280201050907261c0c020f0103050603190512040b07060606141e04030606080f06010b0903030702011b0f03080f13030e060306040b030d03021809 71
    0xc00203a2100d910781819100c0c55003104c000c0c0181c070452414210204903583c0e400d140150f10301070025048060000d02c5e20304403160844001301140c0c404924800664401030640024410907250700c4000900c1c5550307500103240760f40c0b906149330842c8100030340c05030b10080c024105230405061001c140c7c0c0110300c1e8207c0c1000780400c050348050301d1030705d00d013041c8290020f8051054003040009118901700d00820003644621000c2294075200c1405480d0000300c4009921802c8040c4135603011001c090258040c4070062000035410a503691791480f082e100301d82c100f948240c002d240920020309041211a0240007135054250038800c002d4003080c0d6901074031001030704010102c0fa484101c0d10050b520583c5e0b558110101d030341c04004030700340134000b508151038803940c08a0041c0020540201040c0b0404102d900d651051480c02002c01001020f410241100f81d006079240c641c2ea15030742d410000d039615003000351030250715100c2a8845002415003461024010101003040001003201d22441d5040740b550 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 879921115 1250 879919865 879919871
    0x70509220c080303092d0d230d060510022a0112050412091d01060302090103020c010e0d0909050103020f060c0a06020c1b040e070603050903090a09020a03140103080a03 74
    0x6941440e01e1098030640c44001d0328000001400354040010550350189020314a03129a11000c04041d1040f1241d45c090320f000c0794021040d5001c0242c81509030030412410b00050b408001408404003441e80c0c06401c03110080345d81c64408103c582405608204841c4035030001c1c04a0a4013402d0603403d980c0c607560700058a80140403282c06c568041c07205101312030954401003180345058542140711881c4980180007085d07c1d217030005075000c2c04650602c0780212040c0e60134080e929280e02500690030000181d4140341d002e0200044c40c0a0903c0b40382180940c8400034039000700c03c4030b809005100e4a41100782410708040c018400350721134004c12400c03694155100342d5242600020582080f84141004102c3c80c0000780040d6600c5000035a400801804141e144a00300c1032801c100840d0760504c0b0030b00050300080020032a46029034084c0ba408641c0300d00f036a1800807030320700003800e01320123400040c1d9465010401040031a0315204000c5202044e03c4e5040807941141c0fa004a14020144c2220416032 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 879922365 1250 879921115 879921181
    0x6170a0222051501030e0c030c06090d051522120309061416030c090501020a0209130c09050a0f021213020604080d120b0102010c021c051c0f05060303090d020d06240305070509 77
    0x40e0482c0c1103958a13003700c20380d4031074405d000d40059441c10507103114a030400584030015031050315501140c4581d42c0300c4109510348001103010f50190a0703840c0c090f102240d40740600c20200d501c0500040c4552800d00c1070b1740b00d059091a025080307410b0240400100840448240030690b00016010040c0750122540c80195460580303003208088001e1004010301c040d550006640c2c1c68681000f0300443c0303950b0040c0720350384118209030100c2c014468081c2c4030858110101d0380c2c5484907401d440600380090091440e0580350a038192034234003800c0101c00018003900c04d08005180c00c0c0304141c6a03400910080c041c6c2a02442c00039560190f400745040022804521070250360b0040d000c6070340034ce0440e4501c8003220003546281c40140040d6121b80400780c10310000a210b03150100803034019200040c18480703103603980d40030320007054031050003202d000b590b4200241d0f10a0303600440500c0300d04c424642504050440c505282000130f01d60146015030440c8050041c003000f0900080d9602d04d0703540710140c1c040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 879923615 1250 879922365 879922369
    0x6031109120f0f0a08030f0a090b130605090d051207050c1005190605130b0d02030304080109150c051b0c0904050601060306170a0222051501030e0c030c0609 69
    0x4031036280d44580c4000862051628a040881d6003150482d2610640f0b03424070b00a5034168a5000c82034006020301c07020070000354004c81d0440c1d07460b08884441d50024007801d0581d0380303401ca10016940003449042c288106d0007004014060369501071800009849524000c0901030194050252140c00070855180040c3c009031103201071340d0348050400b04589207940c1c0540d80d07038024401941c4450300888041c4a05001c8190780c041d001c100e4001030800812581c1007074091009050100060b0382c02000070502c0d20160342c0410152000d006040000680b54500385480b507044080300c404003d0440c2069400c60101d42c1000a6610700030030346075101c81076151483d034a820b001a83d0000c99102c20950240010311a00155880c180e40240c1c50821100c0d444030844c06410800a0302441d03941e00142d64000181030007100b900305c5c44164600e11842141c0b240d04181615001c9624901c88552902e21400035070b414001d084441c40c8420240071060348840110b0b071102d14005e51240074450000e00307030600b5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 879924865 1250 879923615 879923617
    0x103020a11060118060501020d14030a022b0c080705040e040c03050102031501020607030902030322080304080a030e0d0b070e120708030d0605101b0501090f0305030901050a15060311 80
    0xc00000141e0705103684034401c5401485010864404c40b0b4a4510040784e95400002e9540c01c80072191a80720701c420303806080074020740c001070a10101c3c80d001c1c8070544034002d045400c422685415035100354041040004281214a291001c108200c411400d02c0f81c4540c111003103606803020010300c404a0342e03960800003510602030384001d09540c400801c00495109001546418103026403d5a6403034485074000ca040c2c4d060441e000c9d603d40c00130050403110076001544907a0b01c80c00c04004201d4281c0d140d00c83c81c00c41d0455400b158058020817003071000c155000c14945000d0a00712112011903030691625449100000e110b04240000e101a0304007a6485020040c101014001110080c0e81c4450800c2d03140c0c1c0050303440300f140c5424405c000c500c81c80d1034145c5808005403540d80000c11280505580741a5181d204240c4079550781e214030a0120302c81c80c0800141c240240c60f1642d503800c200c50319a0031554000c061002040c900141c00340d0300207000c03680004441941c074001c20181c01c0ca1240e4415 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 879926115 1250 879924865 879924887
    0x70212070f051b031005061f0f03060f14040504150c0c1a090d0c38091209040b030f07080d0f0e0f130219031e06050d020103020a 57
    0x21020003003400420080c040807001c40c5a8070403416202040503100d80c612040c0ea08140c2e6030340c550485150348007610030071791100340c0c001d00c0202882c19101d070311396241021401c002083c10000b00520704d488803890301802014000c044800715107400070b00d44000b2011300e66100c00e21901c1a40c850f0082014400031405e40720700d21003011020001c0c1e4800030005032034001680c000b140d514031400118012603540320035583c807941c080405401442e600304800c0f5008043c49a0880305000c208008400c82e070700100340d1981815043c580070514800a04003c10343d890001e0070300e541940700e0162458025010300554a0380301c1c099501042844200c000a400c01d021200c281c17010b03120b06d5100044100b00010062500c1c1301540b10240c034080e0a03031085a0f403c2c0d031100c0701500b01e00701d01c1580700f2608010700c038090300800b00702005017420501120505100031000c01c08001941380c0d034a03400f020408500f0304580d016080d8040000701d16010115503004003040010381459400b04d0300c0303030046001e200040c003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 879927365 1250 879926115 879926143
    0x70501091a01060f0c0b1308040807033903060b06040e09060711070e0f2e060e0307030c030b18070314010b040b0f22090c08011808030c030702 63
    0x10240c06262100796a024492180000c1c0715010316401c550080c007100c440c0341d03000080380c07403d507880b176400801710300015404403041070080000140120042c071007030010710300c200700c004c41e0300e01644a108141c0340501c00944806402d1030f006e40400e1007481100044076032101c40803842c12031400005040e801035a101d00c2561040320f04200d18000b0118409204594030f0322901d000c800d0070b00c3c503142d42d82010f000300280c1060060100c1d001e442c4035901650301208c0c901003060b02006a80c4200c4c010013502400b592985080361007484a00d411034000d00ca9844140d00900059146440d190360b80b0590b0300c07001e01600c58240c0481c003c2a422611180080b10440445003515982e1800c560782090884421032254a01503001419182c540a002820280201054903061600007005a02c50301a0080c4140802c0440c000b0131180b000e004a4180324000d6107240f901514048010742555a9148030201141045080c0000a40b250050301e030481030b41c034102a105d55030b082c4141d2821100c005900 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 879928615 1250 879927365 879927383
    0x20405030f060603070603060b1b0a0609060912050f0d090203070e040309030b06180115020a05010c12062123030d0902040c1e110c12010e0622020607050109 69
    0x400e40801c0003403802d00a5100340c044803983c0c1c0d86c500c2c0407400c8030f52038021022200f608200f03041ca500d80c40140c0c0c1030142000c00540308420381940e02e80080750b038440000c8800a4031007840034248152416112072ba512281071191602d030f40c00302e125005104078480c01c61119a103a1000b01991010805407003c1d16910030340404d2428282005460f000d01032104641c5c041d08103000800d80d003440c51941c1c140250b213417201c021590030010100001d40c0c0309003d400461003407500a40201e5000d020340d4a45a41d940c032494000411110048165103d51300329415180341c030098480c203802da01707490014191700407014003c00001c0f55440d200d8080014980d0700c840c0302c04035540e0190300c0d060780603040451089400700054080c203041610210080030246c100c1200401031200007a000e42002c41403a0441c10544e07020309a18000541a034200001c8440c0d560342d01d04015022110070404030360420f058011b154225844c2820628030300f04411002802403101148c43c4041041c00d401500505512500303e03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 879929865 1250 879928615 879928633
    0x90c05040e1009080301050913021503190606121a150f1e030601091413020f0d0513030801080f060406091403180907030216060e24011a0c0303180102040503 69
    0x44d45280c001380140d074031134003401c030100f50001044054280c4042e409001c01e1208518811b412149400050405403880701440070610314100604c0f5601c003800780c41d2509c0850401441c882030844492415100410540110111442d50745880c08042600d41a042c1a41c45e281089100020b0141c0d1082d90b244501c501e00174a100c640030009180300c0c03542a0703618600d25544a41044403504c509143c0c0d41c0040a007021880325220b00d400030008105103c541918003000b1a0f0070a04485044825501c003c400360703580002c01d41e002c2c0b0310a0050251600900079802d6030b0920076103135900a400201015603d2080c24101b060302000c0d201c0100403c4250b07a190b804000c40340b86401200c41140d4855071016001640841c000d10a98100a1400594001804141d658540202203143c6140c00511825202d80c490a4001c0018400c1c01070346044250703654034102d580c0d404c2e088500e002ca6200d482c00d00c411a4003a1000096980c4100a80c10315070300d80c90100741450080c0703d950030268140c080d600301 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 879931115 1250 879929865 879929873
    0x306010603090b100b0a081012050615030703050d0518090405100c050c03090d0f02090103080c0d050a080606090a030b100f0e0709030305130b0301030f1203090c05040e1009 76
    0x400c405450140c3ea49050f07a0759820108503011007a805071700c010b80400d0000301c0104d80301d4180710380e102c00803802d0180003544461201c02c014500c99000c540e95803040d030070807140810303281c42d201c0c01c00720660042004a00310750780c0702e440c0e20075840030100700200400c00011151550350b89070508100a4200740c014146414559100d03240e6960200f1000c0c10840103119885c4510119203540c80d07404095400d1003130740c0d0200a03200003140020f0702e500c9048110907016940d2801020b0003588102c0003160340c4e4a0720382c04c503410301c41041d4020051010520103094429007144d80c03da40480215400d60755850050b0000e18031040f40d400107809a5584c10802c018181a81c59560944030314607090b030851540ca440366042c81d50304844050010340407c2d8100000b0b40194013a05210b00001e0741e030003100d41c41c0e0100c5011904240c3c400d0b610110302030309010601c61700c0c6038803164441c860300e014066101152502034a020091060074091640d541d8922001034041c01044d00310304060741c003409440d90f103044c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 879932365 1250 879931115 879931121
    0x711060a0507030e0a0e010512030f191d030601060305060d0b150111010b0a0e28090b0a021204121214100807180c0306090c0c050d090f120602090306010603 69
    0x200f180402c0742c82034002060700d00b0700301e010100c0e036030521400c0003682002d0600440303812654000840344014040c820800c44400064400d00100800d1588501404100100407440c0c285603404d40005113a01c1c161241c0700030a50303a040d144142000f02c3d280c0c41ea500840c1d90080c1e840005460741394403109000c40c140c0003c0051544071800d1362503c9030312295900d85400c036122444815803002c00010108100c03003c000100d0f43c8107081089020f84020403204460083c0010074222031219560b0f04c1c07110401080006554003c4c00c1c02200b14103200d0102207075034144c0c9010740060f02e03240200310f0241c102807081c20b01001c0042810000d00c10000c481110592154041e2507801c10000a45e50200f41c0100000b800300c00c890b034000344400300c1001544060002c0914030000002c01d070310b40394046002c407054000d9614410341a5101103d41d0700e01c3c00d0183c2003150944804042000e00340d0200b204508045040003070300c001e181c00306a0101503241c014000d10800d440b4903098011f007000010901c9d0154 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 879933615 1250 879932365 879932377
    0x50d0306140406051c02010c0c030305210f190f060905101205150604141602070605090f0105130e040f0302010e1f0c090906090b040b03010209060a050711060a05 71
    0x1c848469806407100800007520031a01415800c00442150800c0580088101c030020034010b050141540c20fa50f00c41c2070004807950000d50110f20001010b0304c1c44072421484c0c8140100b142181401d5007410702a8003040f0002424800e00010b012409401104044d03010001040c00000100030981d84c0c0c80020700a02811101c2c0140d00a100000041c600004d03c400c0b80c000c1e03400006840030751004403ca6100000c007414003600640e840d0038030030542010303015103800740c42c902409921a078030551000346411980d400c150100202408207202c0c58849201c0188090b80c24204252558684100281a203105521001c4401c1c00f610510090149484030b0a4580d400ba42c001d1111202e4588519036172074901142c0d0110260700c2e00103446204850b030022400c042c091400206255580082505039a017642100c800d084e515070241c0214a028801c8500343c9a0641c001e6081c00441310010f420303400f0700e80208050100c0007800d00100468003220f02a80e940042116481d41e080500040054001c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 879934865 1250 879933615 879933629
    0x331206090e21040e0402121203180c030c011b0303110f1903020a0504090504020d0204050901020c1603232e1112010b0f070503190215010303120203070507050d0306 72
    0x700d41480d510b50494000c442c01c3c2c528003286403285071a580d0a00ca447d100c61207008540d4083d0411500c190070040005600980c01020014001641c82411a0510b9868a05c55100364003480503003500da6081403070300c3e0b0001c00c02403807074100180d1410107034042c0c00d0300c00400d1040b1000103001041322100c900684401c0c1800b07405841804000c16080e0128031030400f4640209100348420008621a0b401040e07000340702518550100307805034081801e907081501c007003109940108903031058100402c28511101840f0503201c55240c55600d03507110644c500c5448204030182c0c0350400100f0001000041001c94803c072959903900d029071200c8100388180c800b80c1c50312901305071401400290742e8003074035003103850141c031400603928152400410f68084005050b023980c003841203801182c0288041c10030b514098103603011601c44036070003d00b0103c0b00e05920108640e444014000f080e4003035a9525031400000c401179694480c50015140c80c01180340040062040640020403294507801c100b04036412 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 879936115 1250 879934865 879934903
    0x30c22060e0f04120c05030a0909051006120c02010b06030c0a0801050f0315090c042903190b04030516121211071b0506070c331206090e 60
    0x11165081d126000640d2200710140e0101c0c0401c000c100d100c0034440d001c00240c2010039842c0701d00c0e03540e10b0550300001c41c50b201055007580d04000303d642c0c80c01030071303407000754141030542050071701c80041c100090b11045201020b40d0360720305000040c000d50040402c450b00a0076a0707100d00c2c2200c0c0042c0e041c0d0140004400185006000080e982490b05690040c400000c02074074419218400c00113052100401c1d030301903403241401d0009075031583c0c42045940c1c0410047c0d496564807046020311101d81c0215a01e003c1e61201e80807074008540307042950102e55004038001800c0e100e07401c0488560045009403420b6041c940c20410402203e55041034202c4000c0d1598440c8581c8040104101c4803500b110a031f17001020004000010851420352001c0300741d2111160107107071948042000e07900000e100301d4060515101c14002c2d481c5401500720a80b08010748075010003500800104131002a1b40e0703000074400076214031103084540d50440006044c0341d400400c00d01e403804050584c0c0350000c0492909070703a4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 879937365 1250 879936115 879936119
    0x3b0f07150e03150a1e0f02070204053d030803070806031b01080c0c0a050a060209090c0403051f0b18100906260a0515100b091e030c2206 60
    0x80c04103425070520410080030031a40d58660790f8001400c03811310302c0000700c1740e01c3c40c86200b03070240e620403105a60311160b80162540800c0c414031045440140038000207a005c80c3c1e154801c040308051042c200c01c1d106030044120070000c4001c0b00117806607040207210500200411148035840f42140340b24000480442c0d03566a0300c91400880c81820b41209170000e0f68800004203a00c0741307940141110f00c104011a040101140c4545041c55841c82048542d650001500c0346280b4040b034800b0703000080c2000712854145950758003981c8801c0030750451250040c0b000b0303640115032154004500030401500c4030002100c04c04420807911011500401d06c81070b0a81c0100d2500c1451050000740c54881c440b8405c00e0354a461036a4244185039501911841070b01c3e40d50b00002c00900030003a40c40c008006d10645800c0c910f405405286441d0040920700e801802a00390030f95881d85400c44004480800d0390401406030f01207428641241440c5400c02e451070040080303040020300c2044203458400041020740c3e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 879938615 1250 879937365 879937369
    0xa03090b0f13260c071a160312090605040f051b090604180f05030307030605010f020a0b060105040510081806100605090a030c15033b0f07150e 63
    0x800d09a0b5400d00d10005402400002042040041503880c20201850030340401815007285560001e2904003164001da0340402900e00690b007000405458a2140da040c03a1041d003082e00805510000941000b1400c00051205c14007903008400d0907401a43c188603034502802c2074066851010b208441c144184400084001c1d085102031120742801400300d540d9488510030400501003004600c0e00052020304e80900040d1180da884241c2807040c00a9600c0f45800312001d42200c8007035001c0c038148812125264800d0390b020610307002d440d620600705c144039220000100c840d40519000583c008201d505d030790103955040b4440038407419403401c168401c680501d10f069241c4d081601d00d050840150740f4140041405000544080b01002d0408234040755a602d44034400c0181c0e90200d151103801601e0a0442030345070280c95900d0840410000c1070501c070700e004202000200040d5695040520083c2c0081c440911148144c05411400c50f5036541e2260071380d9014000c141102e5002c00c3c5c1d403001456240c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 879939865 1250 879938615 879938641
    0x11e050405010b090402030405010e030c071401020a08030a0218031006030b0604060b0304020108131a040b0a050f0c0a020f030304030513080105090a060c0c051c0f020c090a11040b0a03090b 83
    0xf8401003900da5050000c05014000070b5000908200d9455480e0711040002550810207071014034001c2004014003803620b401a482e40400c05205411500081011000b11795827000f242e8224107a40801a601d0717801c3c46143c1c3c00c185000000c0c0d581802407100c800e1031202141c0140094901a03440f501d01620b58200b00701c200c80d054490300713000f07290903c0007070003560282c28110b6002405a03003500f00c0304955661000e143e00c086030000310343c503016802e00c0f0900450314131141c0d02901582c3c0070015810100c4120180c8003000b4482c85610900291203c40d03d8420300c1481c03200000303401103a40382e04040c600074165030003000c0800c902c1d020282000400035814000c1c64081c4180d40d0103015030f03c002d038603201c001d02060507100052002490200000800070400c000d0420b1030b044d2250320342092180014451b00006184000310350081801c40c1c40c1da641c0c25a0503400c040140d5002078a0301e11644488864004d079404845111000308014080d40d405401001480c4e00c2003007807502c0c2c0e640f03c0500d0503007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 879941115 1250 879939865 879939869
    0x90c020d050712030b0a09060e0117010903091a0c060a06150c08041e08150f0a0213140301061d15010c08160c080109060b03072412020d05011e05040501 67
    0xf0f044860f640c0d203580350080d4445440d480000c0d0056190300c0d2900040800d0341e210f80d114940000405c030041000d4400303111010080f40320f040080c491b00d1019100280303401c5540c0500d10400001c03650034a09200144101ca02c00c0e1030322026900e451070300004100c000d09462040b1004056a000500c0c000d40c45600c81d0130b40143e0080b1254100740c240300149401e204c180002d501903d95045c4042810b0300208850f040e01030510b8901d615078540000d00800151000e04541400c90050041c0c480c032407900f0400c5815100c03094044400781506100007800344c4010340c81a100c2c201146c2e0340031145048002184d1103030000400c90030f00d0040c004011154200b01020207070030040140320007491003c1161443c58240e0040d040c00b40c00a0300e03136204c1070840320000320032120250707500f406c5240c504050010800601e8045203984089552200e0801d4007902030191004008030003904541040c119415500500000302c1c0411176581c44014810020a00b410421144800c0500c00106032a09000f0141 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 879942365 1250 879941115 879941123
    0xe01240503010c1b12140f09100806220f051317070b01090209030a02040f020409150e0601050a05070c0308093102070c03061418030a081915090c020d0507 68
    0x42c15506a4070380c080c0100d256170b0708804102c1c0b0701c810225034107040e0b030180c031060007080d186079502c09030030040090280400c1004001d001c1150200001c42da0344141c95000b48030706800c0410520307048150350000782070baa501c11408030318200501c0051820700d11620a0b141c4115070381c075815612845120900d0052000003040c124180d40140011003050300903101020019044500710358290b40000e0954050500ca00204c50303000c42d007001608541e01400c0c884260201e440523006003040700c82c071003512004190030305110300003681e20a8035101e44119030045070021258a669030710381c90206030551007103540030304c501d200c0c001007205200032818190052504c2c191020b420420307440814042c1d00700c4402900c00d90101c040c00004540c183c0030b041c102e88407402690310303513182c03080d0000000720121606901651050003201744080c1c120842640140b0183c918400c0a85201410740c0904109915150814040140001d095055400c81512120b10b6000c3d94400c0035074400c21506401007420181c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 879943615 1250 879942365 879942407
    0x1005270c090126061c1416090605030a030f14030109050f091c14070c17070e01080a021c0519030e010e060706020f09030a0f120906120e01240503010c 66
    0x2e1305a140268080d1400d4141c00300d425100744450320b50180400e054200020345401c00c01421100198400201c40606a6641c040200e6030a002c08a0350302e015502008003401400c00000b800c840c0a00700141d2010303203c48426130350f981c40d440b0b40340240106031076180c68400f2000120f0348441c404548084280c50000305020302002c030b580e04940307484502200c00c0005c0800c2102401003640c500983d00500b641c0c050440726801d0382e84806142900d290300c080b07806102d600052200c140f004c0b614494154044545561501000700ba41b2942890220010300034400c000c1d04c904040c410000081c3d1060207625404200a010001500d5405039510340c182d000404101900004544d6406407080005d540580e6081803101d802281ca400e4100100b918a0401d0703d8502081090041c201071083e6402e00d44905054a0f10314040d05c02d00d0a982041400b40d01c0e40303c08481d43c04250300120320b504248502c0d8110b410030440401d000b1005005450195091400409442c0d002c0c008850103114143c00300c03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 879944865 1250 879943615 879943621
    0x20705190812060f0402070b040b0601090e070e040216051b30150721180312110414130e030712030e0a291005270c090126 54
    0x101d0342c0d10000b01120752050304a00411816122880a01469071003044e111140d42440c0c241040d514000503e241e040007210041030003480442c12400d40c000d01c103400e000040000380000a0007074000c2d41d00002c03400360000003000901200140e4904881e00340c03420a82c103201c280d0f0900c014451040340e5140c034500f03580a1044101140041188207088442c180c0340c1121b5903000350004210300741c8000b0001850b50000603002c2c00c800300d4000c910900c0d10781c00c0001a2204d840322035000a81400034050213414504040d00d8150b0b0b401000d80c0414101c0f15a580d00c1e01c418080300f118540c41511b500440180039842d003c503413184600040000010011424180c0b9650740b07807000740191404001b09622251140c4400404010100107148501e40a081400640054041c00c584031000804003a00344030920190941d142c00b1041600c2080c2c8145c1011039508142c6240044c07801c4110150500d400e0400c208442c115014054043c004d0780c550301c0074131100160718031050083c801003148940d29008 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 879946115 1250 879944865 879944887
    0x1b05101107121b0e0105120a0c0509070c120302040807050301090c090504081e03061f0c030f140f041706010b16060e0f070f120308010902130510030207051908 70
    0x80016184254503c9041d07041440d1400501082944180118400c040060281e403502c80d006c50070802a200082c50340b56003649540600100300c0c8102c034041c0900d0b00210301c0c07042c450100403107001d80003181c8150304480c0c035000400a5010384030b03a10b03440c040d1010200c1c0524060082010550300178580040035030510140100034080a402210895800c01601e500361030602c501407d901000d00c42c16840c0e240141c2803204199443d602d0210120001c1c1c070303264086402c89280c0d40601c0d01460300c69800b12240c54141c604841410a907403e000007c2640511706c14400000e105460225805007031101f80910080e42c1c507102801400801c0c0402e0007030a505801c0c1c1c100c0d24822138092036010500d400c2d02c00702d03103050283c41d0b290180b1036080b48130140451221101e00000400c541e541ca08442c507030700d40b00200003031018001c9056840d00080d114070640241c11a4070045c1000400403004819901c0000e0700075800040e00300c440340983c42044076080c0369803c0d651296900b000f00b40b458503074000702d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 879947365 1250 879946115 879946139
    0x1103130b0601031109190f060207031109010b0316050d060b0301081b2206090204180e0705010e0607060e07080312060f06070b0a0618020d0b030c030a140a1b05101107 73
    0x8000340c60386c0403042c80020360082c2014281d0007040150043c1040710304600300bc60051a604031b405002d4091000100126440d00c070480e5481445030010402080304920115414880e21040b402445d0502d880460004494801507040b00d10200494a01c29800a00c602100300b55105091344a03a003102c0920030100024041c0e1042c0100c48000550742d40c135603503040100e0b0041d410030075890011504501c0b1010301c1d413086152900681000341540c03803408000a0280d0401c03041603019840203e80c8004009403034200140e038408507815240c0064469240ba583c0f038020406a038851041c4501089203410941070301d0004bc05c010f00068138110217912854880303c80940103400590745c4402c0000c03881e4a040d04c0d41c44500042c04090781c0d070001c050942003640e1100131181d1098000200d0f5500302c1c0c0d000075100a240d940b02c460718802c00c604049940c1441171811004d07002d4503500c0d420f081c0d03403c00e0f4040682640c0044035480c14104100004132200100d0f0380201c1c1d07207a40403a90900c20031100c42 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 879948615 1250 879947365 879947389
    0x18140105010c150612200f0d0f0212010504030f111024060f020c090c1b19060501030b010b03090a0311120c030a020105012102060304061103130b0601031109 69
    0x103440016046400d04504003103d0499001c4440c0d4403250b001181003042840f01040d440280403006c900400d001400111441644019140f088101828140c00c010fa0400f1400b181c0390024213050078800305001442c0603000031202100026075441006182602840a100c4203d034030200402c003022140f410007004000241ca00c003048075a001d4440d0803002d010319070314003403d43d6556880b141d407500d0340043e1510b44480d40c0079108603140350800c00100d02c81800c2e6501c050305540d4200b5540c1100200b50b0400d0300800d0004034005800e038002c418403502d078200a042701c3c03103161b01d511140c0e0b851100808501068818902c2a04440302e95004240308a520111b02c0781d540040d038401e4110205040400e41c46111603401070f82010503000d00454080c850ba07030041075810440601d1301c029081001240e001c1a100902c00d0a001c030118051225030b0f8840d400480c81060715030b607607040c03052000c411010400d90840c0d08035800e80028200f03501c60b002d095003043c020750300c103800c16054804004442c01c070350b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 879949865 1250 879948615 879948623
    0x10e06060c0d11061e2706070801081227011404060801170a03050403030f030f05010806090c010f17060f0303030708010905090c010c150603021918140105010c 70
    0x7441094488442400345040c848501d07181e001e10050300002c038a050420042150780c5014a101000541080310080286e104c02c072105d505400303881501c103c0e00b134028401c41c422103510482040000d13080c4c0100049059400724000c65018000c100b0328500c10748220039640501421850b18400e03840c074200020741c0144414101403c600101c800380c8245500030350b104100240d01d07000100700803110003413912203212184000c0c01c0d03103801c140c0b0081c0040c81640710040810802c0c0f5113100034075205c0c1d4400c0c480d406020400748403a581d51910315a89000a4620320514042e42e0442c40d084d600800c1e540700c28020703545800460191442c0020340020b8010115600302d482c02004401566060000718030410300c41d04c5540c403950410b200d207011690010141c10190744420648285a070708000c103d42d40c15808804810099040101b0001405c442e5000a41040c064000300303c10030782491000d000d0701c00c41e203401d031074683c4e00c0d0041205849003245001c1c502804a0300512255200312026584070380a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 879951115 1250 879949865 879949867
    0xc0305090f040507020a11031b090714041815261203040804081228210501090b0402040b0a0e030a08030a09030801060302070c05010809010e010207080a030e060f010e0606 75
    0x1054021034150f5000721261001030300720346d04403c20042c0d90038105a41350400e9000348680690200240500b4041070755241c4180d81e1140040c880c513100c0c48042155000301d0f020030340c9660b640c2024007100454506070810090510601d4400d00800400fa001194110300c00880c1242903462a4989921010b94040e054010300b001801c1d116950341c0114010307481003210346d80e15441c100115040110901c0102d1100004102d1070180d003003101e59000c0720071150b074a01c252000d541f00040d501c1d40c40e000c0c400200300c0342c813181c0601280d0550b40818101e03240c8082c180144075000d0100800ca04c202c1c0503120f0841e500740300c0001000c3c07150718140920003010b0b00320742c05489242c46040f025007086421340400d6448030070302c00405034000351300c900411316810709508100e01991020080040390140c68100100800000d030344a000f500072003a604000b9000b1036450c096800c3c52035060788038450840110b800c141c0d5801100c1000902544100307411000c100a0340d0030000410740310880507010f160300c501c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 879952365 1250 879951115 879951139
    0xc0e12031606020a0e0411030105030706080106171e090a2006070b0a0b0d0c14010e01051905160804080609160b0d06050414040b1614160b16120c0c030509 68
    0x341e6204101c0301f2040c2401c030396220b40c07500d000c05280c9141c60300601e00b0800d1480040200d15006a004141c10382c60181008803030307468000000d40d05803030723784100d11071107400140100d0070000315030101c0660040d81c009811040c0c1c55001d80d203503140640443e070024010010640481c1d0740840b5035801c030500b030802003103032800c0e24001085060340307203001e8843da820040108620011002c1100c42420b003030809841c851780020000c3c281e4014408904448110001c2580c00d10340708008417088499241c0b220400300080d1b092484080d0414015101140710b842c020030300700d9070005092210f1644c0f210421100f20304240703004405800c01076040264544030100840c0341c0c1e895000750304180071341e402c91070418030b0305042440014401601d003a4400b43c10520080d8100ea02514018582d041c0c455099900c1c00060f00e9034011401c108005060601c9083c240441c07101409010f20504180e41d071341040114420504104543c005200d6801148014a0100c0001c1c0148041c0c0b803002d8000f014110804 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 879953615 1250 879952365 879952369
    0x61d040f0b1009061b08030a0b0d12090302031506060a051305130b010815030606150c030409050f010e091902190f0f170709020705100c0e12031606020a0e 68
    0x44103001da07140031450104091004c1640710807850034010500342c808407040401c0d1543c0c40341d4840640b0780554540c441126001544504541c7c8068541c4401000303800c1180203c000c0124a803400b0480c440d02032194000c400d00180c10303859006070b40c01044946842001701017940c140c3d000840040003000c00c07880008659548444614002c82d400a01203031602c2610300040800034014403a03810f804911000c2000740d1400103200d90710100035a58140302d209644c07a0041503001d178020296081c0b00006000c20f400b0308603000f0a011343c614122626980e40c0f10020420a00012142c4032001c1d0320000844080090303200d07a542c0c0342400503000c01c056071000c81c0000314081507a04900d0076901944000c212a02800f41c5003001488100000005c0c140741c00549034844e8060b21a8140031134011070020180881030000140000d900c403c00c0145091043c1c015020300754800000e071140413481c618074a0440c020044a800d034030020415001c401c0107580d880002c0d000860b01030b0800030154810200c0d5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 879954865 1250 879953615 879953629
    0x708030406080708090303070f120609022a03030c091c020d050105010503120c060109150b07030c0b0c040501270b0f03180c0108190f0c030f06061d040f0b 68
    0x90710039542c845010386001c0102516654000d4421a0107500c00c100300320016600034040540600c0702e2821425002650380c8400c09425203402402c1240c2c40011580204898054044100e425000119005041d210200f603182d0004648140c0d8802c010041c41050b03143c00760680d000c01c02c40e4090140c0c0c440803034000c9082c42c10481e5085a66a5483d40140034078982040784d0700d680804000c0701d0745842140607003d80c83c0c040c18864a45015140c05d030f02203e408031706000c20301900e40113503081d031104403500f001404140160710584a0b0f40140c400b150032130a00000f1038050b100103840d8417441840219200007020346115000071040c0b090000840c250740650001c1400500c3c29800c5034981c01c04101c010429200c0030000f4982d0f40c483d20031071000d0b0340c1110006030300006007444e280c600400005040c000d481c158544440c3c0510f00312003107148581540c40604000c04100040165a40300d078026100e0410400500100f801124504201450f150300f12106601d0810000f007103680b114000300f505 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 879956115 1250 879954865 879954869
    0x160605190509030f042303010c090e0f1b0318100603110303030f1b090604151d031e07030f03020604022817010b19051003091101030e07080304 63
    0xc80140188144018420300a07103401048120203549004440034041d90345110b10b00c00c44403100341da0f040b20059049000c007040303030541000e4000e2060802c07449001340031841e603010ba40c01940200c008900c0030001c2241d424410300400758010910800b0f0900c0c00f0040e00004c2c00c0600318114010808022a01400b406803142c20041000c2030075811403400083d201c00042c07405003e640240104045114404203030390308201d0700440c904030b510000c071168055101d86202c4a401c07440020300050303e000c0303001d20780c4031390102c0380c2d201480d400c0c02048020014183d016080ea05074070100c01214000d07500800100e410040500b25074009a60742d0b500b03418030059110941c05a00010204800d41c00c0080000e421003108500755001800100f202d0320503894140580c4003126100005041002d000754030003585540cac002d041013070969607403c3c000d0981e01f86001c1c1c41c0c001c84d01805503030102070003801400142d5511444400852020b400114024800300c640c48103540b2400748000b800300800d0000b000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 879957365 1250 879956115 879956131
    0xb0c030108030412081309020c0c03030313110303190504051e0d1502070609110102011b0c03080601091e03050c06070c05090405070315140609061003050910020f1308160b160605 78
    0x80c40b1ba0b09d1217009418a60701c6000f682c001e4008104010302000910028804507a001c205190030303450341d43c08645140a015080c200319904030341003101640c1c01c28040c10844108880031401800540b0070900005440078900d504410f03001044030001d820399421a0321000d9100c0c00608010701c5464080640e04a400e0595800e188020655070f00e50f828001c6503210b8080030100100034a84143c010401030fa001c5000e030402800e400420102e030700c0b90b13401a000300384901113642c15800018031a0144a03291000302c0d200e00c50051200e4150074200b054a4503590400980500f01e80b0302024081c6400300248112031502031224003000042424850380c4142200c0c000004414900001c03074201c0c440c01810640c0b040d00c051013001540e80d80e84485c01c00c1004245070224850f1207801820389400003082d00e0080d114000300e81c050340480c0100141c01030020302c2100d420043c0d0ba400402c0c2c0c455030b191850422881e25144c040c010030042d040180351215083c0c890f0b01e2100515141c2104888054031690 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 879958615 1250 879957365 879957367
    0x130321050a0e0310020424050415121805061905010602070605070c030506090d0e04020f0403151508031309020408120a11010c090509090105070e04150b030408070b0c03010803041208130902 83
    0x1000e0480031044040000407400c100785032078101034007041c0cac0041400d0303980c6c104002ca4420444d1a80550018842800e10441c0590601407514020380c03144021100c2018400041d040540e50a1582c090035040b100250090480c050030004100c3e42540070343e1061f14480e40f503000010000f082042007900c00c10011005c0d0281e4950804000c05410906810030303c1507006110299118001100700c0b81200c0c1c0c042031100c0f000d00400e04103c050032450703075081c0f030703808000c00c00054005001c80101020b5a01c41c8071b1051054603034015604a014138055442582c0c0525140074840f41800c0c0144100555420502c1940b000847d40381e0030f68145a0345000024480e402c204407030b0420100050301b003100d1100900991504c3e035070061000c440d1fa90154030503038032191803401c20504002c0003805040080f0b05c1c00c0d034a01d840d0800c0301e0540d00503001120155103c2000481e0030a110064030f05a0740801c0c09940380525064162000c40010300c01500c80407004c015800c80c081419101034001c2000107005 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 879959865 1250 879958615 879958649
    0xc061608010605090907050a031b030605011202070c0e04030c060f0b1201051e060604050405091c091d191e0506100c08030907030503130321050a0e03100204 69
    0x10410344041c1c1c44041404402d001d840050b40c5e850951550200803403514a4036601442d10841c041c1c01e5007800d258807420075680e860041c0c0c0d81034100e00150781c4280c032007600d183e43d500410070403845200d2001d414040741607000d101c0500741c0d051003504140203251207042c0721010348607241103400358041c0e03c01c050b684d40183c00c603e081c5140c90200c01c0001400800c090314002507080c0c0044d81e5105140c1907617907200000b601c00c1d1384001c1910301078100a0030030811460040200f50342c815280501400300700d81c0404401007140b0030180a42901c00240900e110721128900720030f0740d0038003d0046550f460074034a14041c5604640304070300302c0c412082c03a80740503030360729001c0b0790300300c41d8043c0c07696004100c2a84c10060954210600003001c0c0d61040c0202d981b139072200002400c20b623094100400e98080065940a0214a40ca0308020faa00901104100309086154400036009819404002c100c2c203101045c1c4640c0105004c500511000d41503941042e000c0704180100d80c020f8100d0b250301c0d4002000c2c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 879961115 1250 879959865 879959867
    0xa0f110c010b13020f09010311040906081f0c0504090515180402010801081b1e15120106051204030f0e0307060c0506010504020f090d081309090605060f1e01050c0616 73
    0x2410314540c607141d80441c5017030742e125100b051504c640a1881d05050300da00b215042001c1c9501218020071840c501007107003544858215844100c00c040400781f481c4c030b95440300c9070604507108a0302c802140e03444192400d031620b0245406400010324200c0c00d0001d44003105a82d44601d21002401c8100c13080500d0b10349414400075100c602d0680180115901400030803c41c0c210840858402450464010651400004090b8544403c1c4041c068001181c0c903400d446420000303001e0544005200c0484186daa03d8445c11291801141ca80e4854510140e0200e03002c240140341c00355003038800703140007040c110401020030728068591344000700203540601d404051020a00285d405040102c0301507140289030040c1100902030392080911031348107101080104011501255505552000380081490762482a54003d00341a4425202d1509010000b06141307000c1c001064034010084c1a14100c420340c90380c42c0c01100003441e0181c14442c0c10400c008034500200000c40c804d059a45c1034900819038094 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 879962365 1250 879961115 879961129
    0x2d010609020a0f0f0f050d1e0b0a06030c050304030305090f0604032a02030a142a0906030c0a1e08100905010e030403120f120c09050108100e0a0f110c010b 68
    0x3c008100142010403003140381d40200035030640b051a1812a848080028a1500a01d422080010134184120400d00ca010b0715030407000da02c610480d800700c225540ca039001e600b510840510f00001034010400940080e0095122540240d1038030221012968498007a41c40c2401c04d40302a0b0206402c40b0b00c4810401c0441910200d40f0364880351030340d0010340c0c0d81c08666100f01c102c80092001c0703d102c41072400c80320f0405c0500c0d41c0740d459020002c6d240031100c0003052000d46808005000e002c8410004080e4140092050b51380c03000680111102d038504042914419400700c969401c07183c101d503001034000000c024402042d0760355080007518030340c0c40c900030703003100d014900e141910341041c0300410100340b111004130241d0303405041c040f448840e0b11000700c4103006000788250006150143e50201c03154024613240039074800b03032110303a240e440307001d6082c81080b864401c16a846a54200140007043c142c2c109002071080c2d00004520f43c0040041090150880034460b442a9515100240c1301d1078918 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 879963615 1250 879962365 879962387
    0x1906050a0b19050903070e0106020d080601020a11060f0724051308030405010914010e01050702120f0903152406030f0402090415021c1a032d010609020a 67
    0x86032144801d00e0840c000703901e0b029038401180250325066508102034001c600f00d40542c64000c050b01c08464654424a692601c01c2c0604030044c8500e0050b80d29290003591040d0164105070000c00c40400c0960310714102080364002c9503000707002480a132000140d4070007d02031240c458018580788000781840103641d80303610002181424103090a00c000c135181c800d808011150131903282c0f0764031794460400902415100b180200000c40400060404c100194006584141e400c0000c0c00191100b040403030380c0d180682101c0203280010000e1011041084009000303d8030090b0503251280004d4092207281002105c0c1207518200000340f101a5060b0100d595001d500c0c00c440150442c20066040440310400510090003a409200800c040c0410410b140704408115070b0207566901f07444001d103804000c031014664046003004025030701c4800341580b003a11140060010a036446400fa480f184c4901841da94844c11480307103848603517880b828051080642070841c0003595480c5202d83c0244020b6204e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 879964865 1250 879963615 879963619
    0x2010f020316321209070503070611070e010b1222061a100f09170a03051617180609030a030e01020114100f120309050103020d14190605 60
    0x41042041446101041c50000c807198a05540101c8030341c00c07a68480c2c0a0001c401e00f2882c0440c90428000c07000800400b490804807805441944501e9400d6a8034001409010b0345504112024050302d88240c01081e5600f100320200c440c0c81c0d56a0320301150025080e081070312012030006914014911101065800c070f28600b007031214234482e031a806030b5905085040245210349402100300400c90040c14154007a40007401c114422400708005441d19900c242040041540c22000280c0c00c0344050101c8100b82d544800b070035080f602645c00f21107642c010b0130140101c0c0300604151002c584192868071445981c0c091455884034041030401d01003150080e2a40315402c1081a0f000e6600c011800c400307801c0c0c0c5800c000c41a100c0307120060740500146d0030300001101900c8204604e4140e0790b001a800c030380205141e1b018954440d030109420f000f6142015000c01c0c510007081155522030750082c440043e030200d000074180300107a41c03407915480c01e0340c1c2218456401424400c00060b148035040080400b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 879966115 1250 879964865 879964867
    0x13030513120f061b050406140c1504020306060301060518041b0e09070509011d09010b0d2301090201080403081009020301090507020f012919060819050721150803090102010f02 77
    0x13000200801c0c4d0700c900d0007070a041040d01030454014001070000c5c0c8480f40307408000d550440503015001e100280c02110240d2107171081c00e0101d4141e04040c031510b016210058a5012084140841508601e01c040d0040391003141c041da248038024004400d201c080c100b000b866003d141008500ca500d0280c0b140c2000d0b101e2071040c0b00401000b402184044405002d0782c050141c9a900c0b143d10500424448108542040f24401038108002aa000400f041a43e010064580d0015046180d08881201c40002d000c601c014001c1004079000741c00581d400120400d0420b441502d821080c01a40c100385e0041d074055449006001c02540c05000c002c02d141180c1e0000c01111301290842650f540600c0e032840020300f110300b00c4a111383c035600008241e4814490b14840070035618400200840000c89000208404c00c2c40c41c0c1c241d400c03050050038011030301d9a031655101900002010400011510820a900e590344510b2401070941200d801c0100807101c00395858405a80001e402c0d07441c1111114040ea00c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 879967365 1250 879966115 879966161
    0x6080105070e190506160b0c0304110904060209031203040b060f0a06030f020f0403120210020909070e0616050f0706020319050903031608090103110313030513120f06 73
    0xa800300000000b0802191590b1100c802c100019200100580280703400080000b0000d545007120844002034602c98020b151207942c8140320030040e030005a038010040a0040c0c07541049281000a00c0c0e007003405500018030f404103240010303180050026518510203800310811050002a5044a9019030192546c1a083c9108000070301105e01c24001c10083c1f41c0d0360040d1400d600c5071070303042c0e42d68100c001a043c0e0f0758545034100034110962500000005104586900c11451924002d6070611040544880e1054907100d1003501c3ca410314064064004000303002e12651501c44140755031102c0e01500181031811522070322581012050341200055600811601c8090040c01502403128030341480c1030390700c2e8002c1c240005c5c1903104401088180820b24050441800b80b88002440c44401c240c80803c0f40207c2c1018881c01d40c08101c030151003c2c5040c00103140400d01450003031001580840244621680ba40c0f2010845080d0082c10342d41403a029404c0020014580301d49408a01e040380d081407034217 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 879968615 1250 879967365 879967367
    0x21201090b06060c010617060a0e07060c1106120a0617010b0d0609050c101706040e19080c010c09050f180403050a09170d030f0b301f0608010507 64
    0x6607025100c80d00602d800941e102c0d00740020340c4100d0103050503070301c3d2201c5001080880781c1d4800c000e40f100600c2d42d203010341d0001c3d80107000031003a0840c0ca0b40e0722a0a201c188603100c01d5851004d8242c1e45030444420030084051b101807003500341c410601c40c000001e1690900018802414403080540c426a02d0181d07040740d01c0d82d4900110307074800c1e03100d200072406176440c1c40c00d10705001c805c4642c1904a040031006c13504d100e40120183c0410151450424880c0c0d80707003400c0109441040300d07020840d07044007d1500c030014030002c00c41c0e4100d00a8041c180751034241c0e201c072400c655802030810300156486906001b90b1401c1255001c0c1c0310b504071030181800a0302440c2000d01070018000606110000420f4030785a8001e8070100010003e451039000c40074080b4401c0d603180c0100d0703034480000074a4034140f034072280500e10a0000c0c0c448040c0058071200c0007900300c80d0420b0004035038000344403031441d8883d981c041d0400141c0c0303000b5800d00d22100081c2040c038034201550f00c160030200072641000c08001d506 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 879969865 1250 879968615 879968633
    0x1e02070605040902070c12140111090109170f03400b031902310e0c09010908010c17090604050a0f0201180305160b04051c031701030b0402120109 64
    0x607a0500a0069403600f0600c0c1601e449403c0383e00030104032034207403c07c2041c810041034100321844004001d202134180f154070071095204072804180410390a58080c403801114007200115812544116000030302000c590301c3c84c40c0c000c01d6095000ad41c812800c9081e101088021040e40f40d24441c81030807a0741d0140f104076140020340503d00e0081070200010745001908050744071040d40000045507a6a101083e0100742454500c00c2a01c1c4940880081c0360402c0c50600d40c0c0803107004030020802e5850702c2e02001201e87c080c80e01e541c1000700d5028040f07542a001e22a1580f01890b98a1b0b5621091591160402c5004001c05445540c0c01800810010581c045007080c1600d90009048000100520058540c0603461506901303050b00740310301204001c00002e000100c40441d01c420803095940d103e2024003445140680c941080d91a09400860b410504401920500ca8146910740751008034807001962001d03032003558001c1c2c00304140015420900c1c26590a44c1811000380319282d03582d216031540c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 879971115 1250 879969865 879969869
    0x303041203080c13030b01030c0506030403090302091302061314010906020a02060904060902030901060819051504141507090f060e0d06180312050a0608060c281e0207060504 76
    0x140000e0b000003800c0501d071482103404441c5000f075648081034403424070301d16221003400111a144080b20010440e03103000d505403031003144d15540300c0c04014115400d005e1144009042c428495a106a400d001a80c41d00040c2c02d407080b0606805002c50303c3c08036140b40000d017000d503060512100071f0302804642d50100b05240601d805890b865079510320705000c1001803859600c007a680078404018400c03401d406401c0356040751180e10499070200c034520b0080d10921303000c5070000d02a901089400142801c484000795001d409105101851400315401c28100100403000404025090040284140e0041644006000702c50609080325003810300150080d03c030414603611070513007140001c0c00c21010340c110070345071070030303170a01c4c41003121f0510f00906402e0350340e05540011820301000810504c85403107044120340e407040040156881d084807448560f4403000d02120300d01d402070902c2c0b114400c807102c14004807003a982c4140c01001ca101d00003842078140450b9008641201c441040403562144c01d540c2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 879972365 1250 879971115 879971117
    0x110f1c0f02090f13060b0a051503100609050a1a0d0c110d0c0320103204020a030210020307021801181b0e030f1501030c0602010b032a09010b04140303041203 69
    0x18104d50346c00c00250b00403466622841d44650001902a5100841000307107001e40b80c0e44800005103521a9800c6d90450315070701a4a4202d0150041005a4100d001d240d40f0751914504aaa01e07040c2c0c0303082003105581e84a41020301051001030300d103427003080411240310041414500f4202020b0590703001000081158004549001c01141d0100c0060b03081c05010448180c00e2010051040c7c08650002100d0300d00c8035038107017541801000b078140348018003240d204544c010f080740304403801e41e800c0008420b0319038480e00440c40144840c0f00140c654030384810104c509000aa4030561401c185211540582c105141c559410600302001181c2c4c0c00031340c3c00d0f0681181c20040d00d0321501401291420205034010381140c4102940c2405840204031140e050303e00401e003149010b80c41701d10907400e8408800d09103401d0f030300480c209209000d8040440503c525041c0c020242d0004440019000b03140a0708115484400001c003001540030500e40040d200d1400e070051810300c4c1c50007070800800c070b45001c00a0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 879973615 1250 879972365 879972371
    0xa0509133c0c050c0105070827070b03040c0b030906010306050916060e2b05070501021609020904090b190515030304030f2a050102010612110f1c0f02090f1306 70
    0xba0005004030256105445000020003280c900202c00034040d18094038403800014082c00c403510000c07100c1401c800411945030083c03c82070b24051500a05501c000c0081d01c03110314584010403490a01d400845c011188040100015411407c2c010102c0390060f00c00101988440c02480c03001c060046a40110340345802e205151035409008222021126407109980c1e5008c0c0c0304d200c2c60202d00c0314022103080d016804030b0309415140c10040e41e407142c0303103a11000c621841080802c100000f98004180e040400750000c2003117910759607164010f5030180c1e0b20b1501c0d034240743c6c600c551440030b501c20150320800c440a40e9805100d14000f00391a8840ca000241541030003500c0b0b40c090000301c264a0598602d000c1c2c070b01c10003441d4000c0a10100c00750340a801c0c0154208400010202803020383d4000064100d0f0a46000315680403c0014243ca04190b45412803070800201d26103800394034041d1441c6009082c41c2c00e07060864030410500c14002030520200450510a0020703c0a0002e800c03079680754810400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 879974865 1250 879973615 879973631
    0x7020301050f04020f04110f040807030b2d0a021201060c030e100f08040813030308010303030e070b0f310e06060a1e230703020606090c0d020a0509133c 67
    0x8035205202340988030740ba10100280000c2c0205001440c0d40403640076001000494980301c000c92070700307590250a5846004281a41c8034820850702e013240d0000d000c2c2800500d82190a00c4800311408240d00080101c0d440311200e4043c0358011520a95105045403901a00d80522034042d050540d800d0000d4100803c0e000054104a5500121105009980100c2510550760310f4020000700382400100c000900f0100c00345010b0000203821026205003081c0c2c00d0601140340c101032010342002021200f200e462000089c01041e1800015001644144110fa407450409141414409000e448207000e89000c000c0700d05041d900a00340c0090819054a01d244840285002c1f01d20703e00c0041000b540300d064104982001e80c14070010056a1b100380c0985842d55222401c004c08200f0480340740303280300c9040001c1c0342c0c18501035004042c031203600c0c24400d0030004001c010520920301c900c01e11440e80d517a890f2011181003801d1001c17183c101d621200001403444406401345482c0062100c2d2a15603d820030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 879976115 1250 879974865 879974891
    0x5090a0c021f0902090a0e100c090e0a14090c1e09010b07261c05060306041b09020d0225030e10360605040303020a11040b060c010207020301050f04020f04 68
    0x40c00c003113038004095030303000c0c18040002c4004206141da80c140300c1c41a50303110090a8294003030700b00c4183c7d8946801865500d84402408140001440116095513995010f1104050395501c18050f8003040700511040c1c600c1011b0003482d011442030304006522500f1aa0aa0f0351403888440c15501c07183c0d045c80e00c442a40c6042d03010b80041303000c0c0e9002019a42260703450a0600d402500c02820140b509009801c940c8070302004407481654070a406802900005001c190032003400384444c4c090f01c9000e49419900c4007924101c1e08282c44554000e40c00055525030401940f1440c4610f4010119588421140d9134010b004d440a03941c0c15402148802c0d241070b1110b0045111710000007003410070110a2041100c161000e03207a02000300150b03800c10780049146403088048ea0141c0780d1507001401d0721005622068854003624401c1e0758056150527410042d91075040c05891154280c8d4005a100d060510415003502e100034a42c5842007403140c20000965160318082c2b1011708250b9001440841c168a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 879977365 1250 879976115 879976121
    0xa0c09050a0306020a03050604060303020604201005071a0609010311040b060a1806020715031808160510110a0f0e0a180b04150302120c0d080405090a0c021f 69
    0x1018941c8100201000810b20080b9001441c4401203a40d0812095880c0c0c0100002c03078845000c0a070041e801000054000351302c0111510190501700b000c50001c2c440400010062059000d44100190020605100700000096181145109540103c41614203034003c100003503414030019101215403504a80c1c65142c90780003803010390000c4c1085648a80c010313402b400c0805864942c1c0450680310038002030300d500c00314003841030320841d01d0151000700c5001000c501030b00380c2c0c0e1003000d841040000e0b44000a00107100829206a46103480c980084560400d079043c00250b503240001a03092160b48502165108111040d0864505100a4000c50756508485891b48003410f1504401008400b2511480400010310900b5010205024591800003800141c640c060170010905504070030520052801c86d2040c1030a031a100211707412451040c00141e82c02442100544410400040c144800d05100030410782c05103035003d0600070780341c0c1e80100944d1200030115180011034516614002403a0fa90 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 879978615 1250 879977365 879977369
    0x7030f14040e07050c0d170c1c02070516080708060a02031816140f0d060509030d05160801050108090723190806011d0c0a03023901090b0a0c09 63
    0x441542c0c0d4a16100501409961011108403082e11aa080c0000510b1049007500c64050925001d101d150b100c0340034001180d00704003081030b100600d2801c074000c804024409011201e000c0c100404100b00301e414240000075407074110280c5030b04441e406210174407000802c1c0780c005103081c100599035901d44003800c4803c11103080c1c180ba903020745e020f00c00d005410349401c0001d0744c3d68000c50710f8541500008100211440720001d81d00070840307031036800114806920040c0e109050b2415203103030100315604801128002c5650b40041c1c1d40e03030000d10b0441c2d0f610940f52800340c0002c0c24800b070281842c0001c681e50303184501c01ca811300074802843d6440c4903c29001c90124040c090409145810b0401d10310502184501070207905105880c00020b200541090451103814880780d01411500d80c55072692a50b441aa022410715400b00809007004c2400ca1000003810002c1420030121035020502d2a507070240c125811056a041503039110104000b10019500440340100c0000c94485404060310380a020f6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 879979865 1250 879978615 879978629
    0x4020409050d0f1103090307051201200c0d0813110a050a0e01140d02010f0c0606030b0903030a0e06240f03030708031006300f0c02070305060a0207030f1404 69
    0x30741c160310704440d08032814030300e805426210900c1820204c900181c3e203010b00454250f1660000400300810305145503000e11582c054000801c0f9465a568031454032882078080c03041404001422026851040c0518076000155180c400041e0800d1645e0090886410102409954051907040c1d416643d440e496002040c1c0a00f40840c8142e031082c0b0907640710000d206059413007030400c4164603186440800c50a0043d03050f1111402c80c40756400854003099076120490b00c155070307510040041075502004a1190078084015990b91401c03a040c4d5040d180c10702c081c075405501c41c505102401c40104203001c40100c409040700d00c04cc0340d400014824104c4840655058000000c000c42846101c4006500c06d0040701e6030f000f070440d644d40d41120751007802001201c041d01c100482215600345040d80ea100c0403906c240214103403455075030700790441d015000c000d40982c2c40481c041081207000c0c401d05070302250030702007181031070740d280c6018000c460800f11050401c09408460440400c0c2305098402904031f07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 879981115 1250 879979865 879979873
    0x309080c09013f032601060503040303110714010c030504030503011211091510090513020c01021b0322030b010308160c03060b1c170d060306051f0b0f030601080402040905 75
    0x3c555a444245a000001c0c0d001400a02c00d28580305260380404428254010351403100341e01c0c0c01d0f0207e5031900042d10031010180ca40044a02454011000c0c050b0503008544211640310001c426500b103d080c01182d009050402c010000865040b20550303044444403900340c40d0400141c030300203580c20408290280c1c058041410f20071880c04406c94041d007054250703003115854064220641d401c0d0301c40d101c1e090b032188500c40e0b20581341c0d00e15005010349031549000541020300f944046480c1c4407080b07051488035440840c0c0b1412811400d411070820584c40011006810708580751040c21800502000d45803030000030b981e41101c000c120b107044215400c48440c001c5071f5123a16145024006035aa8188291030500405207500c0441c506540910342c030081180b0300200815400402e900400712500480750380b09000808a400d6015040c890040c81c482840707168070350800f5504122260300140b485d19802d01000058405000490380c10a00900701050680d6075440000c001d040c0d8100b0080042c02 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 879982365 1250 879981115 879981209
    0xc06010b0414180a0b011713031b0f0609030c0c0f030c0e0c19201f02090a030b0c04051e041103090a0b0612060f040309080c0901 57
    0x140d600903206036203050381881401a009410480c10b164021003c1000c40f10342808141c140000d6485000805c006041002d507100c01800f040701c5d0340b03100300c0c0e007200381800400302c1c08109540801901c1505c030703105188910402041d1220200f140140740000e10b4030f5680e422110506002d00e000c248595840303899050360944900f03541d4018009480121000c2c2c07078680d000705400200c81c10b01e40c071441142d0082030030070295054413202c2c10710001400c0d060019019580780e06e400003a420829414200b4010311410000400b0b4902059407007101410b010300c1440b050000b540c80d81d4030402160f03000009282a6141d0300d441010314072442d8000d40e07102d40040440d0351000b403034030441441c84804a50401c5054603040c203005da07522040701c08070032070740200443d00b00080009060b035801080c05001c0e039280410404449282117000e071911402c51004004000826500c2111100680001c0c0050640c1e03400010100c1c000c003006000f40e0400070540200c1c0c18008401e070000d668204682000905213103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 879983615 1250 879982365 879982379
    0x5030321010e0f0a09020a0e0711060907030b280603060b093103110f061f031a070302070203160918080306010c020112060b03010608011d06060c030c0601 68
    0x40341401030851020200c00006480c4052110541c840d4001c0c80035241d1030b0369541c200a00901e8681401c0743d00500300440800c0b50024144001d01c24801a104e28035841c0312600c0c038a02e400070052a09040d6803010fa01480054600c0150320b800c0040c1080c0c0c00e80d00d030306c1c4040c428070300a80c0c446060303486858441c0010904c400c0b40c028402c01a0140c80031300203501e84011444414415030441d000044100291050116003800f1151003039002c0c0c035000c01a0140c00d2006420f00904406401e442d90080041c010001e542d24043c55442c04901880ba0580346160b546600c0b4581a0f60308040200e40380c2c000075092400b035011120304a600a05850102c0402c002c590001040d502800e00c5030b80c03038100c646401d00240040d082c11190001090790039030b0f0b128001140c0312500700b202281088001440303040710405500420019084419189844e9818000c00600c0301c401648020b800d000c080c0e99818400300c0110040360424000ea44071544e8036140b1410519522450310000ca0382d1003100c000140c88 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 879984865 1250 879983615 879983647
    0x15010f11030c1c0c03020c06030601021002070b0901060b07122d03050f010501260606040f06020c19144b04060803040e2a03040308010f15030213050303 67
    0x180d4508050700011000f1045484140703100004000d6803004c81d500500d803400b10042c2d079002e601481101d8400103024012011f981002100b16802c0f0784e04428811090000c0c0176070405481c21950351421701d501c0e0340746c100c2e0300d007580000b510500038480140300104d00a90058800c9410074034072170500220b000001401030004031035091252608100214441d0300c18049172554503a601001c0010303c0b21444202c1c40c0300c41c0944481d40c881010000090220124a500e10003400540c016201819005040c003200c00310044d609411011030260910204145030070045003600c06031014442801c00410261140a8a0752002d444040e8170810300d0a0240c1692400100304103095122144000c440601056454074040c80c05035802c00c0c4000c0c001e038071900030a264404000c440b2400312075248025042081c682a12a0708840d90000400060640242d0344500400450301c401c01010b01e001c0c440031084042c3c0b50794404040c0c00103100120300c900c038400440a410005d00342c2c1d98070584070b1282060 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 879986115 1250 879984865 879984883
    0x1509030315090108030a0315080d0c05060606090d0f050c0415051206090c09070e0a03030c02010e0a0f0909021813020307090c12091505010e0a1415010f11030c 70
    0x2009580c0030381c5030301400c0080c0c40383d0403940d041c030003181000720392002076000e08080c040680c01c10f00c2c100070008001e40200400c6e640c0c083c0300d840d0f061540340a801c01c58100710000b80000d0180300200081205902e4a840070382d06c81d034000c20b45a041d41d110745422814044e801e030348140c1c0300341850082e00d03020303111507449801c0310411a0561100714224000300c0c0c039100101c030184480c1e041011000d07068100300480031b03440f080b1490080c085094080004007403159580040d000030b0f42842204c0d04650304042212039149040b200d000341545000440040c03070a00f40a0740b5056038035034840f4011502c81c01800c0704141007042226040340b802d1881075515500800e000da00c81d1040e80c4001403101e03603521820400030302c0d980d5490100c3e10010440006840100d0080700c40760120391101a00c0c805500c1395034081c1c04441007144250800644680c1581c1c071401042c400c1040000078000c00c98250754030403500c0c92007801e290004030504003090399440310000c050140780c04001403034082c07888085180c0304 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 879987365 1250 879986115 879986131
    0xf060336100b06090108060102070e07080f010b131509030203010f0e0111040602070b0901111009030201291509060301030609031e0203030703050c0c030f090a0510081815090303 78
    0x4107804208425001e07103800c44405900100200b040303116551140311032a0380540180111a271030f035500c2c0c2112051050403a02200007855110078010405035180340c0c24010020b03200414203200b080c4e104011609030b41d22520301d1409000f074200500500612000f00119002402004154800c3d60a4000307441c440b54080d41c55441c0c856a04d0355640f1004c1640d040d03070219401841d07007904180182e14268006103650307060000282c0901c03110a0201304d05c01039042c0d10b16000c1440c00540c0f0300030382952002007420303880300000d00d40320703040e090100700c01d6110903000c56140c9041d8920381c0002a0510070b404030b050304802d0000000c82848450f40202100a10a580380c14040d020003184d074556250800c070b03130401038004201062015100750045074022019405152500c40e00500c894030307541c08000880004500450013400c039203032014903403009080a4400e01c82d20314403003000511200b0000e29035801d03020704d4441c010000e00b040000c0b41c50b007403500c86803120608081c0c070655942e410442e0148 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 879988615 1250 879987365 879987373
    0xb12190b01060309051f140a0e0d05031603230103031815080103060506130c020d090b0408070312020a0b040303020909250302250c0812090f060336 65
    0x18641e4828031644c0d08054100740503082148424010b8200e00307203064001071500c4c0c0c603008018030354070b0014444c60203a0b480d041b0000b00c010b180f40c412070074180b810310400180581802041100031183c68141d0504416280001d8198026020044040b4041e030000903080c6503c000807040540003110f00609005000443e45019a201c480280d003881420007180003030600e2004000189043d00400d8004400911501c8401020749883d0b003141c000c40405030069000c452480c40d5250403801000140c400c05004d240b41030309080c29183d5640f400c0c440201213003104030807121568401e02850503c00e0b40b04050103228102414001c01039000b01d100e0714410028000030441e26180d868140c5d09903404041b03154008424141c0030b41c001c0d000071200240701e40c2c02100410b16140c003204401c0480d44124040100b44d401e00c003030645000c00006500110710010007103c071040c0e4802c000c8030300200d000c5411540d00d54600860b0003143c03191400c030b10130002c0c004000000e400e10b0034040a00e154000c2c403c071 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 879989865 1250 879988615 879988619
    0x5040b010f090c1205040f050f0705040f0b031e031c0516030b0a0e06030c270f09250503060a0605031b13020f0408241b0307030b12190b01 61
    0x6501191505141070340031480e0815144c400c40e0240e040564480d01a0400c0d03820403025888950a00e62500d038614004d40000038240411718251103035806000d1612002c00004910501107a0740d00c0684540d0492103960f401c42c4a404102001260300808904140c011403503e40803107100a04030a42d040d000d409000c102d1031721300e2882442034020216009110414040c58201000019040648503d80502030310f0180d04040e10307104c00261000c11040c3e5469001d0301e00380d0010340d09020213040500d5960020090190103d80080c404108803812115084294900d0b802c3d02514041c903070025030503018910402030410200d50003142110340681c1507502480010702c10058202005180c4d0b680a26241000d4080b1881603000c2c00701248a01c0a061426841ea0440c0d0300d8101c65000364148090200c0c440c81e00520802c101070b0300b0642c03004c0701582c4000011b0030310900d4000140000201940c0d00d0428005945e9404d08081c1d1401c51402d8410841c80701300a10b100e1546090107885c040001d00c00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 879991115 1250 879989865 879989879
    0x109030f0c03021b04060b04060507020f090613020d1803020609101503140c04061e0f0501050f16021002010c090812091e090f0a0c0c05030406200105040b010f 70
    0x540e104540d06a0282240340d41d001d0b1030100c0c1d6150b0304c0109800903964003002c103440c001d403401800941507540300c0b1a01c4070407a10402ca81c00b4921b500003070040d00e0b02014050b054851a20380864603c410102584400031421240001e010014200e650b10000a40e034030145900031541f00e0081c0703440401e8803000218400c1c0c802c150380301c0009550021a840108101180b413502e8500200c0c00464203880e4180d10400c00a0140d0320142c0080c40b403d00440d00c84040d640c0080b0f07400d8002c02c02c000560369117920300000a005070055000c2903840003000250840000e6562501000451f030052020701c0c0d100c04000700900a16256064102003005082e0200361080c0c00204400c601250001852030840000e003440200c6001c207076146154200d5040e20080c60356a115200d1142100384c00e0034881d41780400800c000d98060a0401c0107000e0041c5201011600120440382542c1c007509010040c0c8074030800003c200899803080710041c1d40780c0003d000402244910a6048401024040b0702254860316 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 879992365 1250 879991115 879991127
    0x807111f050915061903051510080c0d03081e090c01020d0e0a12050f011802010e09060a26030f090405010e0f0411121501030302060a06050f040e1c020109030f 70
    0x1035414951143c500003078068a4400b203510250001211150602c603034a41c0d40740c1ca00240d0030b0041440c20400000c000400c500c078501c550082c015400241240750340e00000c6403003020402c1018080040940001b9110020440e0ba07503598000200c28000c04e103809007240d034030390880300303134950040c091540b17480046071051b036524202140c000e1880601e07501e40480300c184017666800440f66802040c201003460792080c400d560b1200300a05108004c00c020f480010041c4010700345080c441c841490921a142e00c90310000e20a03241c404046c00080303010524515024126100598007510000800750320340382070140946060602070f18207020fa40d0f280e1252034090b83d41201d040102c0c170100b2001401040706441c00c190400c002400e40c43c0c00030304c0600500d00700442d200d9032003120625040104101030381008150b901020800c1e0402c4050b0800e40014121301d0704007084c0784126201c0e0742001e519241032006000c140a11320011520007108036011b40642008a0280d002c1003041c041e44071014000c0c5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 879993615 1250 879992365 879992383
    0x3020d03080a0b0618060a0908060f060901150f0e19090f0b030604120507261201050f0a1208160f0303051b090103091103031b0f0f0d0807111f0509 65
    0x8480045103102e41010300400747c0141080a08100d092440007500355014007415005200391514140203242010600403008010b27448250416404a0051341c4181d0040400c90300501d10b03e840240243c0c503a0000f501c0b401d181b00c2c003510403c007200002403900b085600141503600120070910140031004c042503100c450480c2d0103090018001114803096108400600085214642420140126401030320100c80400c54030440c2000024040c8099004606514010602251002c50240d1107202142c0c4100c900e220b91b036200d0080032a070208200307a020603200b003c80c80e800d200c4000c180c2801c088480c491221000e801103031400c03021424130300a044214400d00200c0356014076140311340d801100140718040b019142c05000910351486076402f030004098004907403100c4030500d082c0041e507078102124a24491840c3d0720440c441d0428a4011400340048582400d001c8440d030354a56043e034180d0540c1c000d12803540203905901010428410190b9484038000c0c0081042c0c1d940d02911507583d840c10 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 879994865 1250 879993615 879993637
    0x10c1b0812040b0a111c08040204050901090c050103020a120903020a140a0f0b04030e03010e01150e09060106030c0c05010905010f11070b150d050703050d02060903030705120a0603020d03080a0b06 86
    0xb0055404d0031030184980000890071602181e000c00040c408200d030000da040880030025008005000c2545054082c1941045101c0020050083d0b40d0b40c43d10740e84d0320350f84200341c14550045402101c0d0380c05041d1607440d0049030f01c0c05000c800d005190007510340a04102c01c450302040005080355801e0300184040c1c4059014072400d0b004512900d07864a03a0320010422002c21048444803000f0ba1401e02800003840105800450703518424100d11814810940050307000c80220703820001a1100010b455046171001d0071300080d0000e81d100100d5814124503406001d9600b8420303040b0800005601484540c90070708820428200740c0740f407031102e42c1700f0b03044050305c003004a601041c040345045040005000340145104441011603494905003d060b5206840302d410000d003d010307050f0140251a4444101000786240d490a140003130054000c20b106001e01040d05c10010754031001550110010f550000d211403083c8a241c85d0081c0b20a10840b42400c2503402c00d00351403181c4c2005001d5407044100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 879996115 1250 879994865 879994867
    0x5060c09100f210204081006080706021216020f0a0f030606090b01050706111605060603060601020f07090b011404090209121c0318020402040b04081510060e010c1b0812040b 76
    0x1202c1a84100c100f2110120004550800000403100c0c4200005e060390090742c200864820303e400c44207824030703e069000d80190342000458a5054200d030b0111764031201101e100c0080d0390034034008100d6541d917a07240f0a4110340104000318105640414800403a4030a00060011584400080c8142c2d018070b065240828000c2c07155200151050700119214034070310360018104500c0f000843d46454850009031503e4001105108040c10103201d41c0394001420f000400d00311224400d2035070b07540828440d91804503601d100a4034503070b103d45501000040f206091645a603100c1600704001c0d48001a418842c00803441c00382c108610204036414220b0354081403010340e2400c0b400c140c1c00740030460460300350100c80081000044c0d41d584090400740803100c0c10662107030300f05040c1d02d1801020340206a0325490810820100101410451080e1015841e24030300c02902d43c0010b032005070f4100300080c120240c1401a0f42c056540154040480e12400212041e41c10742c8280c480c11072055010311184610 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 879997365 1250 879996115 879996137
    0x314060a0c1209240b0102010b060a0503161407080306030c0d052d010e03210609010b0c2b230d1112040308151815030a05060c09100f 59
    0x69a00009100d8010295050111030190b604e4500004e0450080d440a60380c2c0507403213803564244110300007041d064490b0391030050284406070080c0001030500340451008104004494402d10190303107410710603500d117903d480480c0703043c112030703001110840c0c041c0c40345c0d40f00702c0c0a91501c201512749a98000300034120013a956449491101c1450310202101c6400000203f2912024031500d2106098100596110040d441c4102c0c0e400f100c042290a54120401c1805142d0b0340f10a507481c11180c0b000c40072903892890f481e103141054840c00c1c660902e000c1d20b03c541d5804e041d0000c59802c04182c3e41d502c0355040b03220903003828085d0702450500115184d040c40001c01d10350899000306604040203032294100020340185d072042e180100c90840c000340407001031207a800318091b42d41c000e240048a51101603100b4413642d900010340106160281c03100c0307a882c0b4189440c24001103080c560007805a1f88a80303031240241d1100d2307010490042c00b0785241b2a15000e65441002d90103a688560707035070071038045 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 879998615 1250 879997365 879997397
    0xb04110109080604080703020c01020318040b040f021305150c0318012102120601030c0c0b060a0801060b032205120a051b010f2a080a09020a0314060a0c 67
    0x48209118906008421002140940c0c0070400ca0740710394881d24100e640c455003171600a00f00540c0f086a141036500c00e0081c120380001c0c02417902d408810666000070195074000008010f4402000e14855052002401c050199803202c00314060b0380381540e03c035901901c0c83d148495a4400c60140210540060000c000d217120400b0000a0800051405190b0b180d1182d0041a50b60001400c2182c581d500081c21000140f00388022940603000342020094089480000303014000325110092680a101000821643e40c1200c250080c080482c000c01c5010b85031a4200010f510980302000e031351152089155107064901a0402440d034400040c060f00b603880c2d01500d4042d0001c1c00c2007030601c4018080f02a03016456221198403071161000460b00002106408040701d01c0f1401311b180920f0010290b50700c0304501c2d184c1a11150b45880c00c21400e6403284c00a100904804000030343c48514400c1c00006d00100c03a00c11103950803800c06441c61070322280681c070115100b50030070f0804905140080310f0307c0703 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 879999865 1250 879998615 879998633
    0x80303010506040320121e0304060c0303020a020708030406020a031209020d15110d09153c090308010f08070806040206070201051306081b1303170d090c0905060603040b04 75
    0xc442c1c60316034170b50700310070720018145c480340c1481c82c841c0380d11030a40711f001c21500c0c04918540340c00d64405503181908044008101e134402240150601d43c00190350300c1c0c003030310800c010b20003040c50105503a1100d40b02c2e48000d4a54541800960000d0540000c03020421840e2050200c442d0703008142d1f00f0b010740159220407400c03420340301c40c0c1551641c6025903d40d000d002c0005045204001d80006800c40f00b6250885001c02c0a082c0018000c1c50000405001202402d10400d00095024001c0305050b850300958040c0c0b8516112040c01414200601f081503004034850703043e102e101e041080f0154030b50340220750f20035661286050580c4640086405420448000d10f40c9a0062500e6807030480300c0620301c0e803044803a511140000d1140f400f0448010701d80f09e035038108031005107045460030f034052104040c100e59500000e071410440100d00d860a6045400300c40041c1c2802000f0700c0084028100382d20030f01000e21030100c18034148070006000c2e02d07022007241c0c03045501c032501101607116900d4034050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 880001115 1250 879999865 879999893
    0x70b03060a060e240d050901090c09150305030f0306040e0d09060c080705240c07023f0a060b091909111305100503070602151b0c010212010803030105060403 69
    0x215052000e07507241d003c1d0703860000d10813001c0e0b403140340d4030818258010100c0d0b60041040010b80d2400e2000c4000a00398600c1c03000715001500042105d2403803043d800b0342014140e100400d54030000403031400c921400d0000e140b146c2c00448080228800070f80883d5121841c070410740000030b01410f010302c165070242e00c440031080d002300a01c0d801d004181e61102d103030401449400c0301d1165800d10401c48400c003545100d9020b4090814942000d50b1680480d035550100210b010ba1034903076100c11401d64440c4002408010f07494840c0408100b00341207111313210308801000791501810207140c510300f42815039841b401440181c0040f086070641e90303c50002050341c908100c03442640c0820009503543c3c0e4180807104000641000242070500a484180100190b40141c2c002d8102d80c00811406401080806184070180107a40f1a030781c0e100140c3c5204aa4040d130f1144020300416152800e46055000e8074200300c00c400c4c554920317601d61105c95a03a01003441550b9020000300f1007400090f034807a108540d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 880002365 1250 880001115 880001119
    0x52d0a0203100909080702030705010516020d050a0b0f040b0c0301031101050d110c070906080109020105031f090c0806030d031a010c05070302060f0c06070c030f08060f03060a0509070b03060a060e 86
    0x11034a0b83e0030350303040c1c84400c44c0c00e0b81e501901242003815858244480344c001c09003420403514051000402122040d101200680304901d40c000400a01006001051b034031540501d02003110710300060f0b010941c800c16101503541c0c101c007000040d04010020201c90580c0d4004012100c990310303240045400782e101002d0840d07074540b0741d0b03441d04080d9110b002804800c1d42550240c0915800d041020044650680c0030300b200ba03050600440150b41c208080b26004191001103921100c5031150445820300c1c564401800c81d4a808591206d159110a074140190022401c5c3d03901c007001a6400c40980381400584407441d4482d2280d041158003804a00b091144954180c07821169241c0008205401c203800e0401041c0d400907402240843c14400c02d40d0240380382c100480300105c152001480c0c03903c0c6034a010300f030003a46004145656240b29090310007500c010100d135118070b09014001d0144c4410359640340c07284107900700464003c0d03a003400e8130310404020381700e240300c80c3c500074048a100c101d08403866 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 880003615 1250 880002365 880002391
    0x1403070806120a0b0c0315011e0e1807020c01082a3402030c0306040302191401051905070309080904021b060112030806010f0c0b0c0903030706052d0a0203 68
    0x80005044c00d0070345100312824801c0341d4503443d00c404081000700128521504014a0328001303a00c019100c00f0308030f0007048503c0e144845003e02c5010404409111030003807013050f450400c10000d44e038001040a00b11b8400e03a00d10a180d101c01094220181c160b81840801c652024017286200c002c41000c1c280000c0146400c0ca83e11201c104507040d000740e02d804091603d0845e003444030550404012464a01da8260018801407409480003911207003420140780340501c00c80b10f1001480f21140e5800c4102c04048000c0100d401d00c41c030010048032501c0b4016007200e017020f00196445010384035a011194002c00c2e40c2d40780418000c100703c001e500c20305800030840180c000004055504002c018043c0005440c0080504150306014081000041c5031504100002500010300e9030700580e070b42002a48a2480e601c10313243c0805d20156030240111164051201280007000e20150b43c0080e1b0107850400c0200c040c080c23081d11003400010100000c1c9103202180004184d041d85994019507110000110030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 880004865 1250 880003615 880003633
    0x20c0619020d0c0314070504030b0115090504060e040318140621161206060f12060e071d09091f060807030f1406090c01030c020a0c090606140307080612 67
    0x400484840e26034100000b07170f0b41e22542c42c0151010b0b02042c4c1010480c00c0c4913082c01d01d03568a000d00000140100400041c01070b29501e0881e001d85003003005403800030000e10031291508200d085014040b18150000f800103640a00c44002a140c60000d50340c080324502c5170040440140700c1070360322840a21104d00900c0500c3307008032041c00440c1d80602c0c954145031281c19011500244510186400c1c1108139223131510070011550001098400c501041c2000445000100f4074a8001d25207540540c00441001c0104090b03594081d504841c020302d0015000103941d28031050040d210000c0701d4060701a40074860581800403c60841d862103e40d42c00d002c6841600c81c0300f5070f402c1028170b034800c070342043c0402140c600308100c45410b40b00c0064528010081ca1420a084660354080608002d0506030b507606240c40c40c0e4400e011b41507040b6007140e104541541d0b920b2030103004105a01c60000002c85a003c1c48003001e01c42c42c100d81c040c0340c1560b52917101b61940010892252480c1030318003294400c225030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 880006115 1250 880004865 880004887
    0xb0d150501300507020304062c010e1212030601020708060c030f060a0f060f030b0906150c031e070501060b070c0312050d18020109080a08270307080609010b0103020c061902 76
    0x10343d601c188180d60240d0703200c2d03251210151407400680700c00300a944000f6071203141074580c811100382a0b4000d1908002503980f034404507000c0c1407014201c404600842c200d007418485800000c0d030140100380d00311001c5a0f40ca1440c5a210030302a90b0700059843c0410210f40c40c0d0040307015440e00260014044160340759110010701111603150300042c04200050302d82e01c02d05070544108042d4a1090b142c040003485e01d01d0008101d22a00314004005032400b03e410039401c40308000352551850804456405282403031044801c1d500141c604803040e60070060b01044507088030040c2d07100c09a10020492419055540d111504c01c007000a44040150070b0059100d01403660007031821030045a241a03010360384500004001202c1d5400000c156405221b06000040c8070000300c070311a80801d4410706400181c0c04054424401b00803880e0740c1403040c1103010442a0700404c04c1c0d0700548084008010400049005605078015400c500d4800d0300113000090445110148204403600028401840c0501400b1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 880007365 1250 880006115 880006121
    0x90f191b080a0c0e070f0804030522030b07180b09030313060e0915010f030b0d081b1504020d1218090c0801140d0201180509010b0d15050130 62
    0x4841c5109a002a040c541400300142c5080d003d01038001d491146490070103c09000f80c5c41d46190f51042284d484005424140b0903002c1d80c60a003d940b403003025880c4080c0344941e80700d00f00c0c081961f071384028901081405000391000001d402c900c0250203101850034420b03002e02e0b0030a507107060301070000b00921188255404100740160444e40c8038091266070704030034030601040c02400c2c00d40804100c08490410ba80013441c1e0441881c2c4c51401048490520011480306442004005d00340138003c22422103180500c01010201d41480e0101c2e410040300a00286d016401503802075002440c8840c00310105911034001021358a00b1306000032120803080e050695681c05601c9108034503600c241c2d0b100c0f1650710807100d9006013000c1314a003000e1018040003900c614041c4038000e0500481000041c0c0c4418010300713141c01044000e1000351300e5a950f420050709a07006020303c1a0140c9841a06100440c040700c852040e20f2060351107102c400c0e0711100c809407070440e00040f501e1517000c3c19101210404140 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 880008615 1250 880007365 880007369
    0x604171c050a0b04090506060402210f0f1005010e0d060e0a050c0f0105070b130f053a021f0b061314150a1b140601030308090f191b 58
    0x6040001c0d203140881503801103400300c0700d0b80d0384210b080014000118400280c4160440021180142d480d038034095480964101084503105401c0804100040115043d00b860300c074184c0e401100710180d4a00051f1219880c0600946002c20282c601005140c1010712080d6181c6100b09000074501c0140400c641c07801032000d40071125540807030000c22060030143c0c1030000d81442030800905007403071981d41c0c8600c010014103090740000090018018090100400e912442e080801d0f01c0d1248071078030500100b86142d100580001c112040a401a42c1001c0700384d2760f8420b0300d580640400000ae8400b0318400e52110070f45c1090640714546d0301c5d0300781d40f0000140f99403040590301048851401620500e080c810720321003480388080400d20b03541702008008540940d5580d203003951012020b21414000000d05000280200003941159030800f400081c9213416079001c0d4503920754556600304100d03918590395481108a400c54840d0446080b00500708007103843c4034070a9110401c0071290003503a4243c5907 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 880009865 1250 880008615 880008667
    0xf0618080a0b07140a0c140a200306010b04050907030504170a030204090509010203040c03081c06030b06030606040513020f031507050d0f0c0e01050d06080706111e060417 75
    0x103100c4501c1e0028030b5040c032140c84800386410017000100151580c124100d010b0705841750000c00c60342804080c041d1400d6194003084040d441d10304845480d100405a00b81c29009201d02e03c0041003110400c0c00740c5040359401070252800e940d07000d8048000d040080c2c03048400001e5844003003203000740b00c40940400c074045c0d60016141c03032412690001b50380e4080c0c103c800c0c80e441041840f01082c126a61442a44c0e041074046030351310110940040ea0741e50040d640e2096a1420381c0110411446041190091030b04030101d52843c1c07140e00421003202c00a44004141a080d02909801400d0400a03890707810780050a841c0c101a00303600c4516528421070700500024000500101c98865501c903281c200c842d00c0c1c800704011089504064003480a043c00a4144000490807401069050300200054100f000c1659461a078409015000c070003d601000c0e1a070244503665540d0383c1c030030590300406800d14801008948c0340c47c1c440385032007000d41408451125007041038002078468150910344842070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 880011115 1250 880009865 880009883
    0x609020301180b0d212f06091605040b03030702031c1103030103172d04091d0307030c02120a03020c120f0d0809010b15090108060a0f0618080a 63
    0x961201c070812200c0f0241000d1181e0303003040042c8041103e0750425160a40d500ea411507003072140d844251a88a02d4010802580040c0556480386451191012080100e40011604151140303801075813a0301902c58107181240301a10100118901508400080382d400341c152032508c0b4031030300424140307165020821034070b0b080384140c990010750205449070700c0303103100f0b010b54115410360b039a2103005074004c2c585104c894000705503550307990039110a110a01d010081ba1803e10000710740d4500c3c46401c240b042900d0f241c0391040d00c2426110300e5036000e04c207140b440080d51414003142da003550701c5440e007041aa0000c0c0c140b60b070031186031000c2180b004000d0007500205000c040000c08c0040c0bd002c0b01c0310511917a00070f02d00740100070000081c1c480f0340d101c1c1c509040d06a5039628a000e1700406101c21025400105520080f00341820840101038804081c1d90f11000382d92180244850480303680b24102107105490410400c02e0312903541c41100317065425520340c2080c0c1c0d5070083c43c90000100c1060b500706003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 880012365 1250 880011115 880011149
    0xf0c051005060f09160309060605030d02160b090a0b0d02090607080c010606050703020a02010c150c170c16080a0302160302011a09010f050603090304090501060c110103060b1c0609020301 82
    0x900a4440e0f46900e41c11038183e10f9925241d00c6030781e60500d80324240d000340b58440c1425800c01140c2c1d04080f0141601404803020240c0d146002503030b65120312941c0c8005040b544021480c81003090880e80150805171a040b1058540381c60510a43e100e000501c84840d400e01c44007015598440080c0301050150031401c6d120580344590500311082e5511140510804000000020f03801140c521980e940908003040d4003c06420410031301d0302403050840c405440e1140e10020b4940000c40d402c590040e012804010b0b07620000300d445240f150b05c1d0302c0021058008691000902101d00a00402c007462802509058100200c01c030045441d210440250351a01500c02c0c5484c07072000d85e101034810480c0c00445c80e525101c1444818045800340a01400340080010500d007002c1085074024111650200165079595000410710804c0079012524100360040020140d8800d0160105035034403494460718200c204082c0d21858119007000404081d00c4203c0056010000d04c0614001c01d840107890203030035 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 880013615 1250 880012365 880012369
    0x130e06010206040218070e03010f0204080114010509011502031615050f0c0f0f09180711010507090b03180607091a0c0a1b0e04050d1d100f0c05100506 66
    0x141004009a045501803800c00c005030341c03a09401400000040d130b030201d13951140f0f0b204841d08441c1c042e14a82540c04e111a034820307030b80198001c1084032034010082010158058a00110714800c0c800c3e00e0340041c0701c00040c4004010740d0340b0840d480c086801100c0c54035200f000c0320150641224003d0300c01d11f210507404254901140209035003e85c40600581c2245000e0b00d82c12000d0082e109440c0c00f01101091404c1c204581c0001c0300c0303a50070018100c841c1170090200c00501d092044911400041400c018489105014010b2500511240d1a902c0b0410704082c2d4400250300001c041d00d80082c1039221250003c03c0c1484940c0c061006a03440500f070a003031594040800481081c00d03850281c04020740d95181b1f00c0801c1001216506c000d20b0001c29850070401c90054201c0d40018002e040e11130184400c010000404290410306500d48400480800850000f04a2664100b60b000945048031042d00e074030440304058145024280100700c0e5405456903407400b41e080c0140e20303d140d62201480546c0c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 880014865 1250 880013615 880013639
    0x31f030804140904030c060209060f040f0518070806041509140f0105060c0307020d031e080115092301020f10060320130e1216140d0507080705070b13 66
    0x200b409442010990900c2e1750024080810303081c014003110b40c04502001d482c0d4600f000c40d18074010300950283c4640d00d9016120312000e06100d0907115219500f000114804000c84035413041c0d40c6625010241d503240d00c28000581600c24202459003330203140410544550b01c202c45000030782000c107126520340883c600761055410f8103c10300c54841030110b454524030010440c0e6840e40d054802250f090720300d280c20350f4000224454110380c0e0980103070f8030f44401da201017100d04803207804038107441c3c0100c0755505682040050149842d02c561010042a010f40401c103030084440c41031044601701c85503230015030f0411b00140c124400c01901e9581c2001480101e0a0b86a901d03511a40d0b01e000f885c003808001510030702c516600307200003501c9552501c2690401e0081da0785491403884016038030003c07081400c0304406288404c4800240da2094910070404c0041d1084c5904543e858803850a051902c81401a81111340700b10342d6031245440104207100043c000d010b0f401d00d840c1e104014a410980c0303240d42 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 880016115 1250 880014865 880014899
    0x9090604020f12031b011b05180a0b04120f062d0608071206090803010303050301053a0221030910020607020a150b0d0818040207080a05031f030804 65
    0x2ca843e20812503801e1a8000c02140c50380031002e20034241c2103a5501059014000e89505080303003058044c1c0c05616150090000d10082402480030151544850200180c2c00300a00441001010501043c4549142500c0700004e19024015442d1085900e40da0201980c0c0030654156040d07880054440c481c0c000304103641c6c0c0c1641080801e2011508254015603035203064422301800300b0118841c1c00602105502055000da04040c0c1560740750303140c1c1400342050307000303128983c00345a2049c80084591528885202002c1c96035690140d8641c031356102d40e50240c1d000509981c0038101811074601c8608900140500c1003a500155441d0000201004141050b098141c01550020010400119400b24494210740e80c48640e801c2c0712003644860300300403c0154101600320100298003824000c1e11005020489082c0c0d12034400b00c000102440207900800b940280100000c0c40150507040c002c0000d55807001c208444c2400700029001c0418070441c580d803065030044400942072140425003020440 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 880017365 1250 880016115 880016119
    0xa03060c1d0d060b1201050406020a0909020c3309010c02010c052d0f0a0908010f090c030609061515080601031a01110712050c12060103080403140c09090604020f 71
    0x81540c21601265080030b003041c00a0100d035032202d140750140c1d1502440c14003041100000c00c00c40c03070940b402d640258450380841d40440c8003400d000840c0c0100f8021200b52014a4000d0420125840c035100c08269030180b00c4002c1805851755101c4d10051400500d00c100280000468047c0e0150801707401c541c1411401030810800b00681c00c103d0300c1c101e6181203420361003001710151041441103c02c403406840c4c011020004009131a1456690002c4440107581c0c294008101020320b42800b8011110382d008010101900120300300040351460b88043c0b4214041e46001c200101340c0010750b00400513a80048503d800c04036800c04540b90320070480c41d4040400c2c28104207000210000c8001703100c0140800f810800c6500803951108418041d4500420604454050b01e1560346410f9480701c484581c82d03406030842410310003108400140c440c0c12690880240b81ca001d0842c0c03610440003a80a122403210300c600248900161924a003491046040350042c0007070b81001e00c10444118241010f840c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 880018615 1250 880017365 880017407
    0xb0402030c041a12040f0c0506032e0f030506010f14011d0d050d1211030601080106140f0a08010503100603020918120706020a090618030b040f020a03060c 68
    0x1c01c0c1c0c410100202d5007980c0315001c0d01c0b48206a2807000703a689118a84c401c000742041c5000740020007804c64038100100d4401d8109444180e115400d01406020480303180d582e400401c100d80400c00303802070510b40074840c18801d03101c03415140c0104c009220003a500450301a40b0600c01008410750a0b123804029002842079801040000c1000074015001394041000981d0300541a450503550f01a288141e954031005440034603a40e030030068048640024a440c209060075402041400000b040f03d2040005845404141c0d09059089071201a40140c030a0400340410200000510b000701900c05030101d503982d26099030501d4241070400c035003442103020303643c10007a0500040e0344080d12035602060030140b108101c540d441245281c42d20a2011180d4290001010418480140c0007462081c4454442c1a0780559400d0102d40618150301c041c8000c0c521078034148006407003c010b05030031500441030800c0c1900740750005080c0704000d034000c892b4240d842c500c90302e4003034001c104a035140002ea12a0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 880019865 1250 880018615 880018621
    0xd021207050a03030f0b0a06120b0d121b05031315081603022a15060901180203041a0a06060311130b0306030f0604140618150c0d09030903060b040203 66
    0x40c079901c40314104002d0031306844041c1d2120b05416a4002c140f07481c4c0c02061141402d070f8408004e8154074455501b0140d203828004200d0301070400c1c001c80c0c1d000a6101140c4028015080390455080020520703d0008220350b04072003020800030806001c44101540c8000d040c41d10f403128040030381d10b98a400c401403000d518104500400c891400d0140744049050250f40c85040402290303ca007203581c2000f00d524107a81c511510610001082441c131100464180110303101d84007000300c1c02c3c20921614000358540240c59141940940103141c1051054029550000e0b260360141e50004045500140b40366494408100307482c0e05000700b031007515040c6131684c54001c1030425408401801d000e8900b4a004c00408221a610100300022422402009803069410f061074542c0010389950600c0166200368008580112480c000c440c0c0680c40c05002803c41c0e468a00001e84c040c8030051401c54402e90600c0060361410742402510245840703aa9106172042c10f40c50000203c1c0e5003d66190700440c410700c10 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 880021115 1250 880019865 880019873
    0x303021b0a0b19050c0304030605010906080109020d030516060507051e03161404080106031401111c0c031401121509022803060f0c0219080406111e0d021207 69
    0x880ba075491a1010003c00c0d9441ca407020f54140c0b003085c0001c26548170004000003404190340c4054161030070304600344089a80d4510181c280c840d04200658010180d026042c0024003410007040410804168402400389a8032108101d0303008071035031400b0640000e0a0105200c21104541c8005078591000c1d0460070461402290361000f0400c1e8010b000c6000c20640e11a01711405071001085004020f000140e100e203000d2840510b0f02c00d00030b045600300000e43d51a180040e00f6580e91400701c441030448041c1400d5035034090300320304900c14203143d0742d09510461040b0140700340340a03015442c18940400c006240c00b0300000011024203851300d14180000d00142d440400c60b00010010f0344140359591400c055180c00381e019680000c21091628880b110b07010507907040801d2491725902628800c0d034807a0301d060f007005a10340b00200819010007050000740d00940b0703071842c29000c15089454904c40040409200c243c0020344840581c0103584c81d4076030541c1042000701a001d40302c400303800c04200d559 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 880022365 1250 880021115 880021117
    0x5100338100918060e0106020c130b151602090906070e0f03030d09080c0a151406090604020f0403081308010c020f0a030e120a060b0a14090408220303021b0a0b 70
    0x286003112003249607002d040359200d400520140400c9000c5c083c0d00d5a40f1000a0b66451006507403900810345072402e5191110f041c404c4440021010b410f0b9400e000c890054400b065106d0a4004145140201039401584980901030f2003040500d008001ba4104540040c11140c45084e01d54883e80642c000d600da41d0320301000f135888100d100100800c0000b96454881458080c2c1803000200c0c2c859490141300f445101ca4440304882c040750803c0108800311040040d1840c0111402da400c15104c2e800f10f8880d0038503900a081a2444411039030829440f562400e00e00d5019209440c0d0410fa9140248600d2000f0b12403400245071900041c03007050706052081d511002001c0001e814091094015101a2610140c80c401b82122806543c00e2541c1840c0620061100b503041ca80110340f2580701062030644082071100411006009484558644d0f0f0b41040b40c0d44881e610504480300c40c0840304124040b00740c02c070040c40c481e0300a0101c503182e049014241d5100004200c3c41150905410044440850 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 880023615 1250 880022365 880022369
    0x90906080c0d0302070302150a030515031e0c040609020705070f060206150103140103080c0c01020105010b1b0c0604030804090506040c0e2e0e011e09051003381009 72
    0x1075072040302c07a2160b09059003002d100f644041e400004060040d1140074051000741008207007138500b00107580f900294802050516043c50350941c0c041d0018202c103a101042487d0810030a0702115180082c0c0000308003581e505500c100301150300420f03070304100502401000c0c0589088410303400a1361500d03034025034500010b0300c85c0311040c03100100d1603080d900c6900040740b080c600001400003560750785001c030040da100c00703000e0845004501ca030309200c1d031040c001c02d4101c0d08842007460501c40034a180d034103070491309024050340d031013a0b80e03506825131503e5010b48000d40c061074003182c031a86020258010340780014112807180e80341143d00200b450300301840c10b0341468140d6450f07407480800b0151041d000e07040303400b6415003139003010602d0040341c1c4400c0041303544100380d850109203a42032050400384d00c1c81d440b080020038944d03030050020f8145001c45040c450441d00d03010465541e07030000346070350100c0f88100b402030740020384091740440090310380303240464015a00304050f80c1c1703a080018040b01440c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 880024865 1250 880023615 880023619
    0x60803030f0c1602030a080c010e06100902130e090a0201020f03070201051b010b1513050a0f0b0f0f160317150616150c111c0c1e060c090906080c 64
    0xc294a001400b00701c850f00c94007980501140e17038200b102d0515180315001280010025800d000b50b6010f801004102d9601844e10501414a0303641010300c2003002c0d4009001c4425840e0340c002001407940c1007060b06500600e0703004080c00c90035100380002030404554200d41c15440e80100940700060341c3c0002121210341e5105008198103018481203409050544020742c3c2c011098000c014441c1c554200518485030550010320b01d140e0781c1c0080c13001a400340c2c410302801042d480004c12a000411008000d4005040346181c503010441042c03e107103411041d0002e008440f40e08443c4e04042d003150203243c04600c450a14606031070103060511011801c03201580c003800000c907185201030509032100a003030790312449030312182c6c0003000c1440050400d5104171002450080107003140b11800700741e0b510013924400c0e401600304000030703050b03038040b4218800b00c4100d0710074561b580400307007001e40700c02046110f81000310301028040d0000341103100381d4001a20f50f61400200b002100c1d0b000443d40b89020302 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 880026115 1250 880024865 880024867
    0x1101091e0324050a1509060b160611040608090d0e1f140c100606050702011b0f0206040902180406081b0f041b0338120d0302070501060803030f0c 64
    0x100581c0c030100055144462060781070205110504103645c0180c07030f5507400541c1d20a200c0380d40d03001c0007044d140790340701e03002514501f0820071040d01488000e0700b0106000b0080450b800743e111300c448041d644030f035009070001035025060180c103200a00c841400c94007145421410b01650031300182d139a00794202a41407894100c1040546a4090802e40070f9031391080c208203403103480820f8155150040107036803e00c4075280c07a0740820900d01400560755040d07010384d00c1c1070b01c040030300c0261885c0c0a4049403d907a101920184040140d0394a00100082c00c0c5008001d80c41c2c0040c0800c1d620742d0840d01e04081d12450519a09020307030039001800a40888017800d88481c0612102d003ca05d04400245801d40c005040035101c0d403600f06503100c0420120007030b0b9420800e00d420800301242d070b40076a4004002c0c0d8071100035402010b2003204001070031800700a200c800348c005540e440c01d00c1c1100081c0c642010a170041940800d02000f031080400620501c405503245181550407a40c42d10b500a0a0180b8084 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 880027365 1250 880026115 880026143
    0x810050d0213020309010f0204060908150103030e19030f030c0506090609031c201207030207020f061b0d08010501110616110a1205030f06181503100501031101091e03 73
    0x42504400725802c0b101c0384c1151b955413586802004007202d0b0180f40018030dd20082e02444c00c100c101200d041b6900741d500e020340c0c42011010480404030140c01c0c443e09540c0d42401001141d001c0403103a000034401d440380303141f404151070f0940c100040240740e00c04a4003d00104100c0d09800300c00c07554403c40710410740d060609201421002840c440d03048040a04902c244480d203401e085009146800304c411a2881300e65507004200c0a03841402d030025088a03c403400c95031107003808006040e001444004007915145045d50b032501e402000030030180000c0d42000100301650b040101c00c11107101d01405820303640383c03404804041342041c51144040102800c01c0700c010041c01d00ca040d031060740c04800c00d441503110290040883d04140d411400e10380b9010042006803070020507010f401c00d40c40c18401070301e64655820b0140e0306000081c840d01400382c014103070188030840c41014003031131140140060924103c0001000d00c0e9094000384054481e91031608000382ca0f40c1c0461048076400090011070803 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 880028615 1250 880027365 880027381
    0xb01140d021003090f0804082109040c05040905041a070323060102031215010e060703080a0b060c010c030204030b0604270201260a270201031a030d0810050d02130203 73
    0x444110009091701c2d03d17413061070341080040801403007260a04002c64040d1603036080e440341c03c1d07503440c2c01c0e0410203d002c001508003810300f6082103108003000e041c950305040d60340c4125015070304111401c80702c403480c610320701c0f882001022246410008518040140481c005144240c81c3c1c44015224980d0403d403000400c0e40c0e00c20412580b81380d1002040000600f000710102104440d044000c0d0b0110740c00c108000d1441c03d0901c00e4440c0d0b41d0f007650b03c10b05d03203444403400e400060180301000d0b0b40011082050900e02c18090140b040c59014513600107030344610b98100941c885402400300351165041583c4001d40203030a641103d003107050301c00084030603111440180e0319000414180805c1e00034120081803400344440e0010b01c0f0f0080d51500340010501003d0030300603001c4c241c18191403042d001071200d0255100c5da12074070010b0104071200b41d00f4010240007034070b040a503807034040c0000c1c0c00e2400c1140306125100c0c5e1500420040d602d40c50404481d50001c8c0c0a502c030000110725041d40440022201 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 880029865 1250 880028615 880028621
    0xc030b2809140106090803031b031009020c0309270f0a1e090302100903120c0c0204020304080304020a080109020d120509091f08030f1e04030b130b01140d021003 71
    0x9101d4140200240d540c03811811030405401d2103404003082d141d1000051042021084902c20a202d0382884100300350740e071170207071183c0010704a401c44d070468501c0031030440f503940f00411000408100071a1610075403410407041075a00d1090440819401107000c0c581c2c141c455940d07410042070381c61440360382e5612031385000074039001007500036526a4509201660303106138451010b8600990940c1d80114002550748103450071500e00800103844042d80010486150780901700f80412498004503014141d00000e05a803c142e409549864000003800118680320030000b004144030b0000740150102e6400003407060820210142c1041c1031920446c13500d0788100126170051000074100001410312107012030400c100c2151000c81d110a4590209003003038004203a41d010100340548a29161a0060044100414909000e0004820301c80440004e180d0074443d4402c00d140e401132210400b407410004044170040c0e00424034510702903040d00482c3c4454550545541d0151000043c8142c5100d0450003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 880031115 1250 880029865 880029869
    0x20603090a201513060f02070504060e010e0912190c020d15154202030a021b030a060510150201051006030c0206041506170c040c030b28 60
    0x7a4142010007401c2e881d1120b10300c5541c0c48054801602c003520200403040306106180480d8103603501e00e0010000075205000464910900d072042d2103000d030341c441c0071409488841d00306c45035030300380030b4010b00442c50383e546000e40c84200d017130040400c81d010400d00a00c81c4174140d6900080c548030301450380700500401d1089001c69014054140316605806c1c680c0040c42510300e20560756080550381210891004041c3c0c00303641800194010f65150309102c8190100404004207115800141c0c3d020004d20038081d2a85021440d0060744d640d0350003c1700282083c082081c4811304100000340750000341c500003401c0c5c000c43d500c2200083c290301c40e00140a4606c0c0c0e5540041e03240c0c2002161007100690641002e07000e011400d005100d40b80d02c0382d80c290155002241c9070350060b0b01900020b00443c0c846400d00e55120040da500240f815290803840c600c0408080e0801765940c844260009541001d200d2140c0b50060352400b00b003000e0b454800161070145110202140c906440e403804880b082400007400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 880032365 1250 880031115 880031123
    0x2090703111308010516260a110c0d08090304030803061c0618060f02090303190c0b0115081f0501030207060b0a031b080a1e2310180f020603090a 64
    0x3844540e81d018141c0070301011281c2004440300381c10108482809040040602c5911600395060030503a8400030385525001494590f00395102d90203030300307490800c0d001401c0002a080140c0040cbc20081ea0180000101501c00d44003548200000c1010405403001d03660820310403102c0d441d5180e00d1101c200d90302c042c40e200103001c01d4501303412001b554541d80b8009a4140c4142003d1080400512000040f406001260364154000700301d035003840e1181c05221039030351285041c00f04a101190b180c0406d4031100b600b00c00201c1072020411070360b003500034a84640c000243c0241085102c45182c4504070305400b4401d090500d600400d481e000c200403900701d0315441c0320241c04070003400e581c0d08240720740301600703080044040717101000070980030f40100b02c03001c6040d044508070079914010b00d0201c503100d00b140020384800080c4000e1820000c0c031a0420204195100024098480c24042e0070b001c49040384d880042c0410202814000261003900a02c49290100c0e015a26175075189021401c003030800300018 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 880033615 1250 880032365 880032397
    0x12020a020a060e1005040e27011b03050a0b030706050309070314061b04080322081504030f170a020f040503120a14040b030f0a0b0d05010203060f0a030209070311 71
    0x208049500901401e420710040702e41c4c00500c03000000c140d407075101e1402841c910000c82ca000036440c400c080d40e91031280911b88a40d041d01401d046109003116404a0001150b021080b14182410303403600819820160810701000f1303000180001941e50b110610070f04d028446c0200000711a040140200700003150007034028480826079421164544608a40c00c040d01180103c43c00c10000b1032000752425960780c007000f94034100311604414001d151800c0c1008424080c01d002041611050045c000c100a003210310001e5803c0902e03000d0402030b5400031040821040120300a401080c2101c041d4200104100050703441c911007500d900c0c0c2c1c0c440d035000241c061060800038001206540000c0000c41d500e503866440c4401000240c0085102d18440d1009290060000c1910001150301503030b0031a407000720006460700c04402041d0105102c41c003c0e501b0b80d5002c4200422420706030980e031041c0e481115079204a5045900140400f0005401c00e0105582d540c5918001e200d4041203c010220900f100c0c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 880034865 1250 880033615 880033619
    0x702011107030e0a15021b0d0f0515090102090f12160f080105011d01060e0d020a180b0414070c1109190c09080c0609060d2a02060402030a12020a020a 66
    0x150000d900d10010343c4c0590020500012007950f00c0a0440c2803403d25405008246406907680c0ca556852504259000c0400040b0138002031000c0d20384c0c04c0045c03045002d0b115405000862000b664001003c81c03031141d004004280359036403044004040c030f0804660b80c0418042c0d00d40d40c01d14000ca045540c45000020a5001c180ca140a4122904841080009009681e04d0303003118100c0c190f55034440c01a8060050061151030b006110741c08400c0005001c00c1e84c091500d8001619283d1030340c0c000c070205c6000380c1d0388142040050142e440030703d109481c184200c52104485407d40e440c010000c104000d1404490000c02034011011107207010020215078485c2014a01e2000a003c0c40140c2c0164506d0160400c900a0140000404460402000e00030030f01b15002404026400390030226400f020400c4175502c00c044512913001e031a445209070380943c98803d000d10401000001d01030007994001001c200043c0e0340062400100c83d0b00a00107110303403170302030b0081c2c0c50440c3c000d900a501c20450000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 880035971 1106 880034865 880034867
    0xb01051c02030706120906060b04150509060412052109041805060c22140a062a0606030b09010f0506150f2d07021504120b070201110703 60
    0x422842d1b110b0341d03018204c030f0b142e03040030700309800c00b203010b00000c1c00348160152002583d0400d00d0ae0001001e00056140c0101c0c41003900e056910401e22040207400d004d011030703515074002d05042d06e8081107448070183c2c00506080303004c0e900d0200000d922580852600251035000005020361381c0b9004003520082e4044101d903107140c0c840000300807500b00c004500741d0090012102d6140b4088180c0d04112072990143e104d54200001e041010003816104601007a2080780e8601c0c00340250700b18982007002d403155900c0a8007440043c0200000343c1410340094080b007640301001c01c41c964901042000788030782d4414901c02c4c0704041c01141025521100100300d442c00300c0c0c0ca80c495100d010000d102100600400f40500c1e820085401000c60070900300e140400300b03103581103500345030611381c1c0d025000b0044440508072900240c08258203d000b03520003814040141111a0394803404d0030 = true := by decide +kernel

theorem cover : BRFrame.Cov 879856115 880035971 := by
  have h0 := BRFrame.cov_init 879856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 879856115 ≤ n) (h2 : n < 880035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
