-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0872
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:19:21.970748+00:00
-- url     : https://prove2.me/submissions/39fd28c0-c143-432f-b562-466ab1706aca

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 156654676 ≤ n < 156834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 156655926 1250 156654676 156654689
    0x30c010c080906150117151008100603240e0414030906030103030305060a03120203040f0e07050912010209040606030b0f01110309041508061e01090509030a0503060d061a03010b0415 80
    0xb03141c900344c0380180d0340e118005150790038043c102c00c2008008401d13424a820516411648200403c01111040e00e00e0b200070340d000340d0404400f200901c00140030f60b10200704040074211513010140c3c8000c1499560306250070651541a0803000d100412480d01e400400b580f00600281d401d0800d5071000c03503d0303404148000303420962903001103115a00d60702e5442010b0750b0002001003940008040295584e800f91007104044180310000051138154226a03034000d82940d40c0b503901c0c1c0400e000801082400848c1c89142c2958200032910700d80d5914441c4100408581d100402c1005280c020001142d41030030201e0306000c5c00d1003803005821408801c4890f0241d040b100003c49504249454a400703201c0d0308034860510030101407000d004001c21604049023450800c036140d03030380c9608070304081e180213a81005159000b8441010314071701610141d64420300180a44003841c5103601e65801340c5180c001e0700f103100d25004940011504081c000c04026800689051050780361262150b0f15032a518401c19 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 156657176 1250 156655926 156655951
    0x30d05070f02041805060702030a0e0f1c0812010801060306060605120109110903030304150605010c0807020d0812180607020705090a090212120c15070507031d0d05030c010c080906 79
    0x203034107000c4010076802c130a07500642190503500c2c150300003a681c0e80c460035002002c9105802d00c540c2a10307085080240406000d095010100d110003407001e01315071301c10360449040c4014040411714513514031405000300500b0001041003465400c15504070b41c0350b0780092007080030400140345120f104048030f9045814003100024101d41d4030b40403c085000711084d4039414000002030005101e400c2102c1c10101c5240482080010351b1680151441c03000c41000418000d03080c805807000d841d04e00b0061034158040c7c16075501c0c280754140c0c103404040c000c03100003085044040b2501c980e00810450f00368401424001031540605000008840080c003c2a52841030f072151400c02c00c5440d49036412001031186412103008481908031503510745c1242c105100c142c4030323204900784802c403c0040036026000a4489926080c1503413022941901502d54189581c20307007034030702811611418410080c0c280681c4c061602c464069240700e0944008404500400203d60301b0310150342e07808a20741d90820340b01c4101 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 156658426 1250 156657176 156657191
    0x50a020606012d03020306090c04051305130218090f0105010503071e0f0b030412020a1205031314030d1503080a050d230103030e0d11011404051e030d05070f0204 71
    0x1840751000d41400340d441d080d09045440811540c03d45c0286018140c00c560304400e503a548000384c1414000c521400e90b22000090745e07105400f070315a10594020030b036076401c00c25a81040d00451034a14050103c0003816401c5002c0240c8044240814440d0114000003402a54503010000c0d99506140c001d507240d9402c40d8400c1412a100c8200e00b0f4000d1000c0102c61040c50b90340d5641c80002d400444043d1442c00c1240082c8220520120702d40d40c00750703404214452201c21190007110590401004e80c0d04654505198801140030114842421101100155505c00c20100508140e8410144200c400c41c00803405000160000d810742d034488100d407522a8481407100c4002c001303000c2400340100000b042105081d9640745140880f41030b070b4000c0e12004c0503000d0890512041c2c0c140d440c8003801800c090000f0017103070740c461003454940090050109041c141c5860029081011610740d0b40a92068440e43d1481383c2003d101e074650041032410f0113070414400b5100c41c550140c0c201c50080c03141d65076100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 156659676 1250 156658426 156658457
    0x10b0f1e01020321010611010501030b040623042009090703080304080409020a030207200a090209010207030503030c030405190b04030311071b08060615070b06011b050616050a02060601 81
    0x2510200340402c414005030100720302200341c004c5000e018010000d101007060000000c014015241280e03801905180c0c2581e490329040c0043c0201c8198103405141003646035030030598400c11a0059010f011644080e41e03000980100c00d04203a000309010300060710420803015000314080048035002100c2c0740c1d07203907500d05d8600f0052103150030040d1024404545903504650650140c100188503150307850860322000130412610300094405a84040d0801041c8620001500600305420041c0112600d50b9126500e15095070401c86011090301e0000c4200000d000301040321850382514000c1c224240303c0240c40f40510914010270180505440e120350000032540d00e008c071040f040d0442c030310099a05668182c41c124400760710800b1402c0c072a00c03021807807a207041850942025501c103080d80c40c0c042240d6400380300d800001e05240c10303c149818900c4450f00201503008450b48200050141c0b45013900e6804841201003182e007080090500c554800c054000607440c2d044072090070140c82c0e08644a0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 156660926 1250 156659676 156659683
    0x10906121716050d03110903060a09060b030d030b0406060302040806040807110607050105040507320303040506041d2d15060f131e0b0a110303010e09010b0f1e0102 72
    0x30030010420340b02035030240600a003c40d010401c00380e03e40d0140502402410f071a042c17030054107201c03a8950015070115a0709050740d880090326034410300c40401c0034443e00d00082d04000c6200c2d080d8020a8032410088528502841607802030113581c20114282801c00301659075811000b4402450030304001420313400c2c0501e8071082c1c000070342c4c02098103030780c0c00491903c24064001950111540c0c8030f503407404590111080c42c0340007804040031314181104a10b012008408400b00c0b08141c15000402c00841c2a80310350004001801c1000141810783c9800a144034406100400350180d03900104207840c0d00500c030b40c69200c00d41c1040e100b00040b5880d129100c210701268008080e174046000180740000302c0040024201614440c100c0524aa60364031112000803402d89406400c0c81010405000f040b00c0300c0040c0c00401c840740707803c0301501141800301d0300c3e69200fa0089001c40810400300709282c40c003406450010b01c8181c0790441d0101d04c650210b50f00c5807c2d407555044c810b520101e018041e03413080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 156662176 1250 156660926 156660937
    0x305040303050318030d020c06162f1002070507080c0d1104021603080618010312050c0f0102040e04020a060c050607110c04092109030809060d0f020a080106080109061217 75
    0x44e000e69545005500704580258801050303039070b02d07000d0403000482c50003410440d27460243d51521030341040c20074240c403020001e440e01103003028025100210030319081c04102104490035403460060741da500794100186011001e0380502115408604043c0f13458594000c4034840551121050440002000000d00a801000038181c1001c00380c56045040c15804142c16000c0c4205071034995026602054580c900c1e0401d010180000d26072540d9040018441c800420349040302100781c0d000c01c40c0b0161041d00f640d019034001d982c01d4a040c4144415441c1041aa1004003464140205240780950303410b0f48400d401440d0b107051010303c000fa000302050520486100306001003080080403110b2411640010081c00129000c500802603000703a140103424090507241c0205e030782414004d0340130400001d50710420200b410b0030b0f161962103074408080c0c0017400d111200d640f03600b1600d60420340e0042000d10140d01c02001241400810402d4009400684c801c40790000d01d10300c0c5220102c0f0a900d198481c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 156663426 1250 156662176 156662221
    0x1103070e0112230a0e0a11060901020708070b0d0605100f0f2001021806090303030f130b0106120f0c21020f07030215060a051e0d050706181203050403030503 69
    0x3d4100c070010b0f0910707a01d5031051180c00010088034200d1244590ba480281000900344c0580c0d03881202d0760725000000e080d0841e0148100c80d140c94540441c20b04003101540815020a0b01203150f400049803801400301405050341c07900c2510724aa500202081019510102070142907003191070480d110300100781303100d00f03800185000175003000302590003540703c6440042ba102d100d4001401514040080b26002c5400400450951300c4442c8400302000c0094403000f80900c0c03c0c23403820001a5464442d1f8000c195544070000614001500c02c1c003502d1a00e5800e600c2185002004464a5080701d039914182920000600100d006410210001d1161001001c6401404204c2804055001540c502c0120000c004016036440350740a02100c036100380592a802880001030710b290741400b080000d21904003d0142000504c0c1c0e8517503d0900e03000383c012100040342080841e030801482d44031903005220030010707001404030302e0724010100d01880c04000e0811000101180b01c4002c00011800c10102 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 156664676 1250 156663426 156663461
    0xd05150705130e010509160302120708010501020f06090304060e121e10050123010302090907020c0f01021203010e18071206050c130e0603010f0504050a061103070e0112 74
    0x3446140074215401551060400d000301d000b001c0b410382444800603049507005440e0a40c035403214640303801c0c00b4001d04003510806078207001400c04110000c0c2107030b02882641d15500011b5040070b00090600c0000700241009601901c140622403400208860803a078642c6000d09a0450050005481e0f21413003807603012034842c0800c080d101d200e0001c0078030b0401d60340d035003142d54070075440b03d01c05c0948509215176550010350340540110050041c04400d454181490010b28105001e40000c003000020f0b1036800c01a44120b0001d106400c140680403030051f001d00080c800c284043e0075404580c48140982080807110401041d200d03c205400a0030300703106842500d510700d40712021070010410b001020380c1e069003007001094000c0c00760300840301400c1015030f968401c1e5040038900c044902028100030b406660300c0740c08c41d01c020568450280110300c200f02038000179045050110039103010049141c04600300b0818460069003004a120039001c007070030411308001d030340034102d0020012400030410814 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 156665926 1250 156664676 156664681
    0x220f0605061b0d0c030207150e1206100b0c0715020f030c010b09060d03050d150503010f02030604150518040c030c0e1608060d170c07121104050c0403020d0515 70
    0x218040d04840745680140b003110f070300c045003000072500b1144802028000d07810481d82440000c81c0c02c200700007070900b91300346814070308001004114155810300c3e2a4015402171030a10000c0351035900c1c003800400c06221040d042c84a080c0c00161108068820501107003002c5211240300f500a00c03006403402032150590b502c40c800290403501a101e10350b0140d109200d4880010089c0c540264048009a019a101030821072007e440b9002060782010302ca0012250840025103540c090040c0034200c41c4c1502d0150300c0307050110501090300e40784421000150a0000244425100c40d5046400c910001d043c00440d500ca60a0440c00d0b000150805400454100c602088814416204e6070080c0740b4a41c02c0e003080c00c03840c00112050030b401d58100d64010071101d01e14020a84501c2980041e0440c0040e45180070f150001c55468015258070030a801003a103402d48040c4440c00010090880050b038051025141c0b100449200d44a9800020310800c0628020010303c4070802c038805440010048148450 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 156667176 1250 156665926 156665947
    0x1b0f0a0e07090312020d08010603020307200c040f090b160c06062309070503060409020604080109121701050904200a0308031b04050607240504060203060a05220f060506 74
    0xd03495000c2138035864500c2600d0a0302c03a10024041c0ca2207092542c82d212143d0901d40304901035440502000108602886052024885111140f29000b90040105526240d001c284800d44088480c404011352030410340002150002c52103550107404d40840140840d0480740548200e420050301030f080b41c0ca84440030a07411980c1d2500542c0030b90f0010503c1000f41e49204000c1c0c030700301c02c48500001443c240702141081c14103400201d10144000c3c5002e0800d03858040c480d00b110102c0c0015a8081120400701600d030760040e051f10146d045041005003298140400f003840b82202038801080424035030b0707003d0742801018180d451841001801d454406075241003844082e082a60703240600071100f1560f543c4580c5403000c4504407280902035030305242164454503c21410000348402e80314400c452030a50440038072482e44500d104060068072030400318284000403413036802580c0141041c648010406108003004010f0580742600801e40b4003903606004c003e81040d921035501312401040e10920b4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 156668426 1250 156667176 156667187
    0x916180b030a05070809010227060904150906170d21090f02010e19030f14030406020102190305010612050603010b030f0f010c0810060305091524031b0f0a0e07 70
    0x3144c0f0ba03640c0c07031031030344449078401c1c202d1060803180c01040070714040490308815180500c070031010006200030708106142c004034003034a0421012a000041003802403055000d503100f860060a035030081c1d100880c0c01e00c03203031035691446016a241400140041512541c00c0303801c200c04903101410302406403c0683c41c01c03c1c504a140308040380405c05003041c00400c1d0170301c20700303508403c41c80c05629803e044c5992a0304c80130850030442900c2c58039240691032010041000100014441c2d680016075a0061183e880d4500030301e01001c1d0205824140100030a42d4005011078240049500014150300c4d03c000003401070034496190f903010f01550301e42540042012542c0c40749088458000e2103440d40c040400c9505680854812040f002200001d10089219510040c7c0c8401008c0c2140d500c801d00302d05040513498102c540f8070f10340ca440c0c22602e500741045d4070070201c6448198018240c55001d6940d044600c59a0004103010700750410180c551580e5000740d0350014034601450074864184101e00821 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 156669676 1250 156668426 156668431
    0xb0f0f0c01020903250302010c05010b1207030507050604060e0f030106080106062304120f0c0e010b07051e060105040f0b1009030c0602030903191b06020303010906050916180b030a05 80
    0x100b4091000400c011703141c0340c001c01e000041c2000b0301075803aa05650065030105091502179956669815200110351a1150702600c0d40341044007c084140c51464201c1ca01251900032a000307003801c0c0000c02c58160800c059900d60751049410500320003c82c00800d00400352640521000e600b44640010800e070407401e071482103580d0346201c80741ca4910840000b1707107200380e115414442a0301d152500102c4c01800c070301d0181b180310740d9215462554034481060b0001086c1c104540300c0c040060f42c601000b201700108414804203100b514061548118610745030070051086501171901c590443e000e241d110303480f600841d40014100320007845032150042016031280030803034500941c001c01107400d5000009441e52340d00020005c0042004481c201026602002c40c100d42d01251004455a110410018040544050b034020340c0c8a42c50241420182da840e98461030162450805011040b0214001c968003203026041c00c17150005080c1a81c914007141c1c1d4032082d0032250100901c00101c5003038200740d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 156670926 1250 156669676 156669679
    0x10e1503160e0a0b1e07080901030c1706060a0c0501020f0408191502090a0909060e010f09080f0c0c090403020304140609011b05030f0a0c0b01080a0803010b0f0f0c010209 75
    0x115030910075401d468052444a100390700807900007040000c14440d03c010400544080c1000c5c041c01e29880702c003110f54100b90b0701201c020801080154065925206000614142d8507080300e051020040400550b00003510441c09840f000927403d000501030b03801c000d04164041c00845d81c9400c50306500e82150050300032001c250040d0445001010381010003a000103410401d40011004072100c0c4100a601080105801c40340d41d0800040c06400c1c2d02c9507003101c82c06a117012482511030034425003124003071540620700328540a005008556041c2c00d4845c20707424042d10545d903401d14401c1c0c52a082c01d9100c11030b401014802004101b40e408000b034000c5800195490045208145c2001354500a08200e1030001d008540103014499030100305008450003003068034588142c42c40d00d10020307485455044040b500c0d00d000c0004000341c010b525030042c1341075000382907201b03052b84e1050424031042c8941c04400c00e02244601700c021884041b82c0d154112490b01d190307141e645000c054040c0d003040741c07541e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 156672176 1250 156670926 156670951
    0x112b020c0f071806080d11070506120601030b150a0c0807020a0f0f08060c0d15050306072105040f0b04030201110a1e1806030917040306060512010b0d060b010e1503 72
    0x2483d2002038020700d019207403c2800342c501035071a03601c02c8540c5442c600258646109907880020030342c40300c2c001080d010324015403007121031414500240550f504240c21601800e00030001d48041c0c0c07404401d0300c00c0c88441d46031040e404045410710815030f0143c108042c1d445140c4010004507451302c40303034a100300c50740300101d03e96050340e503468140c44a00031079401c2c0e1481030030852618200501d500850701c907a81c4034070528a058a030804a490254100e418401044035a00c40b010182e001d802c6400b025009910184900e19142c0e40d0018003a018000c01400c4007036490218080500039045803c0040407182d900740c98501c0e50000424010050070076a00c5502000002402c0502c11000c04140c2c80da03d0031a52212440d100c3c01f00e000f029420402c0d20f201117645c0c20005e01403c0340f4000c100070340c040e040118465040c01d040100a109154482c406c0fa85402640242904d03555180e040b100c1c4c1010300001c00c00c0e20780740180d07080c1e0041544a50301140d820f00443c0d03542200405035002d94100d6a60 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 156673426 1250 156672176 156672209
    0x150408060a06141c05060711070503010501050f1c060203070327170c0c09100905070c0c051309021c0b100b040b03070302091302030604112b020c0f07 66
    0x8990846646001e40c03070240c0d801c0303040c115013030820000c640c0301252030030258000c504068a42038200308080d2031100003d5440c41e000000ca25080225001500d000c400820241d498100002d1880c1c9100141c1ca0090f1071040100e200d070103282e15034007649a0040011341d5a454260700044c010180c2601c465214052208a454444100281c00441d55031083c80c695942c031050b6074164080e0440ca903901d060744904002016a030f11902c60300f50164002c542881c480c18284001c06040d20001061881000b122440300404582c025507603408840f0141c640d1034120b00c1c0e00e0184005800c8881019400803081250317101e400b0040b01a45c1c15142c0506034180181d202d00e204203242079105e00c138240a211040c44244240395101000b180c100c0b140b4200149000845e901042c51702201e44210310500d9400700800846007042d01030580003c2c40442000c0c0340564049400714071700c3c0d0360300c2400d0504440d0350100c0140000b50b81210044001c00d070481e20054081c0b035210f99030380b02d17900501c00f0f41c00d0b40000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 156674676 1250 156673426 156673441
    0x807031506140d021207050406170f0c010c03030e01020f041d10080a08030603190b010e06040c0504090e011e0b0f03060411190510030606030e0a0b061e15040806 71
    0x2c4208000303401004040c1105040d003c00541c041c0242070000140500032001445641d144681c400904003003d2400100c03a0707407410513080071444031480301e4a8010b601d80e4030700b0340ea0040000c00401d0b494200061848510714a081c020702405032565041d0b0000034000c958007125880102401401383d01c00e5140e41c0d64064220784548042c454854148e201501c54000186250003a40d8005806011a200384411034240180c0c02c0001c801070341c00c20201d0006111814504100540c844030a490510008a18441c010310a1184d0f10408160503616403d403a144070b02900403903500e018180d0b24107131824041103680028904041d01c2e038855089100c040d4081d0030080790343c5214a8100281d02c0d0448800000d02400c40d81182c0250595504284040f6495452a1030031522444507038002403010b0518101070201e4440101595850707212650303ca00084205d112103903c0f0b03405540310609040c030080b505510314940e20341c1d281d01503003c400850a958100014100711000d00c0100d8207a40c54800 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 156675926 1250 156674676 156674699
    0x80f010903050318010e01050f0f0106030c0c02040c11060115033803120a022d210c1c090501180306021809040606060f090e13020303040807031506 65
    0x150003004210b050002036000000f8002401004a1040012a104520200e1039084400c100c0b805591001380b82c0c24480032000d80200c0601400b0941010400403c04541c0a042507220030402407059458030071007d4001d11954400241d00c1d1100d08891003541c58100305404903036805015000a4a0002c03000c40c0c06c04104224844544812006804810140250034400f518800c109800d0700c203821500c81064101c3d0014020581e040d800380000040b80003042241030440121964800b030b500401c010b084001140e4070000c289810440c8407045102c880040240c020314810058600501417540340324528805c10a60090443d03403412078180d26800151644561003003928640f20aa042c01d100140a55009040002e02009038841c1c0f6201c0e40001450480200e03400c070303002c41e140c40c8200030760f41c1c00182d451009086801c0c0514410b00302018594002401040f0540c420401c01091040d034405104503000381c01241e05565045459081622462110503402d081991900c0700c00038500d00281c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 156677176 1250 156675926 156675941
    0x6150a0510020c01180e15060f12040507051e121c1107050405100e0a090f15110a0c032007030b07090f0f06050a03060f1508090f0a0213090b07030501080f01 69
    0x100f841001901d605000141c0341605601042c0c0223801006440c50301c055240141100300500f060490b800e2400340b0781340c0e0600c4c181740e0100740291059405540800107030f66040404a00030b541d0700c17040d801508562072074041002e11079141000e00b00f208480d09680203060121200703c0c6822165900c1d50b41c001e00040760300446007120030002507402805a5040843c5d00c80d0000c104c07440105200e6440e480d001c80e8030780c0b0908110f54002c87c00030404800c030002d028000210b51b0001800f070030100300e900084c00d18141103e0003010440945614526502d800d106052101550012541c0300c42d120300c0c0400302d0a0080d580580032607008a400603840080c0c510300801c0d1070f180070815140d1131500381c1c19030341604510482400c0c59181d01c0040f800c0d0f0740c40d510f0b0600508010400b46074040800d00040c117442c50280c101140c0d9040722420401c0c40c0400210b281105a05503002da0304040303903507401d900515070802d0082c0446d0002080c400c0d015455007100341070780c0c010307019245141e21007004a82228030b103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 156678426 1250 156677176 156677189
    0x314030a032417150a0603020f0102060f0a09080403060504030905012319021e01060f0b09031504140f070303080a051005040c020304090603050a0b0108070806150a0510020c0118 78
    0x24100c144408200055040307181d0b400032040712135150000c444810645811540951003e54551003002076290407103250407210030a001410f40d60a00900048050200500c4901da030754448510300204110502210300075038000004001501b81881c005001c5241889418005a058501c0e4050704a11041c048051407a0092451800042005c0c030800ca104068624003503001c0c01d2400c641c00d4104440326010f40002e60000560a0300381700103e80f810f459034002078440ca0007030101c44c4058400044207000f4030001c409100d095074441c030746030012542005414015000d9a01e03c0c070442007000508000b544d11039210040140ea0300020705003198411105402e903505000010002401d090380140740016151050328074003503d903602c5c0802d954056004441650000103a40203003d0101c04c118090000b00000d031090501d407442032955110090024250301000c61212481e0f6507483c4601d01c020a00a010094103021106000c1c1d11801050002804125510340440c0484c01103030220095410707 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 156679676 1250 156678426 156678491
    0x603070b09040c0306030b13151109090a0b0a1502010b010c031205070203130b040f050f031b1f020f0607030b0a060804060f0e03030702011a0d080c070314030a03 71
    0x11007004201c050301e20344400606165585c4408800300b42e001c20030f070340305203409801860700c1d210620b0701d66500203d0341003a0302260300d0206110044803480c022140039801c07c0300c1a851030380720001d110b4001c010148070309620005040000501c0d00c0c0c81c00c0d2802203400c1640082102550709030064603a1908400c00a000401080b14105022400c1d0b00071358200240d441241c0c100300c2c901802c3c41003400c640d042207681102c0410100013407103010489801030001955510982c40209003c2981c90600d450202403400491031580320380c0d25003040319400c1c0b00e0030a00800340100c000d1400394444032203d048980e640144400260aa4003d004070204801c000d81051809840c14030100c03500380d4060401c40e00151280c403032540c504514000c5101070410000615524204005c000c1d003111407900c00e0446c0a90030454483c40365981d03203451919036800541441d62108140382282c10a0900d820003410807000d61501c0128078030001c054001c0e80d401c1d4804000080c6d04580140d0100c042c0a0456641c80 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 156680926 1250 156679676 156679687
    0x10201090312021602040c020c0916020a030813120801061814060d110403050606010906020106030c05150c071e0509090d0e1306060807121a1903080f03040b0603070b 73
    0x2201a4020000395507041407400c1c0c0130b0416400202030b10f00d01d0480d0390043e8400480040c0300d02d40081040e40051003a07100e91080805010b0182d01d070f68100a001d0244500031001504050031541181107455000d1400c03d0309450842003c1d291701002c1c00384800141d9000214810308507005080e01c01e490020444031300c0c40c01602e041240d01d03400031311510302d400d81310750070f141030000c1e000302a001552203040503094601d00040010118603141e4410400c581c10488100f0100303141440100c2038400542c3c1600b003100c45d6a01104071403043c511030a2031403150020018903806110300e5111407034014180c11090a55440420403020f42c02c3ea601c5100c0d40000c1c1c02242100d0280d02d4030015510094818400c082c504000340b0104c44160b840000440c00341c1040000c01c680c4407003252445218440700300499980c0092400000c0c1c80d10349824010941198082c5d0190752488044000707550100e200c90703a8a441444540d8140c1058400301c03504122100855514500410301100342c440170f5103044d0604 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 156682176 1250 156680926 156680957
    0x11030d0f060801020306030a1b050a0807030611030f0a09080c0607020d030c020c010207180e03070803010303030c050a020c211f0617150402060909010306020304140105060604050111030d0c0c050c0102010903 91
    0x1880c3c08440d44689c811343c00100c503107038100340c54020004540a044100d2550604c042075941d0a60f2f82000c01e4001c00402682c880701e100c10907040ba02c104000106407002d85030014192059620342d503007910803401000b0950b60300203000e0071000380f50394091028400c008002c0e40d48000d94003004d40503030004d1000780084a244807280201e20070b819004a00c41000010761400c40d800010705031001c000000c0140b090540601404d03c5010b4503181592a0584000c4000c1d02c07485400d5445200d415050726040b585542400c260f8203202015090b5814004c441e0682c00d44a07203080d19500030f00d41003600018480c6d0201079246c526210640203040010030751030700d81c0b0b00500014800c90b4080410700c001c00580d111004003d020754071884005946e41054200f54104080c118440801170b03042c030082140c1070702c42405644c2204c500b820840c8004410101443c1140031b03002100c550907203081400141560b01c03080c0c2102450041090b14800303507000c80124281e03403441700c1c09804110640041d23f2030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 156683426 1250 156682176 156682193
    0xb030a0b060c0d02010501050603010e04020d0f020415050102120406050306120a060510051809030f0904020d050c0a1103031b090d020a0e0121050c01030b0111030d0f060801020306030a 81
    0xa1000000d480050480000c585801c155a14441c03a0300480028000e80d40902c54036003d0401125041d083d5854440580200840204024064030b0261484010405811405035170a68010824481c98107811070b808500a000e218980c0144559041000c1400d40b4034200c5003a40c48a9803024595914071040c080d400d01c00e54810800343c49410b0401b03010600300d10443e80502c555807151080c0d00d24180070030609010288a00300f02c0032500703060104440340081101c9076420700500264649040c80b0006000f4001c52208411641c02c0401304040503030320380003e15901d201c40c2c0301e4400c90a180868250349000454a5001c0922680d60348041c20345013002400c141d410040143d90602d04580c0451010b0300c03a41e00c0030b00c5600c0c4000c014444122070b0841100e0710030804068440c0854151500c0d80d5400c078103c002d83c10b050f56001d0100d00b45e4402c030381d40c003141480c2c070084a545e590810051402401040c501741042c84c40c0c4600031a00d0300c0107008490003800e0003802042096641d850b85001c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 156684676 1250 156683426 156683431
    0x611090f0d0b041106070510050a0605042f04051201020705010c020f060105010509040f0e010501060e0f0312090a1203020d0807080903091915030e0d030207020a03060209010504050d060506010f02160b03 89
    0x20f110710188000c1001031402c200d4040400c00707234200403681d424654403003001e4514a40000748590306240c5d180c10328901c0b40c4044200045840421292403401040c0310100c0d1055802040d000f070428845110881e005400a060140c442c0008010000400000301c1e104d081c0f546903901290400070041180d58403a40151102110040000482ca4541c401041c1102c000c0703002c40202d07945501c01001602d402c40da00402802c01038a0306102e0081c0f07140066118440c849440440c0e24020441c030b841a1603c20315800909503402d4000c1c1d0703c156504000e07640e811000c40344000100c0300400a40818850b6019500500304003000354203080c1000d0403c07200b00e040500142e061490001c000880290303c82c0400c0035285c00b0b8030001003c22000000c58205401142c6c114203041c01004400016110490448216900010016250340030500120707002d04c55584804e0b80711240300350b03c10600900b68021800351000343c9481905102410087ea1580078000b00001c0010401d1410440c3c524000019075 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 156685926 1250 156684676 156684679
    0x1409060a0227031504030e01090b0c1002030c07061e06090c050a030906090203241501021c020c0307090e210a0f02010605030708010c0f050403020f1c0611090f0d0b0411 74
    0x40d034824880c00c022802c0130049500750002441070710008603650300700d0002000350115103005443c10821003546981c44541072a155041c17940080000c94416001d0192038440d44e00c1380c01440305080900007846114111507245040a24016000409210328400d01001600326100e0908201901074150f004084003001503503a29201c220000050380e040c003000305c12961070600010030000f05080816680d10040c100c0407500c44418803440541c0e00011140300b80d0710300454000105194110480c18070944001190301442003680200740d0301c856810651455190408840c419044008401c002d920200072160715100c08000d4203c0b02442000320301507806590001180c602c2d560004203143c05296030058a150350b6800446a0480d1b000301d180700c03043d84030300d400750804d0f040d80c000642c06031100b1b5a5512610490741c641c00d00001014800d41c0c5030743c00920420598034400403080780d5070b00c0050080c0c0703d01111600ca007000c0c1b034031681e80c4d49071a8100c50b2140d1b050359181c0d5407091403003410b111203 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 156687176 1250 156685926 156685933
    0x708041a1204080d23180613080703020a06020f09040b0d0201080f0a06030c150f0903110d06060909050c13020403030e09040303110706020d0c05040312180503011409060a022703 78
    0x5100d8880e503140c6210084581e0145d4010b142c00d00714001502594130011034a50810300034080c0240c41c01c10346071308007a00088826507810715441d06038500000c0c010300030f20060011490759541c46042c8050484030b94140d60600c034100c441020402c0002880b44c000380030070031034000b0071002140d9004e0242c1c4200907203400942141c803912403028622565000c4400c0c82c64510390728084603880109046aa400303410240742c000e00315507502102a5070348400364002e40c80d80c8980001c0c444250445001484051010055211503052140d25040c141c49994010624620341c4a0320100754400c9408480d0140d8910201c210030008010f524600030b0415000c03d51210108006124040c2c0142411403040300c00581c1c40b09884070035016514901144030601c001803008101042c1c0002441100c09450701c0c03c480d60603114109010003881d56040a03403d98645008850070444440f42c0a018118000485200350f803000500c0c2c00b83e1103100881c80018408100f00100b00c00e10440c9203840e03007001000e8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 156688426 1250 156687176 156687191
    0x31e0314070b010302040e1204030f020301090204140402030706020f0c060918070801170d050319090b100f08010b010c0b2d0f1503030414010c06020708041a1204080d 73
    0x22146507048103a05464440340d607401041140361a204404604408001604040703507410304031031550045220160003e150b6192410440d5802e61058049684c020800c02c50103001c0b07040507022100846080b4024424000f010500038000915900f214036844000c1501e41007400c18050b482d007144000b00d8110100044071140c208035907040d14442c40840c2c0d0381150b150325181c40c3c05100300301c4840c0307070307606402c4003901c24a0346920004899020120400740c84c208000c8090180040c040107201501300c4400d81c060082c1c28170703042644c4040b200181e0292445548544585003202ca000c0902404111301019220004c0c0c40f400c11180e03c807840301014114903003e2251080810000b19414103100e46ca18101308200c14200302c04c80e0046202e40b4030140040307c21340469523070312882c0561040c0080d1a00001040c0e0f1007000f0841806511407400c0d500c03086146400d6295030002d00410048010903950500104200c40c1501c0c0324500c003850305111519143c803500c0d0b190340036101e80b00041d61103082e03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 156689676 1250 156688426 156688457
    0x91b0607020604030c06020307120e01020c15091f030e070e0a1d1929150a180c021c02030d270c05091b040312030e0604030903020108010609031e03 65
    0x420006001b950041c55860003285040324414080c11713944030a0103d0503100031816607002804904d8010203850a5801200c0c03010150b134507010b104000307503006203400946100c41c2541e8408c408803280e1a107060243c00b40748110704e600c6155038000e407050f0824880004d40b07604d00319000141c40c03040c403450144d208040041841e04001030000c40c00c0b0508500080602084a000945090804d400c2e002d0340c2c560940300c0c207250102001034030903d18405181d91450749a41d030720700c041c4010106003440c0e14400a04094040c003a05500700d1401c00350103202c00f11070050700c0c5000c18610034007556020f5880c18410b43c403400005d24061300802610410620740c0038944210382c01ca007030124062903c4c0750080385020f0402503042001041c0c64040804502e5070001110442c054a096907030068448005a0b400031046005154403015a142e0b8420a400e110034980c0000400301507a000307907940c00d0941e80302c1c6070a40d10f0031060311000703041003840c10002c00707130300011211808858401c1c9083c81c003804171000e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 156690926 1250 156689676 156689693
    0x11030f0402011106100e0a02030601051905210619030209040803040f14031804020a09030f060b0402070b0106110109021f0e0910050301050a06050f01050a05040902030a090209091b060702060403 85
    0x140d655589200040c0244020300711401c0b80751f0303c030421050940c0f86203840381c002061030040810445d075030a1505003002c45280a54151080704441c044040900c02406600003020503055403035500800d1a540d240090200340b021400580c0d801030308d0000d0b95216941c80300c0e007a52000704140e9809072614918030018002c90789000c0b05ca40d051004540301e841403400c3c1010010300684071440b0b81d2041060002554100814a08490308140303a44107003103140c00c11710090000b04100a038000c0c0b0010740c1c10100020081c7c518165500b507512003142d404030b201c2407401c9441c043c02c081d50100c138a07030394070368004a0701ca40710122225070701c0c00100c2100c0010128480840503100c112400e0342d0108140800d08091003070990100c1001b1003402040d240a0204041c069042c0c42e10341000800900304103154001c9080358000c04101004540da0702e040b21248000344542c6400724400d400c0c001c00308000c80d4001415800e001849900c940c150585d0300204805540440422030700940140400008100c000703 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 156692176 1250 156690926 156690931
    0x210d03020307020d0e092404090302010e070b0301030b0c09060c0d050405040c0c080406030507020307140120130501050c0c0a080106080d090308120c040806151311030f0402011106 79
    0x1620056101d080c8810041d00344403d552004040040d00702e5502800c1c3d44000459800503e5034401031002e5075189010704200d01494070840d04181002d20307440425078158001220b0b40d008900b5100c01c540c403690034101a20081c80040c0010655401103841054103000800c4419002040d07070f894402d807102038500380188030199502003500410300700f14900786402040c60b18482482c00812a60b61580c82352542c4c055030003980b00b0113546c0d200040b0800c2c020401c49070025008954018421410707410540a803880464101101d00d5100032054005070751016149006281c0411b031003164102401100c840d0450041c1201030311603101749002a0300e0388001100a0200300c000482c0841c00e0164030761814821180c0b56040150200c4108042541c150558100316036014030a4402c0d00d480104138070030b000300d4000c401d40b40605400e0041107650714411941d80e03c0c0c00d4030580141c2c070901c6001d80071249440c03424401848100000340c17061604001280d4003920504005982041c21110913207040d104 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 156693426 1250 156692176 156692203
    0xa030b0306040f06050907030818010c0b09060a0b010f1e030b060f0705070b0c0304060804050a02040204060203091009051c020409081201061b0210081018090201030e0303090a0221 79
    0x10700240b83c0a00045001e8540d0010210000b41025441e580d180001445031030601034411030341064160b500c2e0300c2058180c030041e81281e0584094101040a90b44401c8182c803030b010302c1c0340303000c0306400d15501450403d070030740d000d07034407003d1000e03c01081c501001c00110741c0b540704160b03603407899a105940300c60142075035403d840700c816254031a5141482c0b03041c1c031030f81280340c03120402d1041c10220364000040f44e05070703174031480d0503110364407103107080343c1f4080b19200020340c00341c0081004507440340e0000151100050803100070b03c5940d05100d0548845440d0300545811908144030f268a11284003852a030003880600006001c0c8540e4071a03010a410084003031400c03064150041000c00da0110f51a0011309148402e6003401e640c6a00252000e07019182c00404d1000a40016142201e909001001445404054944550f40e081d842c0b00408d41d1078001c9000ca8504035000011070b0380007040d42c0c4654205002409008043d408010350b112010700d80190011b0f2807040c070650000240a1403041115 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 156694676 1250 156693426 156693443
    0x312050910020a020c0901080a020904080a030e030703030221010305120f040302040c03020405011d18041a07020d02210414060c0703080409140402010806040c0e0904050c092202060a030b030604 85
    0x1041c17004c00107035031300691054a041d4056002c1b607003d0380e5903ea0301078000c2c1c6c1c8401402d0755202121001e9002c1c020000b035075142800041429000c3c1034050f00108107015186004070f030203a500c00140031b0100401e00015181d81d025a0001400310785e008003d0000030044c030b00701c509150f560380c0003800341c401040500000035000705003006656042040c042c0d1807c4c0c030a04400c10400d101002c5154074a203811202c604003084004181807104958403c40c03807800324a02d814586c50002380117990760250421800051044503500100e40b5506a010240280107109003886d20b03242c121b15220f18502044c601fa4841d10070412118408800c00c001001035114444998540703142000d180100c80818030050304000409041100603030b40103c40c1680110300300c1740050602e51300c1c001111000c007002c04c0c0903045040e0703809000078820000b8404003048400c82d0402030f950386018016400101520b0034001e0500610319001c018500302d809803e581010303180011340302001c0c030f002038030b04041138078280c500e00d1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 156695926 1250 156694676 156694693
    0x3090b010f06030c0f1707031404140c010f120c02030f030403170604090809010c080408011d0616090b030c12010b030a0b01030203060105070605060d02060c06070e010c0312050910020a02 82
    0x1c3d00b5008401c1c5140f014241000e0110342002c000d00078062003840440d0710502035000582c3d0a009074080c0c1c460a00b0000389400c0c601e403518242540310b40524507980148104105d45030158407400e00800d400c0d84907510031401500060744000038211224407441035020901019012a07051409940b14500941d40d841104100c40c0900191400140007240258100240030011a44840442c0d00c0d094081c81d00c0c0581c0d103460300700a1214009c03904400e8241d400d05803000c00345000c0d44413a82c0444008400d442417500c1d22450710703200d01c00380004180451010001004a01440405164401035149800749062180b85826031001400d8208a8000d4030110a200300c15510b0311a0005415083c00d0440c50360418100190440c050f000c0000d200b107454000280700354860003000030b0010380c085e0425441b8845004215110030040354142d00080050040d40400e6109200d22403074a9099181d9602c95069040c07404003800c0010580c1c0841d00c038000304501085030768030050440e070017a0b502070050348 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 156697176 1250 156695926 156695939
    0x4150605090103020d08090409140d120504051f1401060f111204090e010902040e0105010314070b091002030c06072001200705120d05010504060905131203090b010f 72
    0x11406a0051405280d60070014401a00c4804448105a821440440d182c080000c0003a02420130303540010480740080c42c0300250364078005581c51442c03425440b0362510140381d80882040700c01c12600a045603000c2c441101c0d070f0382c11111b600c4c0035454107504c01086600190a41001d40d050030390051001440800d42c107001284d00c5415010003852640240601e0240d4895801c0076020b00d0080e50f00195a5001c020305a00c0c0075401540303031a40c058000e001034440b8014590003000c091105460440407040d108000b96004107106060b500b0400010741007918500600a44112507512035095200c02c110b03043d40c0c010200071840c4035444607036480400c41e50041043d51240b0030301400c07490741c4c1c3c14034420a012041e03d040c0e004140e000200d01e9074170342d9091304045280502c4403079252402400050000d0b101c103c0340d080b541c140c0f20151014060b481d51003c01d40c00f04d42c1c0c1111114049145400c60f14000b03801c02c50304400b0070600d498041450f805944410600342030070f030700029440100700c1d01007110 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 156698426 1250 156697176 156697181
    0x1207110909010c0c2a090501140a06021216050f0a062315010212030708010503010615020d0c110325091e0203070311030405100e01020a120504050102040e0415 70
    0x904658001e0100d2842501e014242d11041c0c4001880119100444040245c01c1d54412890000243c03031041c00039031754000b8000500083c0900423200301c42e60140042410003030740810480c2d5041c0c3c0202006909081000c2d03043d08958a11440621031520280c00310310b0401040c4004244003000e02511884d5150100440702d44c0384e075003060000c0f10351500d0b02403420032610981c0407084002d6402c40c84c0e402c1d0300407414110380610702e000304034000c001e00014550207030303109060b00c50980080109940b00c51031843d4149140d00200e006074054020211054844d1002502440c40f87c064009040520f900080c20300704015007000f00349030084032106944001607445401070000d0300c820001540d103201060102100c00c8511000c040d000004102c24030311a41c0311080310507500d100540c90b400c20b4503000d40c507900304c8100741440c613040c10518054154103100b02d03141c00401d9114940442d21204000001d007000420594840d5070a0100140c0c196100800d548940c0c0300d11042d038141952041076804 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 156699676 1250 156698426 156698431
    0x40f06080a0c031505010e030a02031501060e15040603020a02010b040c02010207060b0d02030d0c1e0f051614130b0409030503010e010b030c0906070519050f0d030e100e12071109 78
    0x101810f008500c0120403050084d402a541d081c40e00643d90503c4001103407a000603c01d00942502c95189000c607031011140c4014140c55280d900c3d4001c40c000e100410181c800c4005014081d020b0404c41040154081e0740180a450450300001c82c00715800b1001800302d56040101d400940d400250b00c0c4c080041c0b0344115094458100d550b01074501840d00400d0307a403c8a05500b6080c44140140d4209102d00714800c40e01d40305490b02007034608003552030440030a00300c011044403070344904c421a6010100b60000003060b9a0f48003072080900c0c015504001c8040300c0c0114a01c0d4444e070300d00640045440314081d440b000f500a448407682c0c0c0d4036045071088031281c168442c2c0f030111410301c1130044240030308007140c0d1400e800f182c44507100c0d10039060950030101c240c00c288681c0710b002500f030700030440041a00d400000203042601c1d20315001d90001d50070740d81c0701c9141c0c001c1c46c0c000c044d0b181c051761302070b500c0824080d840a088403000c0b040100d030915203a1020300191912040e035007002c0c2091070401c40465 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 156700926 1250 156699676 156699701
    0x120f0c15040803040509040f05120a11010507020604030e0d14010c14030106050a05070602040b0c0604050105060f090105131b0207081011070204090503090616050c181902040f06080a 80
    0x901d0035203400030803510b902681c02504d100b10b0204004c207084c0075101c0f41a200c0d050704581a04c415203207800e5400895841280c841c03012802154401d0080031040c41198410115034025102c982c1d196501101c2542b0303c0404654411450100c15000c106200c07400c3d503640c9013030000001c8034600340d0000340c00012004074a0400410400c0180700b4564810b099605403042e9040c103075140c00082c88c0440c085d01542e04000e21180d000700344a10724440024040e800b6030b0103080204044d440340703c02d0013684180031042d40e40103040440104402c1c101840200c6c1c05c1007800000142201602e0394100584510b0002e24005a02c05a0140640f48040c000c04400103402c1408002c1024580420441e030b002c0d10304068403031543c40d85000c06000c0300f03008031981c1a500422203640ca0b880c0071703030196614035148400d80755031060b00000c100e1400d20032100d648005030854000c680380e0b12020034040c0180c541c036201032190380a1000044242001c040a0090011a00c0d11541407400d401440c0441e50384490710f0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 156702176 1250 156700926 156700969
    0x3060e0c0d05100e030714100501050a060e01050d060906061e170703090f0501020418140c030f1f031a09010b06041205160909050d05090105030a0506120f0c 69
    0x1a00081002540c3e60801a1140001c5402c01c6140007090540c001d81d00c001e050760b503c0c507030180c0d801d0348042810012100b0000081100c1c0e6210070a10403124814010140460301d001c0d420441580a500134200c44a201e80c030204155031606661000d030740d072540c0300001240e8280c0d0707444d000c1c0c110f006e0700350001082c078649004a089051450b40c030a9101a140c2d0040c1580d883d88002030041170b80e0701d40304460b00300000f03550355542c9602803032501e0701040c614048103180c400e001108416034600640682d180050700e03070441c0c94030000e15070200c00143c00b07001889040100a0000d49640e850701c80190302540c06c407480c03501100b4000c0307440c82000706030b400e02ea45017040007100c9580d100d080d18180c8903107014894405c0000e00d026890103402550404a51401c1c00e0000f4074a4803580103850b0b110701c9413050f248080c80c001300a82d0300d030040030103080c08102c091001403800ea910754031081d03018100402c0940c1c0884944901070521811565548840c2c2102c1403085990400c00d2000845641c5e0324100e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 156703426 1250 156702176 156702199
    0x2060c03060307060f022401060e0102060603030301360504060b0f0a0306020d290103140403080c160b090607090f060503160203040503030409140a09050c0f03030d0603060e0c 77
    0x240c54030a44d0055200b40714003080192400d40c402c11071503907006a060b800d01c2c6140340c00000440c80050910512000489032110020782c0d52000c240c503806400060021800c59003000341c4100c121941140c0b41c01d0141c24160a80d01d00d801d041d85618224001410019082c2010308201082c4c0b0036811810780501006911000183c940c0d021150480b50040001a181d810342200340016114407062480341180292600440d40102d51003245c81d00800d0b2810441405c5803500381c0c5402104070b8010740840c40071000500700c000040d0040640004c910311814162a55540d40141900203442c0303103d0a0348030390104052580c01c0072003440544401d054040d031042c50000300030070510000306500750122412560850a6000300107403405400014290b84e10f80c0d4480c00b0358070007408003440408d400d580031000b15a54540c0b030b1040094141c1c00101070242c400308a000d100c040040b142400350184010010030581c20624821070014510400000c02c41e100340c00c41151400c054404c1803407240e9510f521 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 156704676 1250 156703426 156703429
    0x14130606050d09060e01060f0f1505030106030908040308070f02030708060903070213110f030a2a030213030816110301050c04050918120301051e030304060e1516020102060c0306 78
    0x1e44442c0e45004901003500141c610b00342c0301500c40131030070040035801d042c1302042d4011042d4101c02500c5040c42d000c00221b0740d400f90346510111030f11081c80850020001406540d01c40d0304135100441c000e00c0403a240c19526a1001c007142d000d4070041c0c65410600c10101c0c2107240a0202c40010310340e00004000c0303030401c00141510381c801e4150080c4030b50040001058404a03580005044003082c01659482d81c411034010080c3d5402161103188071440e024440240302040d2240342411204a416988001400c0c5410f400a500040d10707107103003111006001000408210041042c440014408241015140780480039000c6506905100e6410002005005644d242c1a4ac0440300c00301e03200b00340c5490740c05003511001141c85211031940602a1210030150000000b181298402d40302c1550103140840c0320320300040c800c1c404076410341042004106c4039200e20f04011100a00070020700c0181c0c4204681c096943c020304203a84429241c103034038415036070148002548244009000c600d985086c00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 156705926 1250 156704676 156704687
    0x2707030804140f0414070513090c0f02150f0106031116030201020c190206091005071b0e01060e03060a0c050c0703050c030c0d0c0303030504080d0c020616020318091302030714130606 80
    0x40031002001404030b000c62340583c14600c5000200715005040020b4a07624a00921991038207020308050b11601075120010310441d0905072041c03d403240300e26207030b90078030303a00310094800e9101441d01410b052020206e054042203020304018800e80005076102c0c084800c1c0303814000c9004854100b94007801c03a40c07016031201002c4408200044609070f100b0714941c0b10603200c500070300802508850400038001c6804101c00700f034100380e6a504411003c180c0e85c80000700d0780007145401441d01364101201084000344160000380504c156800d14030b00304036541602c03604d000b43e26030083e20341c0c1c0c0c05007004a10303034202802203071074414096030000a111481c4c3c4070300c4088100b42c4001002c0550f40c000003014045040d0039501c03231071980d01c0d081c0301102c00d10000a50b00e000607584202e09607030708803408039140e000104451072000c1c4c1c0e8032042c1005030601c04100b13001000500302400760b03c06030749010060b40c0034440507020340a003010b003079400d107010010710501c88404501860311501e0710b50107000c03090b00301 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 156707176 1250 156705926 156705931
    0x604150e070f090b161101050c030a0c060b040e0a030c020a05180a050708130b0c12040831090e0c0402190306081501140d020330032707030804140f0414 67
    0x156146c5801030761080100d07654840c17144081641d000c007250915540e54001c40c041445805a441071015210078010481140d0342c0300c039002c455501102c003241c00607008035a841d000d103000526544400b40c0e1000031400c0f442c2039500e60000030001c50100001e080e458891170741c0040079850114800e00d4060009a040f2402c2d100142070a4200400203800301d50400c115603c0f1880761100b64030a00346032501900581140c010440c411942d1040c005581c515005031394062800068a0340d080b501c0c1c040c052000340414103010305240a040c0403804070352100d000820018210303031141090400352034001030886000b42c01405050300400c00c1c110b10002891415419100c000028140482481001651075083c1010007509800b660321450715a1828502208905142c07450035581a0041011014180b100722074201c1454010002d881809003d0240340c584102804120b4450769100d0302d544041b900a640140d07071a41765180409032a05042c0c426500721881910140070059500503000c4045400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 156708426 1250 156707176 156707183
    0x602010b12010c170919060e061506041a040306020c030406020d020a030206070809011506080901060b190e030a050303040f11042c0309090a05011e030b0604150e070f090b16 76
    0xf010040f0303880c02c2c5c2c00d00c140104080300e00360501e200e070f403149441c001805091a05402d2806024001442200c0c450361a84030000002c000b0307854641023104000072035145c01c29000c002c0f5818000031000605c10b200601c40d284241c0b00070b44d2180d1420800034a0000065280790071034000100c2240000d400250040d0080d502e82010000e594600c41c1a50040110390312898400900c008001280d42c0c0001803107001d064000002d00038a034482d0204c5000d8842c90325600f0380c1100300418440f50364410080c2d4250b00b0710041c00d598000701644c0342d8a2071a0026101519038070300c98082d0901b0405090391301c891038141503900340484004884a86898075103401e44104c1a40d0020500030b0b151010310482d44010002031140300385003081c2205800521003401394580d91280410344018140401c02040b0403264000208100b47d0348100c24880034201f01520403894a600c4040407424046251070b0303503c80d0311346607034040030418404030043c002c5050b580301420188080141c0c1007401100745108101c2c540 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 156709676 1250 156708426 156708467
    0x8070803071101120b0d0303060906060203070807082508040e070c0b06040506130c05180d0209041214030c03090c040b1e030f01050709080c040b01050901080a150602010b12010c 78
    0x3513021039402902441e102603501c0b01c2d060603940100f40d00b50340b2000c02e89105020070031540e61240000d90342d034031941102806640d400c0c8411000148094000c0c00300d22880e2441620504c07040c1c5900340c91040358181204c01c0314000c0303024045001c003040b034103a03c24002e1800c1d4018116a8aa0422800c4050701c3c6a0145481c1c00004805071a800078001c030306804281300304283d00030041e0042c140c0e082a9a91440c0f403100c00861040e5250428006803507540007880c050060f140e680c0c40c4601781814580c3d02d000d000c440d0407100e015212880c0654070506160746450350300c4c9840c01240341001c401d8001a4456407600c1000d0515071200d4401d8500503819910030003101d82c5000000e40b42044121071000b107907083c0b030100a83e0b0f40d8407a0fa01c03411100785404407031110103030350100404e0b1884802024000340060140840329071007100d19907007240c050080060017105480100f10070705030541284c40544e4507601210950b007011412200c100000b240200300f0408010310080c070700c1c942e203144a9000107 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 156710926 1250 156709676 156709697
    0xe10080d080613051b030c04060206011208040608090709020a09090c030608060c0904020c1c140309120a0c050d030b180c0d0b130501030b04140d0207050111010e070b0408070803071101 81
    0x3003c800c2001e000b91651202c06e44038640352540d1070080c1e2140c002c15005000e45000001c4002000e6902c182c111780c040d1200d800e180c01e0030301c1112071603402004034510b0f02c550900003910b4141440141150a2030303a0300d05904074184007105096070b248000b10800c242c030702201082445004103c0d5034000e0051824960b9407070a50002801038082e580c0520349174040c80155012140c01c0e21089140114241c9510341000d550400c1002c0900048032244255004040d0011201c001c003802060003820608000501200c65141c1031729010340702d20094042581c0340c0205c012860516020030109020310b0f070b040400e2809503801100703030290102800d841030b15042c50195070780d550008401c1c0300715400c03000c00107581d59050500d100385003034809458445e58403418140301a404116000514100c0d00200321b0285020b0044035181030001d104d60040d503890302c0010700803001307020500c000c18540e20344546450a102d4500c1c2005907503440090f403907004024000c0043e140175481464000d007402c02d01c1624 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 156712176 1250 156710926 156710941
    0x1020106050a0b0406090639060504030e01021903050f03060d0209070804170a0f0f1e08041106030105100507020a030c230102070f1703040e10080d08061305 69
    0x50200c0d420203540704071401c0001c9034030180100074008480036551100c1303907156281002d481740401000b9803803e4030542c01e200010b44143c10030200f001c0c8c04602c60100919019100c0340d0403110196421400503203168140c40d41d640c2c0c10428404e00c808250424181c0f55030710782d0013501034400c0320303004603000c40040001030301c5950715010065195000781c80c0a401e031425410003407090130100d82c106d170b12800010441e20300e00901e10503101c0041c030b291a1a9101281d220055841c80d0301a0b6260042048600c000209807503d442c15050500c20b0340c952110030308040c900003440c000b004003401c0c05154280010001580e030011000884042410070310380e20100d60000c15074400503500042d242481040000681600c100c204840180b103100d0b4460405401000481c5c55100a1103980c003001c4031001c0c06d0000502c025040400035070745404482ca003994444080046c82001c031004043c140c06017104200800050000d0030b100c403460720b0414210326052001800d60360411140000b040ea4030800640803 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 156713426 1250 156712176 156712181
    0x230a080d02101d0a0f060f0b0f091f0611060c0f12100905010e060120060a0b030c0d0f020a06020c2b0605010906140307030203060a05041a01031b0608060a0b09010201 73
    0x103c40c4080a80e1015246411302d180b0f220301080c001c442592402c1030f0117480b55207601c1790808001e0010003c4101005450412200d00c2c400346c41102000e50310f1100c0d40900300510603620051a2036140c200b841806040f0460a000001300300581c01c0400308120700c0060582c41c03c0340c1010404842c8641d00d0b4548501c22940b100385508051602031a0400125200030a086154850351090740c4410001e84c1e103007804a440503401c0000e8059a20040200300b960440d60070103011400060100e07001d0b00d000c4070004005900c5650142e0304041030040000a41c1841000900505501d00050045c00c88210100d4003003002290b01d0f0f1100ca0103024901d0009185c0b129004480ea0440030900455031506c0341040141018840c4060340c1d810441c590083e410045844400c81760002d01402966485644480c003410004100f12130242c2010002112881c076508007501079405100340007203c4a8140d90b02d1510100340e0044401c0c441410100022070355401c041d40c09076a084a4000e850f0002600140d01 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 156714676 1250 156713426 156713471
    0x929060303093006220f0b0c0702060d02180102030301030c030210030f0f0b01120e030409020906090901030b04022407150f09030c200d0b0402010504230a080d0210 72
    0x280e03c94a90181008044002505070040544401945c40d1019030740000b0344a2a05920003400320390300304c818001246030396003015803180300745160a02d000280e44c00225150301142c2c200d11801d901140c1c4e100020340004890075200c0d001e000039807442d4110b450310072410b000352200a10030f00c40422150b8809200340c00000e00b00c20000e00c2407011200d009154006001c520440c640051410400c50016150038000c59421041020245180c1405c05002c3c0c0040d5100708800c1360081d60800c001c901985411607110300079406000f00c002070713040c04e10410030b04400800e00444948004003072070350a50600d07000c039050250300600c42d081e41c030704906056010b041000081d42200740b41c0907440781419003010180c28030f60f21410030289140340c40b501903940341c5a01d4041a403c425280c00351000151901310090b080790050506034106030340d4000181a03654035505100c3e43d110701800c4141c42d41002c0f07121a02030710001001d095800190707140255540c07a1100c0c29038605451703a10480414106905002 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 156715926 1250 156714676 156714739
    0xc0706090b0d1a0a090b030d18060c0204090b010f180203010f1401020a060e0c2803170d0c03020d1802090c0a030b12031306030b0f060c010f092906030309 68
    0x280c00f40c5d8034a15000240a50319600c2d00a01a400b1b030307504150301c41e80c0d07a4003100a1608000100c00d0518104036940140343c5012030f009a52516841e01044c210070b6a14001e0102110251006040c51040110b00c3c1c0c03003401600541c0e00600041c0510304643c0409819545039507500044246d042e00102c6c40c00700100005071106103842c1a008148102050384405440300307880c0501e000d844140502228070010b80c44d4041a80f43d40d10074400030360540a101500180700c3c0303c0740c0c02c0070000c0d4901c3e02125884030082004c80d900051000c12401c1500071030511081c80068603a0004907034001c12818000141400190000000c010000d10700030ba00c088034825000d800501080113040d00035030b49500101c81a105040420000603010f8424040c507102e054019002d0b00c2015945800d0104580290303407038078000c3d500d8440c51059014144500301c0d03050301840a5410402419a030030644070444e508502000305540104541703900d000046900b040c0080e14008001c524448030502040f03805890318 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 156717176 1250 156715926 156715939
    0x1e080c040911091501020f030304110d0503070b0c0a110316170d060b0a08090708100515100e01081003080301050d110d0803040203010b060403051b030f01110c0706090b0d1a 76
    0x4e450b00c500b0f212009075000a0f02220f0b400000f26a65990b24007007202d0081c0700486a61900601c0c0c103158040502e038038030503000c5a080504a079a1104841022500000391850226140215503070244a030001665520301441c0303820409680304544241610000d4000412030188130402c04803213003101d9074840e860300c04128403a12458a0041503110400d80710001d214540890031091008c43d400d0203c8501c000246012042c070b0040401410380103000400c942000c15440c0c07030135281c6032030510b0f84910965500446140e03c5001510909000d003203028a104059010b00008c0d20480c1200c3c1500c60464461899028034509015490b82d04007415400416401003102001000720155006a100b1002405000418401c0c09028059403002400540c00041c480050001100c0700307040362440070f02a6901d4403076010000d402e6440196414100d80c200003103130030100c030061102501904003454611040b07071800318803044600880c00400c0380199a03411001e02400e400302c0c010301554025029 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 156718426 1250 156717176 156717181
    0x19050c0a0308030604111201090b06070204110c01060806130303090c080d05120a02070206071203060806130c0b09010903030f260103060e0a0b150f0402030c041e080c04091109 77
    0x40b10540050f0380b0103005504108400784250041410b40312030140208455869030703c2e02c900400644500a41ca5401000c1006071070050f84460003841d1000000c5841e850341d52079105449070841d130341c036401000c007a0485410322180642100101c040795030945004682200c00c0d0512000d03901056004550301d201d083c02c00b007078603508030300900b40e103500c00005030b07555503150744165044e4403408000961045040201c03074002084050b21b407542010600c0d0000d0380c1c43d1500c5425127000002d440c07030300c0901d000c2821581003100440e51240948622440315041510300c00c000303001511700d40801002e01c202003951395282d911500101480204040a54a142c081c1c0214000000d000303001c15600c15003070603071214071840c0004581e50a6644010007587d0713603a07494241c03800c1020f016105580250101c030981d42594a03400914003441030b507242d0315600c40c903024401c03480c0798990803d690814044070f41009240c0000c0f444220307035a800d6030f010403034440700d15085201c941c030040b08580c0840003005 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 156719676 1250 156718426 156718433
    0x10f0203120a0b03070906030213020c0f0109060b030c010e0d02041d0703030f1116050609030a02030307050105160212040905070e03030a03050a18230a080301120506010504060819050c0a03 83
    0x4603d07003042030303040c0c0d50203507140e00420058800d03034040a5080b009603881c0003542c98030ba41c01050701000503810b0f243c460801105e484c1c01d480d030281e41540c0140d140d0f43c01050610b828070502c00040702c02d09102c0c0510100c0c4000c6443e6402224000e4421a42d940391180151480300004d41c0e01c140c03c400350b0300b02c19142e00e00a0480c20b45800d550b00000c1c40c481018250345070024840c201e188800301e186043c0c038506030800509a0002e1070b83e50b05801000c01c014010b840801c054081c4070320900010070301d0302d40a61060440d9218540c424215404900c180700e05500050072034080e070f6290b0b038012446540d10344043d50601e2114400c15054800002c020480702d03416401a4000d1854043c24480704a090f920500d031110602800750100101e0b42c528503040700c0052107941150340c60000c0d2440301003a511150303080c1e0026400034000401c40d41d038400400c04c050140328003401040f5000c0001c28203145d0242c3d981d1801c0d2202801d0101c402d120300051003010442c0c1140c480000b000222103644928 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 156720926 1250 156719676 156719681
    0x30b09130309090b0607020d050f0304030f050607080f0403080702010b060301030f0b090303011d13020a03050604030f020a0f0f0c180c03200a1202040f030606060f0f0e010f0203120a 80
    0xc0d0000345403120080b400f0405400781c2514240300500c417030704055140d020099500015501150a80b0982210604079603007071020784003c500032403401c0b1200781d030380c1089030501d03030002c01150421000b0000c00074134240c18054607812680603d0404155500d0030310a900620000c40101ea102d5000301c00081004106240300307451510a804050316502c8210a25640780000c0c0103c1c0040e44902c50110342d6510501c1d0f600340c1c40700c010034050316202c1142e00804e14214641c0c00c181c505070400b0b402c120502d5080611000c010304548000e1000c1d0006840b0b051503050300e90380003000000483c290b0410700c000d80001e0009003075844443c803003048201e095078000b03254001c0d400d80401e00300003200f142501c0c182c1420700d1460700311030a80e00d03201c1001e100303c0308000c450901901982d421f120124009481c00d40e001c7c041c6102d4040014041e08082c0c0191121801c00c1c029010015000c0450b000c080d0b20002002d100c0c1e1007800d06000014402d1016820350089040c00c21640d50031500700208000c154 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 156722176 1250 156720926 156720961
    0xc050705061b1903050a18050a0b040e150604031709100201060617090604032f03070b0c0c0c04020319020c01062603040608070504030f050c01030e0a030c1101030b09 73
    0x303002c0f1109448040c42003074107408244405004101c003404031400450040ca0014103c810009914008645500c0020004809600006c054507800f040c10f0003c00c0342050b0180d004404503a5030032166040d000016420b1060f8007009041840510b01d0240440c0f00505648110304024540c1c1c042ca548088024000c00300351240e84009038070100015200f0f5151000c45008900800103403140ba034650300c0c1a901c1240d404614108a640d01803c50141c0c14104054110030307141c40003565942d00036003800d80104601400a40b4690030400450b401c4203000a02c0005044080e103015841e0f40e00c40c1c0f0802c0a2120201390142c03c9800000d00c1c072000a010341c061810740d6001070b6008455800380c6a004501e2051003904445580108020310070395010b00181b0703034072000c6031a0444c0780c941c0302da13a10040e0300302049086955034001d10f5600c21541e058026004400c20100085c1140c0044e602c0052000b48800b6019154035481030040b4000d9110750092400303450302815051071800d01140001038240034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 156723426 1250 156722176 156722227
    0x510080f0601031a0f0a0b040b0a021c0e0103050403030221061819090c0b0f090406060f02030412020a030807080c010b09010f03081b010e0706110d0801060c05070506 73
    0x30380c000888540c020b104072a405030504207842c0035030164009010683c000380900c0d51b80460801d50016890225200500c0601140ba40550f203d103c2d2410183c5001c1e0740c2c28400405000710385804401d603501c0034080c1d082c0c480901e400310b920f0711241001d5000b8480c1108100054814042c2a0820f128100c00540141419150a0209800c1b551448010705041c0c8880410040da103a848116200740d4110f01c00c03403030081c04140b000c01d03039840c610304540d40140d219225a050100d402070540c035192151100401903411321894003020807a00a4581c41940100c0340e80c0c4150340c900783c0540d200c64410340003444d4000d400701c4e42d51000342401c10315500180020302240d0f08210300100d180c1040c1410504903006510101c3c4007904540d030380c6e0300c2c54111485c00c000000d0314201c0b090818400f40134028815001c2c00c0075200c00c508000004041404143e0240c1c0180d200171386a880312075000d42c40e80d045070100e241c08000c0640e00c0c502a800c08040c2d500813540b044010600c0c0d10107098402151800d40c01 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 156724676 1250 156723426 156723451
    0x40c050a14032406150c0109030c03170c0a111204080304150e0306010e090a020a0e090712110d0c030609030f03140907140604120507080d14071704051008 68
    0x900d04080040101544859a4000201c00c01300d204c1e420240c0103020301d1503404009608041803070711070a00b100c1c0420001c0c2e001940644120703090680101004507003940d0f02407403410074540040001b015100b0000c44404004601c085100a42c0061007040318152810310030300e03551070383c0340e104a549070801d00810540717840d900c00741d2051034003981e541003a22401601074a038903031801988118034400103100c059a4000c0d05c041c00c005940d500200b001609200e440984242405c0403e245000c81b290415001112038148010218140c00c0c95080700310403c440e00340c08010075280c080a10502540010310031401c0001c801c0070140c2110702d5640c40d0348181d44c100f00c80607003051141c0b4010750603078800c6825040000c05010b9400fa01520348035454000e0400c1c0d28090b502c0c4185021240640c0c0c003550180c0141c1c10610a480007800a450208243c0c038012854040040c00301445128003080140003101d01000c0002d020038010a0304d006000040c503001c200506000c010700161802c481c81c403920781 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 156725926 1250 156724676 156724693
    0x3022503150e072403020a052109010501090c1b0201090e040506160905010806041a0a1206050a060302011d0103140c0d2f070807020303040b0a110d120203040c050a1403 74
    0x2418100b107141c08a01307180c821040400310311054000758421041d05003001010841c0c070103142c0d101440030300304400368020003913240307801c040e014211803040c1c0010101034104011020919440904862610150b68004081c00354510068800c2e840560000500014840411061100102d9164860b8030015094420a501350b1011106103969000d82c03404160310501003549802c05500c10310074200140d81c60752a0207542400141164440c3e41b00f02c0e28034028905800400c00c007806800d03000410b0000030b010140c11540081c00e084404151790701a50014404c8a40310ba03c02d03007000355060301e11100b0b100d140c100311405800355481540342510071790414403040503a00361505800190b442c201d00400e1540c0b0041d0945840d640042c3d001d039030b1440700b8413805026980c140014001050601c030115594050124060b04d04a045500b10703166820013000309400d150030520f842601361070410b006903070703a8651800001d00c0101e85c10140c0c0200611001181540c520f50004a00720700c00ca04880456 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 156727176 1250 156725926 156725939
    0x30210110708030a0f1e0903120b03030702240d0c081b030114010507140c1801030b04060509010e0f06010501031103011406090109030b0408120901020703022503150e07 74
    0x1d115041000304022002c000288188089500880316150000400300c0c0301011000c4640c544c0400184c00d201459854081c5010140c00490181044420000034010300c0c5281001945a0083e0800a4020108403003a0007500b00c4180450446921541800d5100c400041c4504010000000d0307042c045418200030482004000d5050504080c4010400385140c0c00e11071040c4200c18294240d606210050110400141891040c10549401c6000900e031285c144c404001d844492a000070900c0c1b10160300510104103200301c65035105401c100003003016102c000805005146000740c00b5894058155002c900b143d010070300c03904840d0240e8081c0207403281483c1d00b02145c130080c440c0000c911401e420300c0c41e0381d00b071140203444a008141042c034016540d80c2c907404881d00f02201c0072940000c001132030042d08061884401d400c603801340c0085091405c143d4000e5a90403804910f070144c40740e2062480c40c0c0020300c250a802555120225075071101e0311080326009440050380500d0940103004012564 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 156728426 1250 156727176 156727211
    0x2070605070503060a0303030e030702060c15060d05030d02031005030d0e0415050d0213020f03070507060c1704020f1f080a0509060709180609180201030b03010c0903230604030210 79
    0x5001d00402550090385140c7d0150300502c004507110105000501c1000b001d03944140103010001203082c080c0030100303017010300103001c4000101a1845074195480b10400701e0b0b400801e803100310140100040c0e59881d144c290302050107084e8012a0706100d02d521000195600a500780b019410a80e4248404503040c001301ea03800744070b405884d13000030742440020050701e0401c0842d540e24140c00401450582d1071000540c0c07503401142e000001c100001564400c01c44d5600c2101040e0340c4604c0d111504010307641d901081003001400c080d00c40c0c00411002846a500d00ca04d0405c80203840f44450303001032640300003425000080310440c1c0d000303182c4000526452400700d0103078407600d06540c45040e96814441d41001850030440385142c01692484040341131003191181e40c504100310b81c030141501010384001806e40c0c142e008103500070f0b41007050303010b02250000d8400007541d5000c130ba0101e4a405900e2800d0303800305440030024030ba100300001d01c414903030007007030482d10103980c82001e00168030460b405108 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 156729676 1250 156728426 156728431
    0x102070b0315060904020d020301030b1603090b0604050a0609051e0c0702011e0c33060b031b0d05010b070506070203040803091309050d020d020136051f02070605070503 74
    0x103040b400c1c050311000c81c0b030104000c1c000640010001030a001d10544c807001240c2098004480d04100c2e281400400e0a1810007841d040c8010b260501004030b2036511010201006408107020300e0311140031440e1110b00b034200d00081e00ca494401c120b1445c00300312400380c0303203110040c241250000c140450b507a0003101080742c4503550180c42d424000054049010f0036141e800480d0020031201015180001e09500c1c29034466200081c4102c1c170740e184144032411140a0307a00001345040ca048020001d1b4035403041640c0e40300140d521007011621117284002a68860ba02c0750f018468546800405c0013580035010300185c50007101101c0c166030712004240d0703480c821130048284982c4148a0301b801d524041c0e440030881105000081480209542e4061410b4413482c01d20700560024841508156424400d81406081c03d981090480c0c10364803640304400740c0100c4042c4201c2d0801407040a00008101881800383c102c0c015058800d1303920303001002904211000c55001c0d0a042c0442d880300e02c52000e490 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 156730926 1250 156729676 156729691
    0x607120e1315030206070c1701051b070c06050c160e2d1b0f190e030c090a0c03060f03110406050103060b371101060f06050712020106050a0602010b0102070b03 70
    0x40c2c5541542c08101c04d41d00403810448004001e18004100021800409030030301e48910004220f03820b05103401104605d80004c0d10000c49018000d203804503144140d070310102c07040c0341846545c1d185414100e030b040c104c1d04111038184041a030340c0003940c1d841040001c0c0c46400e012050091044061301e8402001d00c030300004160341c104143c0403030001420007954403403002c0e962001503d0038000c0c80301c40800303030040911443c071001400c601c140229040110b54280f081e007100548210300200e400111708040140400d000290303559000005c041c020f1b81710388050310300320381c5403040540e80b0310b0014a00340600044d10b008608046000030035502a00411381654480600326090440342181c90b10600c560115a0664129005050b10003421000d41c018403c050355480c9201c2c100030780d03209800c2d28425400031813841044c0c88100200c81d0300109450400d64011860b0048400c0c05178128050041038100c90752002002c0c0340000c01b03d07015400001180820303001d45601c2903503411580a140800c85801 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 156732176 1250 156730926 156730961
    0x6090d021c050d0209040608100609060828020a030b09010609020a0503130302120429040b0708030a060f0f0e06030c010e010c240e061b0406030b0607120e13 69
    0x1581820b00800151194106038400181040c21100000e0155201503100311a650400c0c3c5200011900034042d035406090b13510700c03d01c0041e180980f6203a0398401c011042011455401d03600e1440380e6417400c2092269002851080090b407241459a001d60050b510306985619204000a0700e680d01d00a5800d49022a100d00d0308503603a00400018240704c42b40100c046000b0780680c100070f01d086c43d0262025200016a004402c14001201525009005000140341c070062000b00418082141282c1d0b46a90225060303880c0e44510846102802083d0403440118400c9174010070004d42041c0940b081781c210012441303031a10317107405154555900b2210340d4000f40d030300f080e500d05c15405110180382e01403007000c03400c81c01120303400140340542c03810601454040d120720383e200203400200043d039007100701d010050180416480c0351000c1ea214a210b80c105164640c40400c2a0b5038503001614000f41d00b00141c00030a01028200a003809150003031103228003d0f5a0701440314803a188680c002d07054170b42000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 156733426 1250 156732176 156732223
    0x605061206011a091206090105060a0b04030b0a0207020a080d0c0c06030510090c090f03051507020303010b090904020d02060d0c0801080a23010209030709090c06080f0a0518030c06090d02 82
    0xa00d4a500120b03406400174422140c90302c540004010062154000d1400000c85046c51010019484981e500100c00281c007400140301040d120710500b038008040000c01695040d4910204000080707075800311000f401041ca820580f143c010f101040e02a11840403038203d5134a40c80160101c80099408045524034071405001c040d406071301c8a4151450b5041030310410b40d1f502401e0071031070502e0b002150b0326000800c010010044400445420106074005181150b040000c40d07e07131340c094102214032500c92070300460300755140c1d10000c0740304030380250040c0c0e13070f440002c00944092300e00e21000d10001280341d0000203a2060209008088039406035510384415960b402003104038030201c12546080d5030820070314540740d408008110041074030410210708602542410301300d1034495880785061204910400015000c0c00344401e034014048140006c50b0741f40c00744c03205031000c030404604c1002c3c17000160b6008400d20008809111f05110021a00110020b10080303850f4000e04c1c00b4105200c3c2240071 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 156734676 1250 156733426 156733469
    0x30e0f1e010c05010e07180c02060f040807031b200108090a0f06061d040605060607121112030112050705030a0309030f03120606050903060601031a010e1c060506120601 74
    0x2220300780c2d5000390300100f100018091110308002c642c2c0c0c8080703001c0c007031a05403155100b018003c0c003c140800340042d28a51408091030100d440004000904141000844508060003542001d820200a41e00000540c0701440c00140c00840171443c0c6081032140d03800301d00303e50b110700390440c0300d4000c2d407002c1d1140300c940b039480c400f243c9000e410032198a07803240d10200f50550318103440d000c01c040380d20300c2040310300b42410050107ea2014045c0ca0080c0c00802c10040422003d0390040c901c9141860100c0204644a03451030a03d001401c1f40c0321103c100000014000c107506410803d4240124103440c080c0707030f891040603603a040c0114010089002554100702080c2c2e41c40300ba6002c0e50281c24442500d48201c10044100ca400390840d8012075400320310405a030408214040d8000c100382000c01c10041d1450f4980036000d0404502410440400d0310100340e070302c603140300d1858031459146003c14451940741080152000b160450b004488030400c0c50560708001030050b0484203001004070b1070095911 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 156735926 1250 156734676 156734687
    0x103140f0d21020a0804030f02060c0f0a03020d110c0d05160b0c0c2b0f0804170c0307060204150c0c0b0901050909040302070f08030a0e060d0b0d030e0f1e01 69
    0xe03002c2c1e480c01e1498002c45409603942c0000c00d640340702560743d5403052902d454040e1030038038a04085411036220100300300c2e40c2d007101c0e0119150a54005000381c0c0701d80100d0000c4021340305090402d102c02d4141a480003183e43c20310060460040f494058441807284440b00700ea0600031a240301410311948089407010034861108180c00c002c1d810f42041c03801e80040c0320107150141d218008130400c04106c0d5521086426103000c104041b0b1285020713090829842c000801081010300044c02c01e18048020000710180b0008542d80184078009403916885181485402034201e84140d0190708010324a0580c01441410070544c826441034030110351500300060425950441c0b940e2134184a0104031001c01545c81804039840355200b54000c02c00d42e030070010705011030f40c100c0d4000b2225074428072444502c5034118000a5007a01c040d45c0340e83e11000001d4900e805000402803d40d000140c002030303c03040c10390110300912506420b0782c1862071942c45000780100388c0c0301c05840841a000c0d0f0302c0000c0f055849007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 156737176 1250 156735926 156735947
    0x210030b060318012306090f01030803070e120f01090506010f05030304090f0603020406080a03031d03390d0f0504150305040303090803100306050c0301030f08070302070306050f0103140f0d 83
    0x44000180d510410500441c07005e40002c4182803015801d0100440c52500c40f07460f944c0816910100e03102035244ac1c0d5009564000941000c0502500101d04092502c0e2103405045408440048030000f61803001c82d2402484034480913282d900501e030001c074001d41d44402d03810403544050700861815281c0085c07040100b50b480313620510036490300030000140e9600e018100103414014044c0c1000961443c2c05000c0f944e618600e1981c01d50908000300e800c1e03201000703940c0d44141404204108011060103025080300902c50140e036030750301003d2515450301c00219105000c1280c2c0310741c5081407070003030252840d00a51080080c0320300010120a0b81a10941040340c000d8800d06020540143c2c07541c8255998000f00c1d9602c01141c00e1090410600800b8010280c01004d000302003441c0d9415911590198031000c10068807a040001c3c0150030144200031520096802820070003a41c101800c40600c003190a11056030030011a41c0c1301502018042108d20011031701c1070081611b1080c0d08402d96880704034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 156738426 1250 156737176 156737221
    0x15060801030f21031a0f0918070506190f0c05030301090209120106091a06091309052b0906050a08070e010c0507030b060909061006030207060b18040210030b0603 71
    0x11600300c83e02c0c02c40d0800f1210011031141c074082002210b1106803030007503580e203182510070205a1480b1203291100c00c01260003803190003089030303113080c1c8030003072031422100e80e0156820a40000d0380016500c088514440c10034415601c0394840e0f50205000c807442ca002c420040d0036038104000401140320f02d41d0041654480140508024500c40e4103541e08662056121609098580d03041c050004c4002d401409004422500c003805c004201d004503000086d6000d001307050303a58a0f425501403010412100d03001141ca82c0600382d001030500501110005004001c00c00300749041c10109603a80604207903100e40040b640e801d00642c5e20010101c84039440004024180a00c14180030046517081c402900918096121481caa0034450300340510111b006004150340c0d00008240001d040340d000c000c0d021180307035180158494950313080c03641c0101038540c1880e0380040c0c034840202074240c00d941c41034480c2c0c0c000c0b00c850306502d40410040e804c0d5400c840c40240c2c881410400281000920103d02444803003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 156739676 1250 156738426 156738443
    0x204052413090203061311060c1f020f0d06050f1e09070909020a0908070b040602060a1a0d06050403020d0810030803040609170304110103060f090f1506110115060801030f 75
    0x52980100b410070f45d0684d808202c145100d2400c50500040e406900d4403424140c9507070740b5007640c1041d1176844004041040242600055034190f4400c019010740c2c00e84100f00c1107607a643c10284500f04003c002920409014501480b03c0d402140b0703214950802d202d8042c0303444880007503a0020031003916001042c84003440b644513404208a0144c0c800307004110415101e07000380c80d04014100740380c442c6a601c01c01c4514000c0200f80031141d80400d00d01e400c591901170104070b144d00c0d8a001fa102e20317a030214090300a6111034040c0700744202034210354011030181c0c0a41c1c82400e000541100c031000201c4520790004c00c212010400200c4604c01103510074002c800c00a2160340c0d540d01c241020080c011070401400700841400b0902c48024010840030400f42003c0050350b1504100700d0801400c3c2c4180540c4d195558000c0e10007040703a42020112860040701410081d89602001e841c2500030b900c00ca00640c6403410800e001079201258000359240f5440d0b50719241c0c43c590707030304900d44002d00c4202c0f42c490 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 156740926 1250 156739676 156739691
    0x1060b1b0a050115030b010e06030a1b080102070804060807110c0f030a020402030a09020a0b07111512070f0314060f040518010e0304152c010504030b0a05040204052413 74
    0x40c0b0070301c1080c0c403030746a101041052078910f0400040c0000103800024403801e01c00f042c8402550005000a42c02d81c4c006000e140310300454100170341d05000c0d50b100c0501d95000181c3c00c8200703c440b81c014025581c00791a1302b007523900c420b001240d2050302d03107100b03480303903070040b0003c000c1841d0460f00c00621000040464410000650200e01a604103440710b40589807078803444003c520309541c6802c040c4c90001c001c1410460140c07991240d0207002c4c00300c40c0c090350007002d08d11101840101107540f00495035840e680b59040018004207011301d59200c0030000b81c68a50315500701800040340c24000c8200400c6e403c0c2c1c20301400c007000300074000501401000101d584600025400038002c140e4005038a50186484900c1c0a100000500301c03403003543d007084052036900c2140c04041007036090313101d00400b12001c1c41d6443c01c0140d550340305540001d4082c10880041101e03200130790300030512452081c2d03014442034440030311641d1700070011040f071240d550540b9009425428a82c500c2d50590710a85004104813 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 156742176 1250 156740926 156740933
    0x7060e15120a0e03070f03030518010213060e040c08190b030d0804031b050a170c0106080a021009230604050a0801021207020d020c0402030c0c0105010b0a08060301060b1b0a 76
    0x298000854004100403000c10003880700214455801002d43c43e80146251001c159603040200b4920b08000302070558071004a00c420400c000350f00340800e030510007190f0740e1003041030f030414162042c880e600010b4502c00c085101404c203400340207134803c880e44034008a619001704850f80a00c10440113040e503a90340d00074041079941084001c031405403a440d4400542040c2c00c00030032501540003180b03641340f14a0742d90000260000340c440780450300607100b103400301d4848501c100b00c1e100b440e085401c158201000480e001c2c0000c0350000444d442180c420360701007511102a66814000d00c03400e05404d02e80c0148803404901200340f1f000d91003004080c189025110030005120a8040d0071008050794086014116807122042c425082003d0b40000c0c170000c00e45840095440c00b011401030f005a40110100381e070740c82807809942101c0003082c000c0c8190340c0c540501c20801d4000c0c02400c400180e10300c1c08a5a241010b20600b015240d56003282e41c9050300000203101e06000c4000301c1c103000d2060095401c0403 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 156743426 1250 156742176 156742219
    0x60204030c030318030c0311030a020a150917210405042912030d0b0102070e04030509090a020306060703030c0c0f0c0807050102030c100c1112030a0f09030207060e 72
    0x9140308100c1c0301c1c551415030034000c1c6240108810400706004001d014004694414880d1085940c000880c0860400650200b4108585514002d4011054580205070307104103890200304d40045659071140107940c1c02d003107040d801c444450415150402010302d2007845c05c4410000107141c81e2082d140c6000e94038000300d0201d4025a030304ca502d50034940d121010286550f48402c403003140440d003443c0c08041030704600c1c1c0c480c86804d480c3c401240c0c2d9205000d00b240d00074840752004007089040060240f4250801070801d41c0040c151510402540300005c00c814070768030a83c0c0c05142d025000a00305040c43d9015002004000703108414085400217500008a41c0c400c08030a85100d031841c1180e0a282c0410a49480c800303406c00c9040d50403e2001101682d000240402440384403d000708074180000c030143c0c1d290206103e1454240070b5080041c100b20f0701c0c2001580204003c00003001b0005d40071416030b0031182c0e061001030058003c000c08001d03092040f940c1450320b0400038503400d444030100c405100c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 156744676 1250 156743426 156743429
    0x20907270b0406080105030a0b010905070311030c03250e19081606090b120f04020f0a0e0708010f0b090d170408241e0702010605041811010207060c0b06030a060204 72
    0x3401407000400348003156108401c68014442940241040001a41e0712901050140610940706130b5460025a0452280d08507400c54000010442c1e030701d09001c001101d8a034000c46094501010402d0500c04e00442e00401300c4500440e6039900404054010401c52400980058868a48a8114040b9182070107102c240703a42019070303030041d2400713160000180c40111258410410000e040c070024127400100208035a10800403a5255603954951000401c4490302980e01604508010700102e0b181c502154007501a81c1035450b031070312a81e40c0f103088000e0780045024012101c502409403580300c0c28003001010710144074150b400d131810b05a02200500f504aa48450030301d61261002510540401050100c2e480d800e44241e60741e4546049020340038807110205403ca028000700240d0071034401c1d03108601800c0000c0c001d1049658504040c0710500c001d860588880300d084960301c26647c00007401004130b803000c1c0ca49002c1805140c4036080943d60041c400790b090700980e91a8800101640700910 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 156745926 1250 156744676 156744689
    0x30504020102060901020301061202091908060f01051903060f0b090907050a0b090108071d13060503010c110d0c0524180a0c0509061305090708100902090727 69
    0x10545400d0000a10b04440501001c0e01039204000502c426984141103a42c1820604000350b522a0048041500004040e040c0500010300d440c003c05c240d407000c5443c42c000c0d2810004c0c0c81041c0d07201e90801c80404154290b17803040c0310400e401000020303030039042054815054840095184002c1c3d0100d00881c0040b40d46070703182d40002605200c00d2a00c3c0e44550b0241601b04030740f038205a04840041c18800c0302030042c0c0d01b8007904025040003d0380c2038a90800802001d8901c2c00224440721404018202a0103214070035428040d0111720a0302c02d030881402e0480740750041c44d0b40d400c00c200903070f03904c19400801d07100c5000741884035103580100c0340b0101c6040f65801440c40c5c0b178034219100c40c841d5082c10440002e03541000a400001c2044000c20038141d07481111b40186603202d0100081d050307101c015180400c0750804042094038900032070701108491000f0b09464084480742c1100c011070304290300c020b5010340721801140845103d41540105031245001c00c101c80c804104100c3c50785a031035030099 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 156747176 1250 156745926 156745931
    0x60f0e0d0f09050f09060a08150a0b040c0903060b1516030201060f030c03060c050c0a1505130b0c0702150c0106051009241b0f0b0705031e151003 64
    0x1014140d010140091000403842c02d1902c0740d0624000560550000c02c04030b100d000c3c150003186180d41e860105900800001c01150300c5604200181c0c01d18400454100000c0d6142003440350311401c09004420000b03406e580c500da10303541182d83d0400184004890140c011a410884641d10352070b99000780b0781540c0303050013803001400ca0f1134000e095071075641003070000c0d104070001003000500314900b20080d01c2c0c0c04880403545c1c19600604495502400c0701c0c90505100759540e400c20b0001001c0140c90214000509020302d0352500311a40d03120005040040c109584000042c03d0406060003170701d8030390310040083c4508041080c404442e0380003041100000d03551400100038600d4240350700c00d5010494201a1000ca2030314001d44d80b18503014445000c04048907000d2000d092094454643c1c4c1c03031740c070700c680c1c082594a4105058940403042040700d0100c140320110741d070079000b0001c1c2c0f0312a10454140c03115001c0c11401411076050050003484128441406500441d41e448682100840855600 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 156748426 1250 156747176 156747193
    0x8060406050a080304030b091908130e06030d1211031807120209070c05070f0602010e01050f090a030f020109080f0918040201051909030c030b010519050306060d060f0e 74
    0x801048605541c04140320300c0c10303000b0030001c1c0c0d2000300540f0212a00807a070310140d9030f201c0075914108550741c2085019058030403000d00030048036402621090192241c8900002d0701c8451011810109554480e80356000800c0001c0302445254045038880c125680400c0030910703000c0c4058150000da8040480e529483c1c48070310071a80400031038004010b002d814416101503a00030814422000e8a100108410103500c0d60900c401009002e000303001c1f81151489059031460000e000f08031101c100d4105500705070218042e10996032030301e40621900000f41003010300031342d401e441c3c03001c001c0c84482c1503540760307030300d20002c110140040c009818002e06080da40382482000c0100051292088102c00702c00f00c004d000150743c0c05400d490b0f81d0f07502e0185070b001043c0c01401c2650035003520b61004062a0326003401101b0803ca490889048500546e81c0019070b131105c00d8100c00d0300b1010b001e1141c143e80a0381c0010b07110b141c9943e14940c0180100b800161209103101e51b002910441c2c00b001010f039002091 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 156749676 1250 156748426 156748429
    0x30603120302070f080304020402090d11010909062103090b04090c08060d1104050c0d0e0a02030c09010605180d14010605030705010c050304140319140606040207050c01030f0b0607030806 82
    0x2540c04214609107421480e2800326511403007404801d0130050700c4288084000380440d01c2d2541125006031000f4188103100006140190400c20101095030001e84484400910703600f0500891080d2031a002038070002c5c0c1d100d00040c500445181000b5003c02030800b0000905040c01c2c00180090842404040350f004013000340030700030802c050503090082085902c14404034000c0382d181c0810030801c440105643e04c648000c14034600480b0100d1080074a01001000503c0b000164001102e10075026900303095104010444580e13401d10504005c00c03010010034000d030104c080203260808000300860000c01c03158a58000c0c8400540b11180c03e03030b648000501c8a403504111a90041500b440d142d0302c40c01050740e8842d2640550700c42c240c1c0c0150080d813034940d65a01844010701c401d19005000301144402e0510380904200e0344000001c40c0107000c04032f52a8200b82c001c44581c117410800606840072080011001488040100003400c1d9484182c0d03811503035840000c0035040d00030ba5803042241001c20 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 156750926 1250 156749676 156749693
    0x3010801140108030d1505220c05040503060703090201140301260309010c060207111504230a03031b170405030106080309091303090803070f060e070609150201060f06030603 76
    0x10014000c44038020700401c03203a4000011201194420130703012607190840251040340201c6500700e00c0d0f00c000440300a240c8040c40109040c50421b001c042800300d440329601c2500d032480380f1b021312a059002040010415030003508030b000154030600d044503440b0340e5400481550b80013a0014000c1408502d000c5e0f014031400f081d0344404ac5401c20207545821051800a40180503203c0c008040075008954901402641c0c60140030081000d80301840159251401b1401030b40103024900440b290a030001106c4118403800744131103031002d02124551825034030152054243c0c06030342192171104110b06400a14104da010711181d40482002c2d445604040825003503550341d03003000407194402e000080b00d5a0303902c2546500140c2903e0364210452141c10225500049a00b000000740310000303030802002488450304032820b00404041140b02242c1600da41c82d50786500c1034400180d169601031080303544490480d031440c6c145000004055658401c00087d81d002580900040380d0740300c00420500c40c0c0c54 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 156752176 1250 156750926 156750941
    0x7030c030c0201050114010c050102090901090e0f150a0f02070f0b010609171e0708010e06060907051c05060607021915050a1710030209040f17070b0c0a0c120503010801 74
    0xa0009001300e40c102000741c41c56114540c1e0840c104890302c0990002d0003800c1d4101c2d4880300000c0e088000320340e107a42c010b50142a00e02c0c210082031050109940c221306010811780074624141980d82c441c0d0b01c5680f00c440c00b50103404200b0684035802c00c905000140950700f25140302d44100c031142d03102d62408a02404030521644010040d06c48020640000a00800c00010381502c103400d0001d6036290910086c50040650400600b545c03921102d005400000650b8502c00d800440b5003c50b1583d940d43c0443e40d9016075440110820f40500710402600e0b8650040c03640079101030981400d10140e9000143d41400342d1820324030030520b03044140041018020000200b4405082c800d20300201980b00800c540e040b189223004c076181e14000310703410587c0850003000468005001c403045081c0740c1050089680c14840483c3e0b4040ea240e03091942480380703c05c1d01c3d0440c0c0c0144484003103a40c1e03010300f0350807079204000c000304200c3e0303d1382c07240006000c800b05c0c012106074a80d54151650b0400c00c0450071200c12 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 156753426 1250 156752176 156752201
    0x60603020408120d1104030506010807090903020312060112090b0604050c0901090909051606030c110705130b04110a091409010e010303230409020915040b0301030305160b07030c03 79
    0x4110900000700000740066440144600f080e50f1103084400351401014a4070540c040e004c000a400014448000303080780c1607808400984549980c3c80400004031112140c0040c056082800b25000092480380c5855014406040c02c840d1400410410002c4a0218504562542203d4180201820507114040d0700c10b01d074000507803600140c40d0010300031800034414058181d4131026030604000003030080340050040581a048520b07160f40010b00034000c50350395440020740881070b0507040703d0005466402c075080a0301c040110592190040c02602c4440c050380c5e00151500c0f4461f0801200800030310030100142c2d2381d04c1c007642c10251021406c803c80559184912803820040c440b0440420b42c0904490b03050610038101c104c141d0701c00c101c2d65407109034034018081c0840c2c0044d10b41c0c0315030010b10648000b00c2e406041e01781028201c0035a170096000740040f6a5091005000180c00f07400240000c3c0501150107e800980e60365441c08004200c40802c00030340c0354402241381030703014040ca0480889 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 156754676 1250 156753426 156753431
    0x10090c090c1b06060905040b06011719180c03140d0c050c01030e010b040603120f0201020304080a050906040305070f140402030402010f0e040209090f010806011e03022205040c0801060603 82
    0x3505500524120201030b4610340c9200751074294040040f90b912920040c28203082c24061850b01e070600030040e4034200d810601007550b8a400d84912848100c2152040c0064989828024860114080105864114800c1c1c44150b15400c401050900e000600154455614154104c07424102c550501c5000603015045c02810074079140010008500c02d51103038005e282c00521162003418160140059125058200d0320b0b0120100c2442091450031649100c1510707100c1c2c4080325980c040b4200d110885014010001c28040f51000381d01c10341c01405c50302d04c000d0400303042544031349400342045490750064085800100741044407074080c004241044204590440c1546050340000c4d1008402114500400400c24004483341d911541511843c08015003c8040e500c0d00802101003101d00703014503c918030030f000000500c0240c81c08003004c0c03c8204419030909925690a0100c00580d06422030400b1003d05600c4250b50554810944140e00070a0603a1a1616005580d030031900260840801c060 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 156755926 1250 156754676 156754691
    0x6190507022d010c14090906010e041b020105130507050d050705131a0f0607060f18050a021c0309120203031209010f0b0a060e010c11040c02160608070804200310090c09 74
    0x107175001d007611100c0b10240d86615441c0c0d10303000100d5400380c0e1510495403140c50726000034039102c05142d410300b2000850b0002c00c050740761071480d0714406804c0c031b60050180e8042ca03014441c0d8144140c65220f4584900100d0703003400d0322074000580d81070100300500c401e1030f594207010000d079200c5170080350a20300070340d444c80c00c0403403240102d001ca1040d1280030345a117485010719104011540d1124007420002c200703040c03201440d403030159156a80f458017039100d020740c01e00781105010300341c1c0700840040d403680360b204d5014648482e032601612103807002e9a15010038045803148427050b4030743d14803c0c404140000303400701541c02c074002115181c416041c001e90789030100340300c00d0350030110341c54081c0401d09081207031286900d01101544004050701d5046803c02d456000540d800152400112000300c91504505407104c41c200c4509204803a00d500162030240400d0209012461161540c86000400b18988010101191500c0c07042c00d00c17503040580d40c581c4a8140b00d4401a0700d000761402210a00110 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 156757176 1250 156755926 156755957
    0x60406060519060f300f0b09040b090c03100501051c0305040b07020604090204060512010801020a2c0d050c0a0e100504020c0a0b0c030a0e06190507022d010c 69
    0x400b0340f40549030600003480e642050b0280074901d8075000404000d140b0283c4144554000414029008103a1000341014820008280d81e4020502ca88101511420040d96030b92140d240c0c082c0040e00442c032a002d0070124103040d84060044280e684165840490154076000501540e5071b0101309480b01440d81107060000a54004111011165215110b5440b02d4080c00021041e10865205000c2c4a02c0001d0001329550010090440002461a0a03006030b03650880c0e80d00381d100c2c1207200c02c001506030400c0041207502c0480c02080c1502d80070a07040b0054560701095038a0399440381a0743c0c83d440b110a551240c45e00c000072130040c0c04500f01d00c4980381800803031441c14034080d000d09849190089007915011804100fa03d203126000300c141d241d981424003d140241c0d01c159001da40031418000011450140000c466000310326500120800d009214620001000301a11880850051521000041161000c1e89181c0c0d1161100c8075800141880081d0031a03884146040a004035094a103040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 156758426 1250 156757176 156757219
    0x18082a030601050907110f16051c080d0f1406040b0a1d13050312060406050609030d0e1c05151503060a0911090a090309141c020301020d05090604060605 67
    0x44403c00d07500c21100da103500c00251464446403000308400e10520305140c0c035040c80001c0d90350301c5039100ca1902d48040e03104c2c800d00c89401a0b076442d100c20301c40004c6030840043c3c005c20017040c0c0004020703000619514214041d1081d940720706940fa0b180f1a6400501c01e10b80340034840c0054646d01100e44034070051529102128100d0000c0a04011070701071400640f007807a20b0608071050661003002d9036a20b103203040d440505a9408d0b681c1351700407440e000003c5010b0920400701d560f60a4007c005040d40e03050f80c20f00711200c2c00c00b00100d90304030b00640c0c07802c1d105442980210fa08039120303a0240c1000b901808040d143c049001317054110a652600e28200a51008640c2641080e00b048002c12200c5039802c02110014205400c290003407143c41c10000901a2036101c0c542c0136200e03541d41440142c3e0348012a85000d8400d05c560341c003132000110202d81900c18109451540d01c081c0015040141a1840381c0c111042102c6044064002c0010030042091501c200000f0348000c84811048210b08001d4054 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 156759676 1250 156758426 156758429
    0x9050115050313060e150a02040605040e091c0f03140403080402060d02090a060c050120030a0b01030f11041d150603071b03020714040614090718082a030601 69
    0x2844070000c085202d41c1c002c1029112182e410103800d2005910858289a4920011494040507440f038004110a02014000c48003140c40aa45050400341400030300c41d444c490140803607035a4414060303100d000c045102a40b141d01c00690311041c0c20010b68600150a4070400145d2400551510081000007504440030710b400503015220a611441e03a180a00700900c61000d4455000346118800103103682c0c0b0454540e0031510400c001d108082000d149036503023600c4280c42d054020010300006881d04010761151800e5007051401140c0400950300b900c2c2103402d411460038501000045c1841014010b000f4440c28a611902c07900451414001c1c400c02c0300c002100244c419540003010401861213440b00603208006840010036003240b514000e96030b8240c030f2182011a20380841d00390818600741c45140200c90702c0507688a014000c6008001000744010070075803e0000c9480d11802070b40c008041c507006820b0403002800340c5c0282000710400c0c1402a420052a0b0401400011168602145190 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 156760926 1250 156759676 156759719
    0x1b160603090311011a130b222c0c011107060e041b17090f0a02060a03060b040303050703080a0203010311040504050c1003020424022109040606020f07090501 69
    0x9501d901c185400c03124841641d910b21031a42c204401d400d0340c050503040d0324201040444072584c140303c103c09203005540c2032650705a404858504d814800e20940303104150b80b072251200002d40b8482c102c07807000304801d10a8401454000c01c5200c403400c01420044a071209000b400d00e10002f4482a807075690300d040340d0190108224800c0c030032082d25151508210221440520400110100d5500040ca40444014031407031040c4070b5000b04d400000b002c01c41801921035940075040c03c1c0d140b5000c0c85a150302c103580d00b808041e0380303090000e90002c0a5000c0d00245220b95283d90b50307000c00342402000070034007403c02004140304000420000e0204420f2008118098401080070780c0ca41c1015810100b0401c0b8054010345850030502c0f030154594002c2c801c2d03a810751691042c1c2c0781c1040011400e42082901c00016a1064050b4440450141c02c6000107501c80c50701c030751400c14607102180c1544c80650260025074850b4403105020401840000007400301084100328943c9412100a410103c030100744 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 156762176 1250 156760926 156760931
    0x109020708070b0f060a090203090a030c1505010303080a14061c11150918060108060105031503120307080f07021f0207080f0301061b030503070f050909010603021b160603 75
    0x410441030805807450683c0018941c8400e250440f0902900d0808441c0e40e13108041480f000f00341c9403940d1090328015000d4100030400003960ba038080e140b1228044041d00c082202c454028580c00c843c7c02260b010358843c3e500c0510505116101c00156010b900b00129440300b210300300a0542c840040b041124640540b041c601340d8403c3c10300030303400000c276458035800c028541d0205000440b00c100600c25180140d80420583d29240016103000c0800c1da4040c0c0090301c0d4001240407580304170083c6411000250604400200c500006071900d540c40400409507080441046800d94025034140d80c08400c0319420a00d92400c0341000f51140d5155092001101d0120040d00104115506a82030715a20001c441c0d6101130b00f6014400d0f94100348680400100b030440e42c1491803050070154182c5a1b0700d074980c00d0564480070f90556200e6018244c079410407506100d543d40a03030700c0760840c1c0d00a004e10784006980780c10b100d00c4803880402240c0115042d600c4404003003540844400020100c840e00d00c0c00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 156763426 1250 156762176 156762187
    0x403020c1804021e01120608011a03070506040e1012050604030305090a0b0a0507050c0a05030405190609050f040b040c0f020106050d150e24010e07030b0303030402040e12130509010518010902 84
    0x1a03406c200e503400104015450034501144100c2c05600203000c10101190400c4e140c001c007410190b40e00514010290004c030b00b0f10041209210825400b40c00c0f0318114044502c507500c84880e84e08000911000342d4140d400241071105141d010f21481d9004640c00010f09581c014a80b05c10790401c60103040104000e80e180c0000312280c0c40391050f0f6408440d4582600c10983d047d003405640c0b60454089c0038450040b81203410420b0701c2d001c0b10386089078820744806005500c0c0c0fa00b041121070000e00c4481d00700c2d803580f0740c0007202d55491060152904840d00c407488840d0000a0003400c40f401d540040380103554510040c1c010641015400f94150044880484c89180110016003880b240c24400050030002001d00d290a0140c0003011b130594040700343c55140c0307035180d43d02201a21500c406c1903416030810404540541031603000004441d41c3c7c50203c0303d107445960b00022540d84924403d50030303980103d070280094a000e030b01c16801400c0860f15a9282091000114143c910600c140b1440940c00240c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 156764676 1250 156763426 156763429
    0x4020111010b2e111009050114131103011a040207050a05070303090602060601020303060604060302030a0618090c080d02031210050904111002010c0207151103030403020c1804021e 79
    0x4102d41450010b080d031003462040c51014150f610040e010111200d405a4030036100314811440050032000d00f4001308120b03400ca548031001003842d03060644055403256400b0303076410316030a1081c0c041d0032508a004099003481c2040030180743c3c04010745100382d04180382c000c83e0091000b0246144582101c00503510300f000d01c1c1c140d1428800410044c03080c09400400410705070410148001c456054007558002d42d2101d004a0701d0344000c84116500030010300041c01080e100e035001d15400a003112000800d280c42c0c08052100f840314000c082c42013600d0301244001c0003d4440f4200050610400400c04c3c3c11100f8000b0f502d0340594060342c0c20340a95500000c045648021401005040241901007542000c1c14074101c0080040c40041c0190001801120300c0d51051144003003000041e030180c4181030912404071f00c2903c10511200420030380440960080409000450056210703400070000b100d1a60180400c0c234a13040340407480701ca04002003102580b10640380401e42c0000071950809056a0030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 156765926 1250 156764676 156764681
    0xe010224220c06020102090a0e010f06031d0106090b0109061403040b04150e030d0c021911130609020a0e011d01080a090b150f0303180405130209090615060703080402011101 76
    0x980503000161865002a843e60198001c10542070b00b40e864030720301c40d1250f0408202c0c1c2428424103c00501111040085900ca5130200b615082d800c0d00d00d001041c5002c3d0340509444c915040f42d10b01590340c2c40d04990568000c00144010000f904100070f0b4128001302c01002404002d10160001d4180c42c00241001440c4880a1503510490b000f0800301c0000074007039940e40c200051001040e8503000c0390301074141c000242c070301425408040280785024295075802029011070071440e0028441203600d116860b40380903c5c8054200e08400580f254000040206088031154410b8140100c038074143e0b440c24061301102c0c1420300e0a003441840d54a98042c80c4005040c00708000c0c1c80a5480750502481840505009000860032680d40844030180e03c2056100c0c868940001c1071035802c50001704480c1885d402480d030240460a84501c10a02174011481890044460340f055403c00c40800003d040845002c04001d030003511641c0c02c00545903009000b52102920180c1070050101114180711003d4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 156767176 1250 156765926 156765991
    0x71107120204020f030103031701050f0906040f11070609150213090209130218030601090c0c02010c02060408060106020607020d090b04210c08031b0d0806060318030a0e010224 77
    0x120304180e980d83d503400d000300788c0c96652710042c43c1351186400000329494004061001040020105542502c0300d0003080001c20480d6442881c05403a0703070a01500f0901100170740171060003840046240300c0c0e140f90805204100d12000d507191032050007543c165844520410054030300400c4010303a9144a94005030080c1c440940c81c201040c00000e121800016450006220700c100350100d6030280d0302c0c0d09d6094141c0311903440c805c0000741641d0551025603c100300c040c60903400a802c582c5441d44800784541059002d81080307003d13074400d4080c010244c2e0b04210741440303100300d86440003c00d4180070b440700075840380e403040301071005891009103140c0305542c500300100d41e8050300036641690788074010b82d240e404c00790b005503a0507454030344080391043c04245258800403e0b0b49a0300c2603910f401c100160794002400081c100300792592a0050703200c00f00000c02103090b1a4485004040b40e4400091501401c0782402007020080c03207055a01300160100e55030818004511a0b5800011044640c54071801 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 156768426 1250 156767176 156767197
    0x209071106130308060409030806101e020604120504080319020321191a0913060e0109020a0603200922200c0c040f020403051e0607110712020402 64
    0x1d180c107011800150320031210900e0700c6a240c841d0b5580c1c6010420045a07803040d40500419000400151107140c18089541c1c80c211604000701034034009081c0707411401070022200003603401142400240450070311200501d04440c900f040c5400d05103400680c807805684407400c2400202030703555a026001f8003d40d0034006001d41c11314070300113070340e8201484a4010746400c1130a1442590000901105014401e06d03884941001008001c2c46400c0c000181c1d401040c030141030803488031140006489009039003205100c00000b1641c4c0002d401004004071441d4050014540382440c2d01082c0900200405214110303a440301c0d40340d10b44071001c999901d001201d80a00840c407801450a204903071f40c0602d0180c01003448048a01c40ca03005074080603c18081510791507844014140710514241d0040303040d0255a440244c203040e41c079981c0358a04144410b20003649501211081380c2680308020382c5a102c0c42c903190002c0b140700524100f9171510024088d00c0184a810002042951101e404817041c80c000c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 156769676 1250 156768426 156768433
    0x3200109170d0f020a1e03090b120906010603050402100e06090d061d0a02061c0f110307030e010c170a060b04150e030102072a05060c0312090f030702090711 69
    0x81c00709912000300c2c100b14000700700c001c0030081c8114070010b01803000c5541b001c0700c1203600701a050b0f8440c02d50001c110031000c0141d40e50000c209141d07900d0241245020b0311503850501d00b048440303641000b005030440c504061605c0c00708000b42c1c0c0c50512502c40041da40c200a10503000306008251a0312035140c1e1309030009a40207802080060990180c8814201075000c20341090a0002454541c00541c501a43c40f40c001e0020440f501c44602c00540d04100b81d040c0011414110bd1410054800d4021190150700000c01007129440d0140240400020030300000c1109510400b0041c00d9004202440c1142618402c000780704801140d0000d00030f000004103140e103407a920b2203000da0100030f2402d0007002414020900c0a541814025513101540c401075402c06090f000101d001a070140f1040400c0c40071503c0c0d0001039588540005241d0f040700c0c0d0014550750440007041090550015020f283e00d548010481c8031000000f005881c0c0e4994103d4040b442511414411503030482c04502c070540781e00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 156770926 1250 156769676 156769709
    0x3030c04090b060a17070918022110060507020d051605181e0403020c040f020405010311040305060a0203060a0801060e04140d0207090e0a06020d0e011503200109 71
    0x21000984101d0704808000e01c0502c20801c00e010480c0a0348114030045000411500030001890540c15400b01d014640800c000d5660000300083c03444107a042d4240d55070002e07034007034047d11004500030310465081500c0301e282443c10f0303074010202052084d402003000c082754010441d5100d0401407002c54000f821600c0100b03a55a41100381c004500c81c40d0300ca6580e04003803503120ba00201d07000d03104051a4051a505480f00308a03042c014000500c120118018840c0c6050740b55941d1107012482a4080c10058440c5c0c04d0400140c121441c0e800040c8460106100c2040003a800286c00c0d41e000c2c02843c005616030710b540c03011400c43d42c076a80060780f00394204103001c02c000e10b078240498400c80c0110100380700c91400b088000c0d11031003161100c0005806c803071b00a112074102600039900b03003034041c4102c1e420400350f91954012608841a45c5803080d0300c0741640f0305c08602c24003c15070601d90010500c0d0302d541c60340d40c1c0e4200d00124a0004800501d541040030707401e85c007400c0c0700d000030a8065408000312 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 156772176 1250 156770926 156770941
    0x203071b05010807110a06090326150102011107150921030c0f0c1202070801380607150209120a0b150d030507050c0d030903031103090906090402010207080303 70
    0x148150055038002038080d400a8480d5218040000710350017044060701415040d80c42d250090040b000301601400805030106517000f0142500152000780c0032070040301c2d401e021070024403c803c02a5154110382c1000302c290140c52a210032944415440301d22096910412400c40c0d0241880c841c0243c00040c1c0c40d40034240e180c160281100211425982c20009001208000d40303201d6084440c0380c4c00600f2991100d00020742d00d80700a070403500039004a460b425500c10b07445082d200d5800d050280745104100c420641600440102182210398982c0c450300503c002c0030514030300501d00046c000c0c40d840160760500098030303030440b1504240540500044d08414003000e030358100051003124005007860001d49541d000004030301000034001c090326625460b68070100c03a03a03000003806540c24000c011941c0c1c070503903c0071000c1c42c078980b00f6100c18a140c2d240d030502401103001554440b406801c200000c2c0d001b40d943c560203540c428001c84a8902e40d0305c0c0c03800106c0c9048415003081945108c00801d11a10 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 156773426 1250 156772176 156772223
    0x316050f221203080f07050712050d090503031003051c0206070c08070c06030203041a040201140913090302060f01090204050105040320030a140115050d1e051207060b01230a020307 79
    0x2d00105840103000d4070360b242e048815103c0c25401422784c14200041c0002e0758414001008650290f480c0425250426183c450444e80b06403481d000c000303a40c240400400105002901002150588010101c00500400307516480001c00350810060109034280410004a09403144181c001c080d0340c26164440c0c5e4060000e5000340c0e0309450b44060502400c032211400d208040c0b1484d4182e45030040c0280714012481180c20113140d441d80000d190320030a4010205214003004140079038014141ea040124140140c0304041c1c000d500c0180c0108000e00140e608081282c0403207901071498040f52078001c00e0b2510b18070190303410f182d0600900000d503043c06500d552821009000000030012561009144003007840607110703031074004a80d00c0e804c0c0c0c082001016088083c50120300340c642c1e145900d6960a042c40344a84002b002c144001caa5076041c002e042c07140642850081c24100304580e0014007041650007100401480d8440008000701d840e071091058551080d44803c2c007800006101141030079 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 156774676 1250 156773426 156773431
    0xb09060a03230f1b090114030705211602190209040c15080a0605010f020618010207050307060f050a09020105070f1502040602010e0c04090b0123150316050f22120308 73
    0x4119050700103404120384c008200e40c2007402c141c503890880311b200540f0301c80c1038000400f41c0003448001d1084485010810840d01d5066031040342181c13036072030700103041a5154441000081107500003680d18000c030400852038140f15404881e030070300b2569035140c03500c8100c0c42c039000004407203010036081030b406411446030750190395041b4080c4982c82c0c40e200111510003849080030016881400400d000200300714480710200061030000d841d184041d1942491071340060000c68107150b803600480c10b9010244581c0d9048a2015411f0154150700e03000207100d4052064050803155114121004105016990a0308495211b0056444540d2203101034001d161100700029103020b2145002ca0354601481075058050744181035039041e074284681488401c0c0301500f600d80108403140c851a40c0e9440c440040d050f0103010710995078030316000e5100081c15081c0c088200920100b804480c0b6492045415141c8a00022201d000c2c2e00000100c0c0d6810018180d004024401003004480c080c540c2c080400e51 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 156775926 1250 156774676 156774691
    0x905010b07062c06090d0809030a08040c05040207030503070e100e13061e030b0108010203010f18060e180c041e18020d060509060708042004090b010801020904060b09060a03230f 78
    0x261b141250802c01d80383c0346011103e0058a400800c08240310a0140702210382083c0981e0200e0380164440c000309049910007101500482c40102c00c000410b9803010351200b407410103031942c88020140000280610101e913015610506403a410b0131075612a0b0b5000741d000303000ca0800300c0311050740152600e42c014000d01040d200201813400215020b8014001c4170304880f0b8461200b00720519103191000d441e5080220a86215200d660000b00ca410f5544964011403c3e507460301c5507088190790981c5081150141c03d400380c1d060146a2021881000800012404403840030841402d007001c004030001106200943c4903c4504030030040c00503a40c003040c8105a0f050482e00281c68039039050701d203080e044074010580c10703d112008199010550b001c16820710b010f000417a240340d00e9552204440000d800641d50b503940410300e02c1e00d500d09405600001e02100111a24203080c94000c11500d12840590b40b00749502d549410280c02e601d80f44043d0403051800b22070a1a0620000b0f9800c07400c01522600b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 156777176 1250 156775926 156775933
    0x1a0a180905070e01020a05060f0408040306051906050d03080601050c01020c0f0c0316080303070c06020d02070f0501051003020a030b040311060702010f11030105090403120b1e0a0905010b07062c0609 87
    0xf040d400068541030b6181c10400a00103076541042042202c040140300f1101600140b0000000130801d010302800794070044da00501d0705020588810488040354866442501d20602e000c2c007180d0880141c503003001c0c00b072915941d640710031000640a4403600c000e2192502c259120aa03d0310001b0a580c0d0040804a00392000c0188200d081055050140070300102c5400c1040440c8078103001c0c05407690690b114072000b605003c100e9040030201d0700075940556040c40b03c1d40c010010082c0a103d1a5030041c80110f00080e000d00716000b050410030940070023045050500040783c20b00d0300400c00c40000c01c25103400c4032903034501aa0b0090292440314182c800e0142000552903003034684a003564142c4401800048282ea99038808842000685000c0052955590510681c07520f46c28105000155103540c143c0c2089206030034003c03120b4480d4410700c03400d494440140f04120404c0115695140c00c14030125a0b42054a600c101641c10b40c15000c403824204a8441a940d00c0410b400e4440c04081058 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 156778426 1250 156777176 156777197
    0xc15060405010602150405013c020c10090f0206071407060201020702012c03030d0207050622030f0e0d060b0f03010b01090519080706080603060108071a0a18090507 72
    0x500094074001c1c01444056001072102450362a5a4216554068002c50000c80d51642d038600d4400c403810010f1a024148541c00c0402198800c0810130749401140604114541098015416220050b030008804070300d071980041014005001e90f0a4000d40c0c00402032691342e50285410203904040c02130035040c600540000240303690042c4241e95205406840300d60f000c8800009800b41c00c200552240c240107001000103803243c4041004e00055000c25900591316140c9040c0301e481d040008080c0038203a025801c20194184580c20700202140d40360400501988807500182c1714605c1d81c9000355002030603035100c881805020b8000b0320030b8000a40d000594080008181403da0703854150460206102c1203042085041c400344801944020a829100340c58885410601f031070300550040d40002c034050107002c52840c0a0060030b0040078040c005000052402100c130181c4120f0810703d40e44002c02045c0e6a440c01e0140c000c80c40340b00c128540007124182c4401d107540c0105415641040001c5101c140c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 156779676 1250 156778426 156778429
    0x20913020d120c021c030c0b060612070210060503120d02030903190903060b040902010806060901050702090915090307050703061a03030a090f0605040803090409020f0d050a0b06010512070e030f030c1506 89
    0x45c0304c00c0c2640696800008031300c80e44030080c5449010342040d80040040040180c89240d100410303005994030f60140600b100e100000f4400c0d0784013600214400d411281d01560302000000846588018512026849030341e00d225540c110b001740b190800d00201c580b5a001181a030018030801940d21400c0100411080b42041c80304a506048009002c03803000340104505250200c041d000802052500910307040c07299001c80c1840505948450742903011003c02c81845a443c001d2a62103825803008509268058490380c0c0c0d03039074640c4001740c490740d40da5140c1001d120b402c040c40b1400030405000c40e0341d203402545000b083c0450a2007031721341e0b0307501d030010216041340b08404480495010000031400c00020b07000304002460840b10490340800e840c2850501519141140402540100301404480502d810007852a16000386114100700b01000000d101c0b0000411440c0c04c40c45914009030608406808280380030401da0310205117220205071091802d04c0010082c40080100c003861185494080 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 156780926 1250 156779676 156779719
    0x309031c080c0a231c06081c0206040b060f0a0b130504020a02031e13031b140904062f040503160f050603070302070b01090219020604020913020d120c02 67
    0x1407003840011841c2018011381200079022020300da504130006485d00c00001c59448008085420120741c09454030001c0180f50410300401902e07618401c5050201800904000c1d25043e0060000740303144040004943c1030384a08440b0810a900a004400380741d0700e0702c108040d6501700b0b610100002c20a04004203aa040c03600a990400280390019070807d01886403456442c43c414403115020311052200b144040c0203520710304021070007032290f01c5003640c240070034545000f05074100c80076886030302010944039241d5503000d035032154101b00002041034040003690141c1c154811000a1100a0500d954101c2c038180c3c010400c0ba5005c4084130540c05c8441c480d0802c0412500c181204510003800401c01401c00800955000f003003850f0061404001d6a11004040b00a82107080340903070208000a00544a40d10a0018011400103201d18a0664009400394000a1103206a6031080910070110f480307480c07000e01d1403a400614560048500d100c0209400400c0d40c0a0f44100c035051444850010240d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 156782176 1250 156780926 156780937
    0x120603010f090b070309030302090d06151e0e07170906060109050d12030e1c08060907031b0509010e090f06090c03160309110d050105070e0303120f090309031c080c 72
    0x1016004140e132030032001e070018040c03004150f081c56020420520b03181d0700c2d81036040076241b00c0e200c00140c56051702c0030000282001d4100d648895804088034591204542d44070044481e195059440c540d20000c0031901c9003184018481e030414560b090094035100840c1c2c11340725034402c1c2d0382c1e000001d81c0c1c0e000b0455401d92081000d0480e8400303013a81f0050503c6600210808100b05084460311103c16207d8100751100000342c6002400c09003d021131440d09821203a045062482c09001c0c204400c02003514143e06400403a0030700c038001074212010703402004500c00a4400410103101850951528840d1220407140184115281030002d1005002d42050703e00440e6806144941c502c040c4600364000c15641c2d20650380b01d4811041801c017607480072140842c2502c50070000c0307081e0910300c1c00540036210010b5110300c03d070030912180600c000c9548500354400d503000e41c41c00b0940c450a21003401c6101d00c0d40b8440c0c240c05000801080707001c007040c0b150315040c0c0303542d14016641d5400040c84224001d5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 156783426 1250 156782176 156782183
    0x2030a0c091b0c080a020a0c0e040b06010801030201051204060f021c0c020f07120503040e0c0c01110405030312130803042f1507020109090c1215030308040f0f020402120603010f09 79
    0x303d050140114215101a00c2c40d864580111454501c1c41d8407408608401c0c0c0c1e00030074084109408000400407001c034400e070001c40a08000446504543c00603000d4021300c0c0c003182c5444019800207003440015002000d051820f858215070707860007103402d004282e4148100464880c241020010a2480040c0e001c4045100c41d028081407820106280c21000c0a082c05407503d11041c003010036942e80104025010381c50094440b0b07a1040d0b001015800d40301100d0190000b003a050004000c81c4c2c80200071500c0e0f00003090351030603255032400240244a40c4145d4040c083c10340110070801085907205100c00014141c4050803844243d10f40030f04c05801c1081001e0f034102c4002c0035608107100189020304482da1050414150031501e0b5040442100e100c000e01c940082c1c0103803060a50070070303144030300f64450764242c503c03411107070454a014240c3c0c88081c200400b00d000060070241480780c100c012000640c0c0c02007095549103885c032a9600b220b03000f503070f03030a1295203003070f0143c5204042482100d125a50 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 156784676 1250 156783426 156783437
    0x21b0306010308030105060d09051002040512060106020303180f070608011a0301050f0103181406070f170601051308010513020108010905250e090108060a1d0a02060d0902030a0c091b 80
    0x90000748805178004601c001c14075a211495140010022f12440840681300c05005031118948002c20078000d80032005600e094111000600000c0d40c04070440b9030010000300242210544946804c0c41c0c15107000500906010b600804500d0b603a00820700c1e412107056889200d1018051841486188800e2281e143d0000c10824100d5495000782c0059441000d8800400300c9000541c0700c00e841c11021000308001d54000c01c040008042e000140c0c0e040205c0c41c1c3c54810724010b48a02d5182030308901070b080f1810722201185903440419641e240c0c9028146800003886641490711b4091a400c01d034203012404a000100045000d050350300c10350b841031058246044130510312012448003042043c0b40b01d001c200c083d4508403900c0c0c85000516008280d038600401861400e40c0f0b50804441401c0c400e03400b05580300d10300f1180180002140c0d0f41150b0115280c1e55170b004440b0052001f0115940029014044c10316210b00340f0440345444411500b481100740b0049643c00070b100d40008d400c0420314007044 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 156785926 1250 156784676 156784679
    0x302061b010605010807170601051c090b0a11040519080d0201020d0534090f080606090a0b0307060e0a0e2406190305040c080a120e09060f01032a021b03060103080301 73
    0x641f444406d580058042c14040d1034088090541d8030094154001030684d142c603441424200030590103403e50001c03440500300400e170804544a242c612452040c01d100e20084015400b031180301706000d1006240d10400c5803d0303046040400b034040e4200c1303c1e140d04024501000916a44031074641d401081004030710101c50410071701060091030040c82403250804c07040d002e01192480c0301da1103040103800403d00420843c64004104000010020305900c152810900d040d011030302c1c000740756802e55500303050035000100d15101003081c02e031207a40107002c44145003040c071490b064228000e00e00e20b45242d030030740502100c0f5420320486125035100c1c148001c1c41c0b49010301e4111b221ba401a600181b251600b0b1603116900c0c0303222071812030303804001d4130071800041c001e03003d90360171180702d00c48200181c54130b1005190107070000d54040464500b150600d40c0b211b40fa000403980d81c00c40000d912081c0503400640c000c0303805000390341d1300c2d40003644c074403141400308803042c64a000603031541260f80c0400018a140e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 156787176 1250 156785926 156785957
    0xa0b1605130b0d060305010606121109100c06110d0b030d11030f09011202070624030803010504090305070501110306041406060d0b011b291312090302061b010605010807 74
    0x76484403103203c40b4a9518180030000482c01c0c045c2c1c0f0300a11031a1b80d5201c10100c010280f0b401c03201e140084500e40c000400119221351207400050300c80d50403c1c24980351062540c20240044d15000d02d20100584000814000012407540001c03001c140c00d400310754013000c00c1c010a90f80705000c00da5070302180e40b0510500303400003051001400c0f000c1040c035041c2c02d8074000c440300100341d8100d0754045800315203d000390104040d640f0030910445d081500d000c807500d0300d1602c4402a034031040c01858004d42e15001054189809601241c9885a00400801c0b0305582c1c00c8800e06540c00c00d0722420701c201d062844110310801c0582c0704030301610004000380d24208400000000a02c507082089062040c1c10081c240180d00c1444115900750003200d0749019480c2c07a0154003290014600340c0c1004490060a0001c1e005145e1440c2e060144c0c0204854080b0944000c156403c0c845580000e43c840c0380003403501c80c0780c080c0008003400242c10500a101c81a200c07030040d0f41044044948400040880f140c44256 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 156788426 1250 156787176 156787199
    0x715021603061109030f0304050424030305030a090f030e030c011107050904020307150323010305031e2502030c04090305120720010b09061e120106080a0b160513 71
    0x45001000620b844e1403507203000b290605d0b8107110445200e800c0460100990304280c00354000d00c01203010068185001c25000e030b01414090700000d4100700000c400120301150035031085031801d400c43d040c106a42071f10724004100840150007e4000d01074800892141d500a0001c441b4842c1d4450142442034142004c1c480d00810007401668180f042c4000007035200f5a501c0e81002e02e603101d0787c001c200c81d09441c100ea100c40040140549000c60150010000300c1c4011058503034141075004450990402005100064020300d0081c00032040041031002d0281030071415000001d2003070341594003062103901048110703091181c002d004907908021500c41000b20b4961140d0102d2079042080c03c050417018042c0584c2c09082340e80e0b40c5a9521540d1035410b142c1008025800501100c080070350951500003414601c1041d00344c107000d1a00700c0721006512800b9007100c0044d00f00742c1d08031401e49000c0d04001d2080781c0240d94241c0359507030840340c04006602c00c00031074840c10801c407000c0ea0b04da4603100f0000d51 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 156789676 1250 156788426 156788441
    0x100519060324082103070503060f0a03021201060303080906010312050703180308091f0914010504030b130209010914041e020a0b0406110106080c0103050603070f08071502160306 78
    0x1c80076500b14000d02a4042c9000070005809000002d00d062896130031031199010014003400f800d20024804c01c01802c0d40041201e610038400d450348440c80b204040071807550980364000a612141d8604174100f030720415072080048030b0103540c1321a10782c0c031074000d000d0301c403079003070001500c90b070074101c800c4111500601c02881424400d01e068010368012101410300c51240d074004513a10380c40090740c0540c526140c2a004082c416100011602001c5494041c2c02c40c0124841c002a02005111214079a070203102174038015504084040c02c1440c101202e0b0340c5030090200101d1007100f00320000b103288a07a40c46094000300440321520321548441e00ea20f8a0144d80c4c480f02440303881080002e000503207903c02020018010b040c50591035034101742c406480c00f0001c10140c401da80c5032080804c080440000d01300b039007103403e0a001a17242c5824022a00f0144c154000702d070340301920440007449480029044080710200c08247e1054016004200c2e00c80c2100c0400940354100300d0018004140181c2c04003c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 156790926 1250 156789676 156789701
    0x60402012609011a061306230c01020310060c0b0606030a090f030806040b03010903051903060b04030302071d1e07052505060709050306040308060102031c051005190603 74
    0x310003141c0d080903103100315046400c0c035450f035180d81d0404281140c030020900000c6084511600f0b01c11680c1d10141c0d000300a214080810840c546403c182036041001d83c0c11403441081919607035914811054081e42c020b9450010600641d4400038070b86114420741211030768040b11119003521200100103a1b5000a400e204d421b60f525601040003e52100d000003803184692030b4207141e8500f2504100460b460000900c2c000d0f41490a1580000c3d0700104540038442e68007110000c01c0c1e040d1400301c005042c0f030f810038108004002000300c00c2c150009010002c94442d0f10411340034528011401d542008280d400201c5402d4a101c03001c500701050084562240035407070a1030624018100d03a1164003c0d0040483c0e251041c511900284241444800c0d40720780b640c14007070350051505010907a501c81c0180041c04122030304003c82c50a80c0b003401103849a010403101144036846240103500103142c155940300307a40001a03000100790500c0408015802045502c0c042400c0c80c0c9402903014040142400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 156792176 1250 156790926 156790967
    0x403090b0f120f0601200c1c02090f010e011a0307030207060f0204090605030c03010c0509060c16030c08010c2f010f021206010212070209061020061f050306040201 72
    0x260140c016519000e02c14003c14680a0903800c100c070000d072400700c00316448005541080d4a03403410301c0001983c0b0070a00001d40d010300c01c41c401c0e0340701548500f9518000940c020a45820f00810103400c040560594002c044e4000d0341ea42eaa840c14040400720f2030b100d42440c0350a00c000303030165000e640038080b8117000740000304890710080344080403a4056045415182d54a4100348078030f0500b086480c0300a44250000c004000324004080e05034021852628442c0d040000e1104019500340054209100c4404c84580b030280c481c039001542404600810141c0c0d8640320108101500c42c400c0308400304198222007034030410320354040c4d40c0d05541001050352036490b12601c0411504603c010300010144020380800707414240300082c1000e603010000e0740266028042c0c2d002581e07501200542000080307986c01d031804400d03803040d281101c8883c280d003881000710418801c0482c011580501c502e002a080d0808031a001d400940001802e0140740e40503840100005d00550103180c00124040d8681d805 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 156793426 1250 156792176 156792187
    0x12020c12071515150309051b03100f020304061b09060818100207020301060b040b0306040207020a0e070c0210090f03061104030519110f030c010c06020906210f0403090b0f 75
    0x41420380d030342a50100f81104030300700208402c205192050801104510b028841501c03151170305561954880540600783c8140350b401d803081c0d80e04000e204070004804009010302954842800c00940003101c0c280c84060078031500060880c0d03000802d02e402c220346e48418408a00b000c0b0116000c84004000c00b20000c2c0d000701e140300c0200c0030030225600c1d289c000405a03640140384141401c0d00c80582c01402d031902c080c4003d2191040d5042501d41c02901914016140d0160b400007074003041140d40441079690030360b010712051030740c40390a00c51740c030303000750384841600c000c1c2e01c1c04540f18440b0b40304401090b1801e14061000a50b56007001c0b80006d81c0502c400d0605480c0c1c0c0310305007405407100c0d40318000301e4904036240402108440c400308600040b00c01032601400e02010a40300c110150b4200d04020313040740c1e0901000115815500c0307011010304869103942940d05195800d41800c1101407005800400040b40307079007925605407140f64580d4448d0281407908490070115080031203480003a120500c40c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 156794676 1250 156793426 156793463
    0x3051009090c032d1101030f06030b09060c03070c081605120406020d08011a0c01060b0f0d0609020310121707030f1b0308010501050706020405150a12020c1207 70
    0x10301d1403550091020502603495807900b6025070b890380c40c0d4128215000074420040b00d034511452140c0907080038010444400607001240181981c0030030070b02d03642c0f40c40c1000c0300340000084958881c0b000c2e6422030760f0b1b07919004d40c122807d000031540500080c4001112400003100580a008c02c6c40250003c80c0c00c1011942c0c2c0c5c6c6003026003031280758001100104007001a00d604120f44038000301181070441143d4100008a480e07190707c0d1107008086200042d1980702800700b58000c1d0700810366507080e01d80351101010444a298019481005003a00784040410f914819108484c011109542580381992400c0d102c10603985201100782c13442c800d030707001d204406104d00009000340b501c00c1d07841d140788085010002d04001d40d41d5030007100b40d240035a0983c001941002c121415101c0908180341c441c000351400c440648a00c0d00301940141d1410003855014080c4009000c0c500b1041c3c565900b4400001c900608034001d42281c1c002d284c1c02034000403e5008180b008140d150b008644d40200b5841d49070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 156795926 1250 156794676 156794681
    0x5030706050a0206010e07050d022a01020d11040e04121b03020c1807090902090f120c04180b04020d030c05150403021606021e190c030606050f1003051009 68
    0xd1142011030000201880d2a41d0f05011244c00341210403e001c0d0103007020030703008001d40528400c1015080d400514000c0030380b80c81283c0c4510441c0c00e510b2000c00c3c40e0b0070480d107010f500048212214607040124600e00e2a03407040641e0251000380307410031400d980702c0e260f0001c03104400c100b55043c049200c400c00c40c07081d820301006074524000d40003481c1d01c000c0038041c400c0703004250261004c0d40d8040c0b030902140760b6000a00c00201c1e41058405a115903504000454464400030550b03402242815074860704500030414030711000d800c6038100505142e5802c0482c806c06141340c010000e100e030b070000500520b0a4070256502a00a281810b100000e540c1d4441c6000b40766854081180c1581c0d003000201a0304004005940c400341805403000791414201079551301c944012001d42c51510701c1450546002008030380c62411400107514207003d03141c1800c80003002d8501007610210b01307001020640e42001e145030702c0c030b41c07034080d2135400c2c6500901d41c200d00420003d003080500f9440703164005000411030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 156797176 1250 156795926 156795929
    0x5040e06061e0f040e01140906101b06090605100f0611010b04021615020c151302060304030f0f02161202010e090108010617010b0109180e06010e07030f11030604020f04050307 77
    0x109115621410201c2c94202104168050142034803100c041c184035407110234810380c025905850400c0301c0e4010050586840d010346880c0181c00c00b80c1c00140341032016942148003281d0040504100700d45403c0c05405200809025031400700041e540300308001480b80f6102c181c1c5810503000000c108440d00300140c240c0c1d1150043c0440442d058100c1014460074260f1000e01e410302e000d00310714124644454036110342a001000c01e51036100c90002d000c01444140d90f80c503a80d40148005c0c0c0c0d0749040e00d0302600c1c0402c826078000000b03100940c0ca04e03440740005406504c842c0819003078040c40c0e10b00000710701208a2148202d04021401001c000c6e10381f5092156400380840c1400800c17a01d041c041e01458140030f00c5840a002d03030600120200c00c0c1d1700081010143c070000d401c04280c41031f2148521000e401c03c1181190144a15800018401c9110305500d005800702d6606004d4000a0091503003910070348010344800c2c42080002ca005441e00d58001c190f9604000b02860078240e40c0c0e40040d051865a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 156798426 1250 156797176 156797197
    0x612070b0a0507211e02030708130611060402030a0b06010513060806100314180a05070303030506010908010903080c0a1701030809010e0306040305070602090d0b071e05040e06061e 79
    0x208611040003006000e00e0204076200d0380341040c0844d200e400030403101581400040c1404e100c1c40001400e0310a00840304805d070803c002541e01d40914841c1e0300d02c018030f4420782001811000c2540c00c0c1240101d141809180c005009044070405900c60001100c005040706040c400d04001503040e41040340241c04c010300c069140c82147d49080e03000e02192000c4150070710300705450410201105030100ba103030b5070002c10f12000d401ca030390350034403800c0d281c008c5228002d8860b11941c4000800c0543c9500080d106a10a0340e840d03003000e9075040c016013681c000610050106020b40d00240c0f09800950103407540108928040c4c501c3d40c001c0924541603403007a0025554034000148401141d60015003203031000400341d005000520702510010311174003031030b180107101580000d170402c855601c2e640c1103a8030a41103505803041307017000a0003030f00c0c01c104990540307c01303240d1540524140e80100184c07400c4818240045c0d1031030341d600741082240c0d400b03221310700840004e2800b5448100281000361410910 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 156799676 1250 156798426 156798437
    0xf0a080d0902090a060602190503070f08041a03060f010503071205070509040204180c05070210031a060a12150f0b070f06110705010e01050c040b13080f0109060f0c02060612070b0a 79
    0x912200070308000e2002108c0880c681c412000e0780008100108940e81c541d0404060f4200400030b15100c803951285610085050988035980071001010400442c00b50740c08540b002c00040c5420015201030200303ca058002c1191640044000c85541d04070944c4a01c46284c840c1c80d003400000001d0481c1c0242c2c20410a042480100c08086540c0c0d10819505101c2420558281a0694002504e0b002450240010951240ba5441c41101104c1d05806004070003015686c45421000c0020211036040200400c100d00745a602801d42c074447c80204144c1b440d8442054000b800d140f00720304641d10004049660b00407000e0b028000c98041d1155043c401c82e400e680580e2000c446c1044d0303095401d12811100e0503403500341801044034108044404888107008040c1d21100240d540106000290380a19400d0140e9091081966030641c0124002d511a00301002031180740c091241c1268a8017000b40c001d07a100c400400e00c50f20f0700030780b200706a241010444180d69111488041c0300e400001d1403002140 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 156800926 1250 156799676 156799679
    0x60e0c04060803041a0a020328021e0d05071a0a060513050f1302130e010c1b0f14240109140f0103060f020f1315020f0a080d0902090a06 60
    0x24040c001c60380101080001542842e08286641d926540040c01c8010603c10002d25103903a24003d0041d1640c0941581c800130307482121f460081402c40704484201e00601402e166192b803860b00201800c85e9825000090031280d2809006032455406142c09550042c5504c0101e885d00b01c9900300541305080c0040040380700c614000c1441409802042c6540840f0304007400c210008812106c00c1d903004559645100d544000f900120f40c44204c040301d0118803d040048210fa81d11054001c0d8416580503030b1120080d107403000305200800724052000f4900003c100c0040d0110b446c40200d40c1c8204848001c0e10350340c02c000031020701513410400c1070006140b000070041180710f020b807281c540042d400302181c607954a400301d0501050344050200030500ca0b5a441c290310034240da03034182c83c0c841400704016541c4040d8502c58100b101c1180c8240804005211501d41f01c10b440460000b00a07120000102500240fa0b625018942c00150b081418180d070b51003504050303aa616200d50044070b50030000030302c25 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 156802176 1250 156800926 156800929
    0x501020d1407080402190e150906030a0203061b130306091a090a12231e0a0f0c0614040605250215040606091b0207090c05030a050a09060e0c 62
    0x503501c41000c02440c2025038200308505411000495000358122140c0ca4000700b4501d0414100142e87c00c1034601032112010003040c044d0704802500d4242044030204d006544000406076202200d50300250140c002d4008981c1c4208038100c0c80b01401ca403d10228104400503c84e9800c45900794000e0f075940c1c0e01e851140003030005c0080c82e840d1500c8414404a0703189000c1c45a00e640d80c1c0b20100c01443d6001e182c6035048018400e501408148030003140c01e41c0c0b05c0c245800fa1144a422241a582500242010f82030300b44682000b107400900715920b0308102c104a003082501e512514039030685001e83c4408071081c8090101080500c100d105060004150514000081c41d001c1c3d110001621082071449030000b40390006030318030302290034842a40040e40c1d140740c440d01502e026400f0801203401d01c0321090f1200440c2d80c108000344016401c45491590b6803c01005403840148128045101000490101540c91f040036a200f000790320701281d884060782d240012183c07180320842e4103410100420b0300c02e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 156803426 1250 156802176 156802181
    0x20307110103150e09010e0d0c11180f07020109020d03051824090a1a03040318120204020a1b03030b2706040506010c05030a02031306020303100b0903070306090501020d 74
    0x400280b0b0100000700030f0401d0b500e00041c803401805038140d10f15001540b494425080711810b005401c0c248d40702091501d07006007840d0b100d030004550b11009001c0d1900141004208070701075042c02c81c03034445030741c0300d510442da40c0c9100034100304115503d8403448405611420441030184b4400e60303800c2d030365009601802a000e00610040d03849090202003c0750310160100707841d104c0e00304106099540d0080720000854100c4960b000048517100351035003004c0c60b0701007030245100b14083e40f0f40064003070000f1a005801c0f405800303034429541c8c02100100142c149a405001101558140383e502034200440c100300b100c0d01080d044000036168000844281002d070b8a0910041705000341c080c0d80d0500c03220382c0c42c4048008044070f0185540d140095003a0703214001e0382644540080a5a603101180c0800030740b44d60061031901d0f44251102400102d0901c004200d0303100d43c072682215000c01e030170030080300c80690001030307076503850b101341070021000c00c01c144202a5014898800180e80301c80d1100790105 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 156804676 1250 156803426 156803453
    0xb0f070513050402030c090406080709181a13140618010b01080402040e011d060a06060801080a021201020f0a020a0506090106180b06160303020c0c03161404020408030703020307 78
    0x200a0180040d400622109041d0000d4500480c2e0158a0b540d0720700e0560158019028400d40c000e05021002603401004203c03507042d0f8004c0b1100388500341c009060190343c01414540149445003040002d0420202da01c80140c2021528140c000044c00c1d645608410b080d4180c0b0320071480d0032034018004581302c445043c500404d1904000c1c8a04010702001030003894004002901903070b00d0300d55200070440c0a5010414039100d0f43c484640701c5441124003030391014104c6401600b60301c1e101000c00c0c0300d4010908203049602c94001411071211950070310081843c10b00900501c3e64091205006241d601070142890fa0b0156004100d000e00c0381c02c04c0703881d0a07800b9281301c0042c2d243c03180502c0f0606000c41140e11850890350045240c41d5108040b901902c1000c00203445840501c03036610070164190002c284410320403003140e4001850310205521104486058650014100010049c049d4440b94018045200500c014185560340c40d0941c215400181c0c1100141c1000907020200250b8904108 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 156805926 1250 156804676 156804691
    0x9190617010501081b090a030609030207090b060313021909050903070b010b1602010f0c0b0c09030d0f2007030b09030309070b07021305040f0c09020306040c020604080403021011010501030b0f 84
    0x7513071401c2a440b5120b281610080340405404001800841c50300e0b013420120086030b000404106090701810001e44441481c010302d05820706181e07400b8102d25026043da4040c11203107034001d1350041c070396082003010f8011400c144c054280c582000650511644101440b1700485405955981c813686040c81070584160414882c010301070061280c1030b0100d40d0191134031036081c200380705c140f078118034140c0d4415003514000b06044988010040c200aa40010b406019426421200d00c40003020040d40c18020507420080024400d40c402c0e9440d81d80c41e481d200d080e50090003980c2680e0b4803621410480e1b0b0b0200c1f400b01c80da900000910001603c01c0040400401e4a9110142080c98a500045a5801001300742d0262034980740071400344020402d50b005807542c000c2203061178650305d0b0017040194004407019172045280c40221071000740042441845035511000980ca400c1c2941d0802020700c0c80c40c600c00b801c000c45d070342c0c1105268400348030310b0303020307500481030f4145034a44150030482d0300748000c1c00d42 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 156807176 1250 156805926 156805937
    0x30b010c20030c1f1115010b040303030c020d23042102030c091605130504090c030c0909030c0b090106080610090605010509090412052110140d0809190617010501 71
    0x15401011080d90300a05801450021702c03d004418841d46000075a0b0325400740890754000001e006544000140212407098034184401c0032000c005a03243c0d5960287c030710114100c1036042d015000c0180702c40c1b4208100600c1c0605064850300002c10707094602e820705e03010502c0b1802e44000d501d000c100300102c243c403c551107029403411190410000c0c0365203400300300b4003002041c403010050886075840d000d84000307002042600201e08001c0c014205c540300c25215824201404186d40c5460b0046000c050740540320010174005030394922506c41c800825452584d540c031840070807100428401d140c0a01c03000c001c0f9a04090620814804549075581310606002d4200402211620f5500c10380d58059041284107200d134040000c10384181c0f01e001e240f64101802d000040f441106000241c500070018084450a0141c4031140301c6200c1c1c50b0540300703a9000b83c201d1080b000280d1548014000924007615026120384c1465814440000d2908000081080c800a141c03101d494001c00c240100401d2915 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 156808426 1250 156807176 156807199
    0x305011e090201051c0920130c020a02060d1407050c0d03050610050a0309080f12060a060c080705012405010e010206040b0112020d020604090e06070c1101030b010c20030c 75
    0x4e4068844c06400054100c001525102c0380069580052200d50304580881c04200608001c1c01e40034146440281c0f10302c2c91094020500b100d43c0c440c60006000e03e0f0010100790403190200000c50700212400800c044d2100420004800002005400f442c00d50b11120340314030186e0212130034046003070b2200081519050412041d07030394a00c600384003140c15080150351000d01080860280c4500ca901402c0c8038000155140344140f5a8000c00d14051492940200c5803075110805c040d50403a8801c61001410216605011985a60050010780c0c800d500004408402417074408a2407860364613402662240700e0200700035600a1a4141307818402d2015295914040e607a480240350b046c0a44101d070803030202c4500031500d43c501115076407a00204255199a501c200080241c500c040012446000740c1010076042d82c040c280c5225000e511401c0ca0a221030790398011801440445501030422980f41100d50104800701510024100861564909031000005051405458002060052100204 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 156809676 1250 156808426 156808429
    0x10e070e04120c020316230108090706180e01120b22060509101107060c05040e07032a08040309051c0b0603030708040e010e0105010f081314070305011e0902 69
    0x1402c030402c60709003820741d41c104003800402c1c0b50164149074414410045140460050b40035000d24841843e402c5c10380c8400020400116498141500d0306443ea611003c03050042c00d0107148028104102126951455580c0e06410410b0320401c0e40107510403c001d03a00c10342071041c0c042000d03071700488210084c980044103d400900100c0c140d100509180e54820114030359400074482e03130358921074440f002d01c294003604601014550000030115a2503181280e0524028010b0003078030100c803104101a1941e40e6801000da010b05039903038606081426494450118415186e040e4040c10a03d0b40c60801e13030b192030b1901074808d08103038000501c10450052403c01505140ca0000b070183c0c1e11044040750f5482e00d6010901c1c40c090010010050a804103012131341d8190207a456040340c1c16050600c0749640d80300e00644155a40401000c0001c0c0744600151400c200d40c1d02d0898441e100c0c243c0c00c02c100050400036403c1a040750012601651141100050150b2140c4251032034418030008110719607880d0f0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 156810926 1250 156809676 156809693
    0x16180c0905130f021e0c100501080613052b27031103070f1806150e09090a2001080105060405180a02040f0f0e13020114071401020c010e070e04 63
    0x141c8940c290f4a80700480c94500309a0142d0f41d0000100580c000ca2201c000031000254020904240440c030881034440181261802424100e81100000d00410f0310f5090351102001354003c1c0680d80391191103941050315242c03588401c56081d000703401c0c0a00c0480c1041c010800210004845d90089050707071a0851031001c5010002200c1e03000ba4030181a8841201003410144a60310240c5400d2011400240b9849003021401142c04404000c2145030748600242e9140d2220405040000340601c0c0311285600301188200c2c2c021101c441141c8580300240e0751250003010301d070102c84c4007401c0d0074205000da5810115581c0501801c60342c682c242402d04010440480d41e1160b020281034501d404100741e40410b504071805415005007804000c1c0e200c42c0400d00f40103444c402c0e00300d0b0000400004034952416405e041038158169220058812000c103014515080010306562010041d0b901546c0248240300415071189084004110f0b0106a203805007062116400300c43e0103041d01040200040501 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 156812176 1250 156810926 156810949
    0x40b01020601060c140f0c0117010f030f0f060e1b030f030304062004030c06090603050f1612020c06150111030a03020d0e01050901050604050604020a0909090516180c0905 75
    0x24a001c0724401d0f41d031709041010b80341d14200400680103030140c1c40ba14400101310f8414503002038940180c031444d421002d1030340d030409200701a03104801c03003000d000203552030030304a02481c054203206482c601d0320307140c04044a6580400c24100e90000d00c00921070480c41e114550f5a0a040340500241c92074591a103499200c0100300510032542c650055202516111800300e40400170107030181c450f5240c0c940340c001c000007806058041001e242d0009030042c03280c040c0d64414240003420f60f0460b01c03429104041901441c0c050412300c6030008103a1030b001035a2024200030741d21600103003402d0401d141c0503080c074000c243c0c2c40c5040000c012184c0c0c807590000402c49640341031034680180e403000d0082e181e03002400148428040c0c0c1d401d1a050080729641504280c0c007074803088808014507164941000102d01c41c0c0400c55000c600058400c06c01c0072466805000b58a000702d00365444468540c81e0010032070b2480e0031111400399444010000e2031168841c500d0100b1071400c003a40114244000283c015010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 156813426 1250 156812176 156812189
    0x50d0c1104050619060206010618210501020d1a0a080a0525090603060b0909031905090a0312200d0819150b180a2909090c090f040b01020601 62
    0xc03400443e0340c1d41c450400b400c80e85405140c440c040c0369182d0704000c0d00c1c3c1e502845000005014585040c0300e40784048091021210388210591004603528020651040c0003502a1140d55003440080046242c0b40150f682440001d09003400700ca0540080002c010100c1d046a482c0d40e100064074400036400284104038601526014090304d50380446800f00820545c00c0103104500300000042003000d15000304030031000031103e0702c0781951400f00f643c2d90307400364500080204d64002c230042a014001d20041ca0b0051014201c0b0700855180d49610700945001e0103508000f40b07004950007d4003442d5500c9140b50070f410805004103003101600100109005014140040e8014402d621428040d6001c480d4070b6040f103481041c041c0c4d5840740d0102d113800500360082040b0b1460f03030303080640c80c007492a00300756907072002400a00101042c1c0408000c0e0075800e804080482044683c0160750340041d6203101c0c044400c002613480c40c042052150b0069600031150040d802c203c0542d84030381e008184181516107 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 156814676 1250 156813426 156813431
    0x6090603060e0d2a150c0e0910090e01090503070807031205010803030f0a0f0608010c0e010504080607030b03070b130906090203070206010308210f0a0e0607140708090907030603050d0c1104 83
    0x281c01041995401382180103007840030507014100c01000c150007011422410352a81041031030001e0500410160031101850b520b03519a17014411749200307500c03e047d03c040440c000518220256a15891a801508103460060340400c480080581c046070001455164540c244100d5141c400032559030700000c4c190403481005500095501c201950103d4002030085509001290344c0c0c0056071300030f09102c1c0c14040001c400034120f0041f0f5000d1000c803011034802100a11487d5a2608110700070003a01030380540c5805420800074480440c24041e020b601054252007900c0e0b850006801c0807110750340d1088015600610410070110307000304d24141103e4004d20025a0703100c07424446c0d400f101405c507000d50101405428440c40700c680c2d03001507110b0040103200708242c420301d6031210395443c4101d40000c0020f80085480151244880107840461f00c03c259650402d489400012000042202d1240020b82d031042c082081c4035080024843e0580241416003642c41d0a842e08a0380ca81d490740c4040c0586d8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 156815926 1250 156814676 156814727
    0x3020306041e0501030c05011103030a0902061209030a0201060f030506070807030b0616050607080103170901090b03090d020c01090f06050309070504020714160506090d1506090603060e0d 82
    0x2212a081112001070740074402c2880306200051100405081c00161007021041301c01007903075402003030581c041c408110011800c55840e8984a40a03104241c0200d03003101e0240400c0b1801d4520008141c01820f403580515250a004e1038000c6c2141e00030341c00a00c00c035040c09001c0022035408649242c102c0e455143c90041c81d40d403000c056015142003441e440d0400f100080c0150302101da41000d4840c58400c0c0e00380c0300981c81e030201c125003940c003e0201500088040d1050030110b40c1f510010b0140300418104860419640c0c409100c032604201d41c03008454100c1c140030000c03117506010110a0310720034206000381314100340c00306503442d440d07000f500c060000010201e80007400c1084020001c0c40028425543d405144c41d03c101500403410312241180304080145030b401d102012114261030005e00382c0c504200c820810072440d0410001d054401a940c446200300004941c05188003501d010000030034918610b1030050210b1b502504078081c107410846040340225031100c08000160000e0400740e1114 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 156817176 1250 156815926 156815929
    0x30702150309120f040603110403020f10180e070809070e06040f020d020406020102070b0c07030525050a031e02070f0603091707062007050606191d0f060a140103020306 74
    0x301d003d07000000e01c0784000c1081d01c129040000140156480341d41c0a020240441148000a0040c2d02000358040c00c10341d000710413400c003003160001000380342c541601c0c003ca88032608a50108641c00001524803003032704202040d5007100030350360070015103001880300c5444c2a000d400341c3c040141a5511898403040740c40b21109031501a10030070100d92200319900c954800003c0e000b50302442c2c1c100c40064507180066402c501401c00c0c2c13250281c1540b02d0070700c4c120002d0003000c61120840108140c04286880c0200071503400c004204c2507920075250214054000d04900ccd1144608100f004210740c800401800081c1c800300032401240c64604000c64007004a14040e0041c480790302c401c64015070085001003c3c040c0390307040003d4a28512202540d8090850200300f0b40b8030801001402c02d070700c5040442e8040c01e1050410b4038404400341c1f00903085444030303020880346c4150782400c0d0180b044542449004840420780075088281101c038102020f243c003140e224920035490516040c91340c0480003d105 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 156818426 1250 156817176 156817183
    0x815040c02030c011a10090609051302071505090f01090f0b06010c0b0a021c05160c05070b2b06060207031b0b0a02010915020f040b0304080408030304081902030702150309 75
    0x3990b05140017032100b6000940802c880c004005e071400d1090550000d100001d03409181c0020035101140e4415401d103040a00703002d4030715403a590005165a08101480101e401e440428480b0400d80c900070500f030070300040c07151501d45080908022a45860500000078020001e020f20a030341c01180b00c000c80e5500d0005032402000d5040c007800c40001c4504100c1c0d00003c0b136000341b858290710581d807030b1014500c602800071038004035412004034a40e00810381c5014020110306504030f02c10700480d030080780c94029039007560b00300742c0106280010325080b0000322241c00c10180e107041444042004a00d20b4590000d59500c1503100160031b0542c180360405001c039040d171070700c8040c014003ca51551f84400510080c000c214158007564032071803408070350006c00c10500860f2504030302c0450302401c02c6d040c200b456085510141c01140c81e604100030001d4144800d10145124078007070740d411500c88681c80e03c0f2501c036112220b00c150454104216240041e0755a4022004160140003201d840390b0314150100d28 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 156819676 1250 156818426 156818437
    0x303070b09010f0606020a05070e040b0f09160803041d0403020c2842050a030603060504060207120e03030304080a0c14100605091006030504051005090304090c0815040c0203 76
    0xf00c40c0d040c0200800e031660001202e010140c410411034046684e16917404401c500d055800a086914850108440c2d518401d1801d40000b108419214a40560b0504014180d1140e000e20800c1d0008202000a981c4010f0003031a604240041c29a480c5030560b0000d44030821510028852090151025005c03e00054400c03d078810140c256a0159251031207003090580b070300360551a072040b08085019101588115901814160b511801e21548070882a50720340c1201c4000400c05547d035200001098060144c940101d018200059603101c4a00b020034404002e4020074007808415500e907462910000120b940c00381c1c00041281d180c900704001103820115640018014004901c044841904042405080300025170f03002c20400b9984d80038441d140d44211203002e480d008401d01040b00d21f0182c0c00440d0301900c10001d61b108050041c1c140c0c001c88a00b91034584c010b1780007180c00c5c842e400a510a80f07190070309504120038545000d181810b540c8540445460103070b51203880b00300030107000300140c1c0c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 156820926 1250 156819676 156819701
    0x1d031c0213030507030b180118020114120f010303020f07120b040f0605090d090807060801050d032c1507080d0e0705030a050f0610030b0408090d06020c01090b0709050303070b0901 79
    0x102820354901b0b100300e00b2601034500c045a455222004451070340140b040e2200c2c50100309030390803042926001956091112041e003800540200076010000c5410310045106d0350403d04c582d4019415410020310700003d0b14041717419544484018040d21030102500a00030f5030085d07100e1030698452418040d880010030700200007604060134812070743c50225202c0c8903410380c2e5580182d040da0b42c0c01c070360307564808a10508000c2070f04140180810300302200b03100c04c814000d0400799040d05042d11884d00071070041c83e5440c8907003156491a811442c280b082184900e42002e9000e0500c1c0864841c103080d803061a4115400c207a40358005490903605012010080c40e0040a071a00654141030042d1034202c0400340780f03c075010300000100c0d00c102482c0c0407020b803604510514010b569566903103030143d210b40701e400c0e407068008130b10710002403440c0002c101c2032071100008070708482245081c4a900101504400600a0030716041c4401e07180081a101031641020a411051b2102e03203009005005240400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 156822176 1250 156820926 156820933
    0x303030f130c0506040e0f0f19020702040608071806090c050a03090f020316080105010509040b1f0e0c0a0e0d0809010c020f0d080714030f030f0c09090a1d031c02130305 74
    0x51502d4411180751180e1f0040980c400a81d42d01e0400140d280340c111791120a480b00d0420b46542200a603010380b03d02d03072003d0400a002da484d03040c101d1501140d81e12041c00800f030840070014200d1140540002070090b060184141c458100c00a441401020440010142c1d0707440258140001405120181600681038fd5840c210381c040c2200b4451403402985419800d0000008250404400702481240c12074a10506600c0b0352568007481c20710044050703002d41d6a5034002c1407504801d00114001d40803101d11943d40c403900700d4040c10070300d54030059a1060070480c90900204668104680c0c610b01c0920746500b034100544001500c52144511182c0c110070707062024000c0010070001041c01c28000c100c0e0b40e00d072006440d076281d624400c2e6900c009a00d10148041000004441556a041644400d00d542010601c0000c035003d44003c5030601500c0751207901100034240342500e002000d0b80060095072a05021b641c0d10a2050ba004203a030351031070f40c0021803820b510441120403010355401000d4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 156823426 1250 156822176 156822179
    0x2011b1502030603010614030a03140c01050f0f070f02060402120727110301060909050612030d0615050f04150c020d1101020c18150418031d0303030f130c050604 71
    0x8034001c0d0402c5800e507010390300c0c0030740200e44035202c20100800004014024400846d8079582103480414101122000704424030681036800400c0c000c4174440c02c20035551004510b414040850000d0004c0c180b50284142d001a0961240d400300b00c05500507019560b6080030007000e529203103403083d680d209080e49a81e04250039124104100803100000c071070081408a000c0c81d00070500c1c2403100303100d0070b80812581d00c02044282d800c2e400403580000c00030446400c030725141854030b007554000070340d0800c0195200c03000d10000f13150720a04d14a102c0c0078a0514100540303008c02614a00c114011690440350400d081810144104922044c9a074050001d113103408091400c801c1aa51420b55540540114000b00c0c8540c00c2c074130080900b0608003141480e40f519800003254180c0441501e0540254441c50401c881d02a4144c2c54a880c5100341c0d5582c2c4201984410001c1240444410038803940007042805101031344030072450742008210f00c460030a4002440c0c820f0040700b0580c805500072102240 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 156824676 1250 156823426 156823463
    0x305090313030302070e01080127060609050a150b040b090108041b0e010f051e0607030e0a0f0513020708030105120307021f0f030e0d050a05070209040503031803041202011b 76
    0x1005e008454900c03540c1d030000c1e600c82d002c4600f611400c0c9070000c82402d1800001a1040920b032a40516038091000020416154544901664800c0701d01400054651138002c0c0c060104842003402001070401940c14181020180c4d6030a1041302d0f02c407410041a60b021078280910314040d103001c000004440240305580e014000e004010902c03512800342d50507180011a410b01840d549241461600c40e031104010060421410383c110020503010040120400040c648415100c2000340c02500d140c0790301d0740d1600c0204082c030300610980e4991740e40144410000210000190b0707066610840e13407844a8408166001d1450003141d10203548651100000c80b2000d9480300d05141d00790707a039590307000407880207841503084e2110803a0002240c0d0001d03a0303524806224002921558055142841c80c015035a000904202800e075400c0d00c00b41c20000038031550408922110020340101c0c0f02450900b490250614110814000040d040c088018076060100300c0d404040103195901c01c2d03003903907000300c01039 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 156825926 1250 156824676 156824683
    0x2060c0d060b1b070e04030203040e07050c06011403010f02070b1602100222050d030804060f02070602040b0c0105010e0408121509040507080c03030f37050703080a060b0304030305090313030302 85
    0x1000d0015018007503021805c0e85103c1c20585c031498054005515081c508107d0781d560200083c903072400c01c00c05020341c054502c010301800c0d00030481d00780300e907120300207600405d0b003115151a0011035417481044948002400c00150f5503000c90101400710140108000036801c00744035a02c01c0250520001700581d2001c031003e02042e03002408100f403100f07076448074240311400400000180c04902d0720000100014010f401118016884000c05403c00c0ca860f9103080590f0080c0d0020201128045100e0a03040400d11031f41c0d00402401c103c403d21800c190321459420302c0340340705800015510200149414125100300c00310402d001e04155454074090820585030105030082c0501030203a840b11907400e190000540e81a036910321840c900e010040d40d00142c6000e0b01520f840800c100b28840d0a1000347c5041031401000c40e2600d03103036911801460b000381118001008444018940300b0103121410341c040540b584030f80c0c0340c1400581354451403c42e07850740c011002c03074070340a04038400040101a40070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 156827176 1250 156825926 156825967
    0x40c05070c1d1b12220501090b1513180b04050c030c0102010c05040e040c08011112010b04030804060e04060801060f0e180616140a0f0f090602060c0d060b 68
    0xb00d101c6900f5200c80e1110804a040308400c401d140106000310310440c0c1100d003a1310f0304001c002c030f50405001c0701d410b03c54562000611058800340d5440c0c01c3e41003448400100c8641c450000300030b40b40361060080005a0003006081c41402841e6108150341c10500d1740880745440701c3e0816900030b5a07203031520f03017039a8030800c0020301d40c00b9005562010055500500840c5c05080464130748601b0141400755401c2030620080c03042e0b5100e040050b00042ca01c00c28814628101000300d0702550750842d0b989180000a0181c1c402034280004220810106003464140c8058a18528003c46110b200301d0008015103840c6e0001056175191445c0001c40b00d6440020300c0c21594490324603401c568500d905051a0744e03581c5a030080640040000803040c809440c0644012945400c2c84411070110200001154025007205c0d404600b040b010300c0095608280040c002c40d5042c0307400c1c1c3d44142000402512070f2f00140c0390211411001c215101000703500c0d00008007500c0e60034480d80d05c4080310008000707a44c010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 156828426 1250 156827176 156827219
    0x8030c1e0d230105060301090b0f0d03020c0108011d010b0307020a020a060503011401030908071202030f0c010501030c0512120c030d09050a03080f070804020d0804031407090f06060905040c05070c 86
    0x81c002e6501e209000101e540c103c800050035075065a290406803800f07032010310030040c2e0041441414000070b0742e40700081e684040c0654000c0c500405424000f60a486041e0800041024007a0007020704d40c109107920790565405260050310703a182c41d08181c0c50000802c000039409806c40301e01044107684507001c0c2d4100d130100c000e41a02c5000f0000103400701d0b155420041c00f070140800680002c194440451040749010744112454509480c0d958019600040b182c6059651118010070078043c100c420100504030803039904064a00c21458640c1e50d00034040c2030a6114800305807100c4c0c083e41407040d10f4842c00c04817401e000c2c400769850840d86480c1407400481c042801d0002262023050114803051280707080b1b80354904030f502c0700d0f02000710b00c9038025400c4440e14800c02c030200011b0062a0903881d0940c0283c014100d490a10803078000b41c520040c0b0304e0303c0d40740c0b42c00ca0820425038010390000403284c0c2034400190050300703020211918030840341e01500d0690560302c0000c5c400b5005803140e008444 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 156829676 1250 156828426 156828461
    0xd080705011401090b0105040302040c0e06040308030603120f0307080408090a0b22050d061806020f0702040c0f1d030106080613030f020102030c0403060b13050717060a0308030c1e0d 80
    0x2c0344c8210b4411030f00c01981d01030026409000a00040c24560b0109a04600504082900c07009860000b62251312940040701e080c1804014002c45050401c019204070111100c00c906000080d2403003585400010054030800c03a140022030140103c5208540052002500446c040f54480c10160700a034088224016801c04e100c00426940c9d2300d000c3c145003910130041c600485108280c0f62f0038042e0808035854a00b00841c209050000f0b01c1c0c0340b000304800d410700060244c8460032401044103e61690542e5814031a20389011000280d210b880058007480785480c54942d862100d0100b80105566005417000c0d00c20720080c040e200d1207404000a03100d21943e10039031103200c0164128284e000c140c994044402c8244000c0c00040c5064200401030803025155241c1007a00048190a1324010b072410741c0411030100c12017440c041d003100303841e0b07001c41d0545501481605d90742d5a085103201c014204020301801040d031a82c100340d12401a4404180301100ca611850101001ea00138500c0040b168807004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 156830926 1250 156829676 156829679
    0xd0905030d0c201c0207051906020d0e13022803091b1d19090b18060603061b0d110306040f0b03070308130b0310080708070e070e0d080705011401 64
    0xf0b51a040112032400c401000e0301c424a05012604998420448203d00354060050041056140d00c0004c01c000b0b4100c0340c50b5000344c2e01d071180180c10940c0344031000c41000380d8810448800d403030301075503c1c00d02d0480410050341d5441c140344091080d40e060001120304003218109541d0280e246d080484000d0003829154100d10240c07215200b0a600d0f4440d02100501d485c1086488514542059600c02c0141341c1301a00d49100804140841790002c0c0b00b1204640e00c1400c0c0091030700290001506094040d000b8507040c00c085c00000d9031920014184450f00b095401c1c000802c41392002a65001000c1c45d01c140580d12984c0200c0d4405d03041119040e00035880c0c07040c0c03074090002e07901850200c0007001d0f0281c90b0807800c507220b00d22a61300c8480d01010707000990b00001085c030744050003940700c0c00706800000d200e1418092114107120b8640e01980d81d0703500560782840300c03d10001d1a13076002290390524000c455413000208070b00b80d04101c4044d18401c00440c000c030a00006401c00214001c01e10241b0245a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 156832176 1250 156830926 156830957
    0xf0307030606051303260705010e1b1302030a02121509070305041a0601022514010804081b1507030209030609060106090501113c01020703050904020d0905030d0c 71
    0x1802001621400c44c0c0b43c2e40030420214117840e801e407001c0c41611111030343d424244451503885500500b422a103e039911300c540d48509005200e10790780c2d04100718946031007266600014155680100d20043c0a41d400404541d41614543c102c5540d400c1c0034907110b009107428101e00c0c0c080388020128038024405c0d0800034450301d20074440c0300d11599115400081240549098400d03105e4010803282c194412111000504000d405103000203101100340030251908101c02d1802000091404c50705002c1da0b00180400180914152001c0c3c05d00751b40701c1446904810005840c014002c5421800380142105001d08503905400030071160a0a40c201c440307940302c04000b6039a4540910400001480d868001e105a6104500080d00c0304030400496a2000e098101d10380d440c986c0351a05030b401c4c034150440c0441c54048120b110ba1000e001e2000310b00304a0b250320081c000c0c0c840c0ba01d00380c0c41540e00162880600010750f2010309413542101c02c4a0303c440c02c20040000402c91141c0c5d48002c120191440d0808 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 156833426 1250 156832176 156832187
    0x6031a15040e0109290103090204020d0c02190506060904030e04050a0902040b03120a0309060b030d0503160906080601120207050a0b100902041203050c07150507110301020a020a0b0c0d020f0307030606 88
    0x15507111002c50307a00750018099502d5001700807030018109629810305001590351400034102200031268001159040d00b00c010b86080101b4040b6042155039032821000b1035004a16103a105205807108401659189400c4524106040ca8141d025140806100259200c0c0e400095118400e8030100052018903041580c0c415071030340451966841008515040c0c0d12030742040250510400000c40c5540e9003000107400e144c42c0080c00c400080c0c01104000c07485000d800ca015a00343e850501e42412414594004c00c1170070300030422810301410f080d68400070211581141d10203500042079070700c040f803145454040b607a000c0e40e090200d122402c1001c10201039a00c2104d003110070001d090007921482d541c0564454002c407482845501900000003030340c0420020b1042d10450682c0e40c25500c3d4070318908008141103294680f400390307105201c04000302c0d400155114155812500010481e9103005100700302e031013414503030854a0700100e00c2d0403203400720102031805100c10361828018181c8400d021980b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 156834532 1106 156833426 156833441
    0x111902010f0c050307060906050f010e04030e0d061505031614042c03030906070f020a0212010e0304060302040311030a0b040803060105040515070515060a06031a15040e0109 76
    0x400020f4840c00382c0c4041e1120ac0c4000079410241081c407150001400142405840d4000e412159608000c000f902c0350702c140140800c40f207580060059002c1441114064170400709a43e940214044602c02a1902d500e0b003401c03018682c508000107841e030041c00030030300c43c0700542d03090b07908042159800c43d0f648500c000b5540c17802c0502c207952800310001c0140040000540000004680c0400d1741d002c0c113601254190352a00d24445860700601150140501e14800054009250754043c1c021300100e078081d0352100141c11500041c140c880c41c0030700000f0150b80383c0100050000700b9000c06160070081c1807401d942840e840c2e01c0030611424801d68411401d01002c10004100300c420800720050030b1440d1240c00da94105800401c071070b008107011b4402450745954035103186c0c2c003d0103400c540300340008080008140540c0409000c6a200f80210316400554000200d8410124080d40c034 = true := by decide +kernel

theorem cover : BRFrame.Cov 156654676 156834532 := by
  have h0 := BRFrame.cov_init 156654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 156654676 ≤ n) (h2 : n < 156834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
