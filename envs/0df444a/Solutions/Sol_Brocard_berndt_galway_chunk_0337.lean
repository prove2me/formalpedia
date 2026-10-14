-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0337
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:17:08.745492+00:00
-- url     : https://prove2.me/submissions/7f1a5934-57a4-430b-9557-cb322e7c7088

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 60431657 ≤ n < 60611513 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 60432907 1250 60431657 60431669
    0x5040e07060e06070804060e190f0302010c06060e010803180f0105070b04020a050a060201330e0403030b0306041103011401050f04110d02070803011502030313062a020706030b040204 80
    0x8188144850792041c0c9203440c0e80203000c0d008918207403071035541e0030090b4000d5104900041940c0403c0705180760000d5003180103043c0c1c520a1816500301a8001107116003444002c1c140003030349050100704441038000d02c0041000c0240320a6942c1e540c04080c1d02d9a002202d140015031091003110300501d05403e49422200c01a520581080d0566035482010349014006990180e0303400170000c1c02e9130b180b20312007018001507800031924111a106a14056041135401e4052720301d49021340b103078031122070180b5044581134500138a454859007010b82c02048004501070301801007004000510003402041002c0c180300f9002008111450802c03814804000e000765948001c0c4044580031a207007a41041100c401c1003081c0300d10302101082c0060480c4d00110046036074540100040260b00b0414928540200f8503001031032442c40d00c24441141e034180800010103032680c800e080d00a140c5290440c43e8000d032610303c0b820001141c00070103565034070b0600c42c100000303003014510341850815000380c0d021204 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 60434157 1250 60432907 60432913
    0xb030d09151d03010504121805090a0c1e0c021206070806100203042606090a1101080a090b07110c0307030201050f0c0a080f1206010309120c15020c03030a050105040e 73
    0x41c062401c41d00c000103a1464076040490703845000742c40e074081c42040c1c080c0b4807074900741c0f0003414040c1c0e000d00082050210240c00740490074041200d07407599035030107510260b6404001a9032400740025240c03000c460f811381c10f50b50090041100000d400090160240c1c3c000c45d88484a650f000940d03540c2c66030102e07007001c00136007800c020980c03504004441190b604950300640b170820340c9410008070b0100341c045003107140602c2401800055401070084c940c011048070081c01944e89075490ba80c10810300f0000180c10800c5d15400900c60440c0e40c0e202d005c003a42c0c03041050505003055007005081810056004516005840c08040d552a0009102080301d03410303120141044082140190144c00c0400d001d10140140c6a009001480801c001d00c40b455441a40c00d40300c8440a4905484440060990b4141403805d261034003c01c800c4c140c00035916005240400c40e00781945400c03103402c600f040d404906540081007039504140048081e52103620301b92803c0103240e0342c030010482a10104040c1e02d400b90 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 60435407 1250 60434157 60434189
    0x6100219240f0b0906010c0f080d0203090d030b01030506030a02041d030f04060207080706050301090203071709150c0a05030c030709030f031e03050c0d0c1806030b030d09 75
    0x59081034440402401410442603060510a4001c0380001d003441003103805940c2d01c440180c8005601c6207540c00308058808070010300d840b030000f81c03124040210203402802915100d9041081d100100c03540c0b42e140340020b54807401c3c00300509990301e84031a1b5032800f01c2e0400c601c080c0d65510174400c60784070b03050046c0104003500c0541c0a110040c004ca04002c04003401012041143c007100300010501c58500b01c1406a945160000090034202c00d600103003010340011004200c526481400d681c1034400d00b0500591b2130300c40c81b100307036810221007030005880381407142000860304021400b483c0002d00c0000038003150307858054180c0b031840f07801c0e556004150103101062410011201865009515061140e8095100e4441c0f1440c09001203080700020315000d40c003561020310b1220720b042503049080510080c1482015110b02e401050200031040f41c0e140d40e40850a0700c1580c405181d5810310607900d0005031501e4005001e0145641c00c0c9001e0301c2103d40c05030311144038580d071104490020024490368 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 60436657 1250 60435407 60435433
    0x10e06041a041508120403120f08010306020c03090306040b01090e0601240c050a0501020d0b0f01021c05041d01050f0105120a150b120a0b06040810020702010302040b07120305061002 80
    0x140f030800c204030381c82e01080e0b41c0403501c038a04101c901450f413030702c81030142c8880c61031801000c0b00b1040c82076581006035254031078000c1030700001d802d03040d00d50003100541c642c00e00100503441c5014041c241641849580c09100a00c040d13040240d05803a075800c0c0a122a00b2000c984aa56900a1160001c0d070511007012100c07681c04204608000d040a203044845040f268817001e24092440303e0a6407140d41c00221801d607817403a4880c0d01c0424605444c0c5d18160110100041e40b82c00c140e0040241042c41040300a1a03248201c1c1104c0151500035003003110703c1c5040c0c0341c64040c1c0500740681402080b0369000050958000c4050716981280101126440c0e550f192880700a0030030000d140c1c185260285005c21100d1852000c0d084048081d0070168080c07400c5170000051381c000a08041c0600010842031020650201d20920b00ca28103500241c1d6030300700c504c0100c3c000e2096601c0360440c100c0c0403401c02c003080fa00c19001040074105036418070a9444031b500b040001c005100b00000582c0c86000c01e6950 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 60437907 1250 60436657 60436661
    0xf0b010c02040e0c03030304060b09101415090d14071a071209180902010905091e0603070f0806041214030402120115060e090c071a0903070614010e06041a04 69
    0x3c04905415103201d01d10600101c0d02c1c640058504444130350700e540845c041d5060080b1041e0303100d20107513140800240b070301501c209080000b41c0c86c1c40c05000001c2c080f0503501d515408680c481c140c050402e2040440d24100403020f4507000c0ca00f1522801126000100014800246d9400721041801e00d0f10704056642c0e1303030b541212131130004414440f000000207104084200100800d402d880c4010030300d12858030004000084940260303200c2c0120806000030341c002c1d12000a40204810504445500e031400001d1500c90950b004410f00140314001090703040d4041585030007144035941c1d04020300380465050719240300301900e01011400501c000f60140c5010070205100e500100000074801e41c1d0602c161001000d20703044807010600380700010b40542007030385541c1d9100f030001d14a0340c200a0140c0d502d4000c1b40e107500c4a4076440d0501000308086540a00440f8901d03940007108001407294000c108180442c2441481038101d2054001404e605207400307114030319104586d4030420402c0340d0b401c01c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 60439157 1250 60437907 60437921
    0x206190605060d020322050309060d1e0603050d0806030309012a2d020907141209010b0406150f030203070309081206150a2a06020d090203010f0b010c0204 68
    0x808192500e000151a441d0344004082104200d40003695070f14001541505160102010f240800b140c44002e1010a6000c01510f1030780c07808844095a0b03842488801c006070030002030103012000700542d035005c3c01150380c5c009022644210180c4104041d00030f000d13a8140300c1100d1140d0160000c10110b14a03600c10502c050788015040092058503c50500406048101540845030b00003590b480400903940100306002148020300040b61030071142c0c0c040f5807040800303050322042c440c00c28260700c04808600192000a0030020055035203140c2800b803540a440d440101c14000c51400c00d01180300c10500f0740601c0d0b80300440c0c460181c1207031020401c4000758402800d003810540d80f40c0016001481e00390052003420031104208180d81005002c01100240c01c24048040740740c100000024075400c026003a900344c1011594000401d0182864552000d0302c01001700300d540300040e0054146c515a121891f03042c020b40080000a010101c16800c6603100840b29011076200c886400040c40c1c81d0700000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 60440407 1250 60439157 60439201
    0xf0c1205040e04050c0310061202060a0309021201140c0901021c0315030305040504050106080f04140a060905250f050906040605030a030504140d08040b07050a050d020309030610060206 81
    0x14907041e901d9981d1070030039038151800c40d40e94100900e80e00c40745c5010031400b02a4604e0140800405c0d240082040800792040002070280300f0205240d0b0308bca010354003c081241e009006810a04240f1031070900820700e00704086040e1500c0004502c80102031800e0b178600d0201a0018018214844c00c1445485560100d2030205a103840c02e80c10010750015582005600c44c0d00c9440e05c440c1000f08110aa4005821010400170488204a01002c02104c41508142c00142628003000344045090610b050402c0c05000f007824494403008101e00054400905508040d0f840781c0c0e01d408100c81e1035010194420f0764910106014103100f03500c0c00d2011030b40c020324001d10018826503900042800d00d10650019000709402260810056a8a81c441e400c200401c542c0200c0481030742d07490300e41a004900401010031008103152003040810040d17840403d0b04041241c40000c40c61400039035961100c1080c80c0a0b0141002185000382c0700b42c4813400b42c46c542d4001d4170301982c2c0c20290b08889a8010040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 60441657 1250 60440407 60440417
    0x901090809091b19030605041a0607030210060e040b1303120b0f09011502210a0c02010c021801150207081203190501060c02040c020307030c020f03010f02030a0e0d0f0c12 75
    0x140d0b005250401c0107100600754510050760707107100c2d03113005421103126500240c095414030303180060086080f4000c1c100100300301e5502c0d07200e81076030504901d4004844500110300340fa001c008101c04c0034003000755129900c01c1d104441d90795a00b010035590300c013400c04000d0200300b0800e41074120f81c245802000d00c3c0a4040c10400c4985002c500151000b0000c0c6d01c83c4891140123600801010f40c144241d01c0501c02c0e03410421904000c1c0200200f15220382d074100001c000c860003045046a108200203030f03515400400c003108903052104070009040080c031421500c200a20181c5c0b00c0c09002042020854816401070801e0968034500b00a01d94001004034005207440320a80104000501c10180039040c0c1d03641e4441814403a10600040b520000031300341c19036000b8014400040d90200102842079816111201c2190241001c02e024003042c045c510304441c000302c1088035a40b07299220122009045d0304585001800704400d9030b01c03141c16102500010141c800140102d00c011a903841c10517918505 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 60442907 1250 60441657 60441691
    0x3030702010e060a17041208010803030702150a0204090207060b130b03120d090b0901091a2806090e250305190c0e04080702041a0a030f1e0b0f090109080909 69
    0x40c19185e5088504a4400b10f008014010465218401e9805000100300840c603604120f50042e5a4143c0e0000c08040e002c40003002902e03044940c0c05540081460743c1d425500c0310071a1500c000500700b242c0105020301d0101e012440440654080d001003200054098048ac41880041401c43d41c0212100c0407195250450f01c00081d15080115108008140000031030111a00d4400f1141c01c40484608408805605003c50000d01c030540e4804131280e0031501c101340e001c00f04180040c090b2a8403024180d4a400c0910381c0110012540e4116542c064500d80034040340c1001424001b000790001510642c003024640d2003040c540b402e0000d071240035030074480c2119600e405c00c0305040f00845080b59003620100344c1d00c1c11801c04e802045034160a40c0d0446205418600c085040210b2610018143d1900b500755a418084c0d9481040808803c030340415014202070301380a8103010050324241c0c504c5440e8000501c4080061195019032540039850310728010b0142c08201c0e085001600c40c91600c50843c2d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 60444157 1250 60442907 60442937
    0x7050a26090703051015052116050f041406100306050a0329090c010f05070c090c170106050304111210150801090f0f15060803040f0503030702010e060a 67
    0x60041d20514100d4002d0425034250b1902a0801c49014a1414040d08104400d0414002d400d51001034902c03d4410700c00782500110a4400440c582d54040141c0c000c00c544064035004000240013030707410a94401040703005132014441108c6407040b000c0050700407078011401a240480c5015485252460003003082600c440020326260141da000711600a0701e0006443d00482c00d005074a84218150410f15151501e000c0c0703a030301d41c48910707521410440d0090000303e00c24098015108040c0e008078402d803085071285240c1004098155015000c58100f1405005a00981d010141612400d540d50380c1561559a900304010040c00c0b0003d074040d130320580c1302462030000c21200100d038001d40b070045540d0417100c0e03503008090f0b0503803c051150790400c609280883d00c3d0000403900300d9840001c121a41002d420621070107034086204480c09400c3c14000140e0240010280c019569100d4441d01c006583ea4200341d80ea203d40c0d00c0007400314a51200c2c14a052030300c100600000300580c1030281200349120 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 60445407 1250 60444157 60444227
    0xb0d08040602010f0506090f040b0714040905040203070b130e04031704030c060501080a020109030210030e06070903030810140114090301020a030213050a0803160203190501050a0c030507050a 84
    0x203040240184c2d52032150055101c15401241d81140c0305032110b00440c03c106c00040380045000f030003e845241c046010a031500d100380d143d1054070074040815500c0c0c90301e803c1ca28016103010384045e4464402c42e90046035540003034044400200014401c0c21000e8500503c40301c00c448021300690600403000f0310318a02e0040c07107810611461280c2d40e09100107801e840c0807011034106810544041e402201a800140d07009051142a81d4048070446d80051291000310058054541d0482c818012942400004c1cae0700030369850283e07032007034940c00b025031b0b9188124607902c0080d10607403401c230f800c10340c070300300d030b65004505c04c4805410601a00385400741607804039007642d00c80000030700021f6001580d2806918400b240901034507044401428041c41c2c170300c183c0d07940c0c0a403c20011700c209605ca500021550b01b000041c1100000a00c0400f6083e03403401c0003070081c28210740e100400ba0612400c0c6140394403d124035032045a95888182c01c3c40c0030340328101e40740c4032001c601100c0c2030109004c55070a1403800d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 60446657 1250 60445407 60445409
    0x308030a0e0d0e03030406030518070305030a08070302072d140a0c0b040605030c0c0106270e06010b16080f13051305010308041206091b060f0e0307090b0d0804 70
    0x98002080e280c600c0035841d864418240406800c1120101101a0036500802102c1c02c440040c540440ca40d1600425101c030701c0c401d0b40c0200c0b46c6124104c3c002041010100c0a00744000303182e110b8000039074424000ba026449010401040040d420350302c4c00c15007100b4141034241448400c00b403a10030f651035490140840404a150600d5402115403001b0071143c81511400380c0322091055003001c0c5000c00103029400050881d0400000114001c05025006d60004008000c4071078010444110348222690001040310340042032828111600101a000144c060407601c40e808014500500700901c02c04c441440c46d400c807000b1204205e007082c6008000060080700c00c40000c400c0a5910303002c1000b95441e880326406062900301001000400e4280e010368040b41c95092880c4200d51507860100028038100200074520821603501601d072400a21b03070501a50584e4462032040c2c4000c01c02074030806040a0f0340c1d40e059200c2041440000d81613002001c1d280da0240000400f00003c1e070320380440742c000b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 60447907 1250 60446657 60446671
    0x70b2206110d030608100b0d06020a0801050f0d0c050f06120f010e010e0f0403030b2709010b0414060d0309080d02010509060c032e050406090506042d05070504030803 73
    0x200c81c00640414000380a58540030034141410003003189419841d544039a16101ca040711142d07501041c040c0c90320b84020100b840b9038005011903a4103074001c009040e0803001e020b0140100001d010000d81070500010340c050b01c940000210405610741020803022038460260030ba08560284072400c070000c807690500e8003504a842d0103a41f03540c1802c0b245110705005a00ca50084881d50301880098042840b0303150308181c1500c1d001c60356090490100d820100f148506c02020714090100c1080c0043d48501a4010140b80e0002c0c45007205080810054811001d0802c1c5102030010208400d840e00e58001201d1500c242419031215640350903450502c500050f081000d40d45980400c400c24400380241980700f020351003918214102100c2a201400e61884070041c419412401c260400709812a41001040014020301103142c4a0070180090701054508502660812540c0000c43c50b0700c1243c25600f0604840070030602e0b4a4a4514000e803d02811034002e2000c208004804285400d0055118840d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 60449157 1250 60447907 60447917
    0x20406020102070b060118060e01021c0309020406062c0301110403120210270c050310090b131e030e1005071a0c030106030218060a080708100305070b2206 68
    0x11904116850042c01420380b4100101c111f042c460181e0707045411070a4494501e45041002e003100c005038905801d030b1030220403080490f586a02c440340c1c50380244402038030a0f14180186951001c0035511a401c030208459000e10807031030500d19070100e02110110300e8004001040607248414442135560142c0c005440e14000b1241d0704030401d07010401c0c1581d5031a444020807031894485a0008000d0140e103403c410080040340d06418020f81140b41c1024000040c05e40d119541040a0b1400038030b02c041c2c080351003a2809002411089650050601072a0000e030901c030706440e01e00b02e07090144880035048041c80440060342019486403031000728184895141c480c0d45034105d0134081d481d001c000c034405190385124010042400e0080b17040c1e90442e0014240540c4640d0b41100e0b000944240c1111690040004661a07414960100e001c80c02880d00f82c5908000792200d04a00d0301c1e81c0c0b82408040c00303a61280c0000c00c10659103070003d0240f07100600310103480c2550b801d80044032920580c04080020 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 60450407 1250 60449157 60449167
    0x1e030609030509120604080f07020f030607020d17310c14150901020a110315090102130e010b07030c0303060506120121020a0302101106091c17061909020406020102 72
    0x401c4c06907400d80d000c280f0400400851409a440701d10b10b1040d90068030100c1804a0304030119265504240e00c07200380101569030324502024000e42d40c1e90403001c10030000e040100c00b01c0d070b10b07044002c4860061603d00d0450b41d541c140002c800003c0702c403101501064181e500030b203002068104008002070b104e07103026000c018030200104a00e003c4070307a882e4400000100940c074140d0703070001410507005510403001c0c8061001400024204000d801c0b0f03a09a0110f280c00300402150194000d05c082464071016180558913a60424840c000034010101040010446100440c1c0036010411072207201c0d01d001302d101501c580100b9071a07004010518498140480103020740d0040d07080d21600b8480d6070405001c00c1005400061004405100c0603000781c403000010114076210f4031010b024448204210f5069043c0021400d40d9010003400d4000030005a0400d0b083d00c3d480346081c80d00c1d00125032a03480140c1c0f980410402080680a544103e80c3c003e09000202c02801c0d001a00081c62580c00040c6c4407 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 60451657 1250 60450407 60450409
    0x70c0c0b032d06120f07030602030414060405070621020a0c0b0a02130513020f0a05040f1202060d0c030b120a060f060305030a050d0b0402040e0612070605041e030609030509 76
    0x80c01242c02000103150070916200c150701c40070090560700c00c80484003a800210005011130501c403402d20950ba40307004040c030200c14018560010342c0202d124103a9080c2030320514408a4507154103444c01480d94001000c2004080d03c41c40090988102400042c50004510b540401c226401320103000003040345242c0c0b40048c000206211a800b500140c404e528101c000401000359081a0281c14402c3c10241c405407205441030f07054074020040d092401d0b940d082c200a0141241c3c00a1140981c01d10000303801003041c55612400010741640a420a03061201e40c0800e440601040c03030b0400c003016550f22480f0b420740c0d910185d4a1142d226038002d00102072a07801c2580640e101c0001440d80c8508008040001030303c0002110303410240c1346000c81e203906410101c10042c1240301002c5600500208020420b0b9103001c0c00c40307000d8072003160405880040c1c000c006844a0062080e1004510184002c101c1c00d00e94801202c24000795594582081c4e88960b103440480f480c1100940c00100081201065 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 60452907 1250 60451657 60451681
    0x70806040c020c0f1207050603070306051516060509010e0607031b02210708070807080a090905090d0e030c0409051c0c0f080d0e030a0c020108060612060603070c0c0b03 74
    0x29022480a841c540404101041c0c442035072010342800364a000104400c1207030701b48031003005054020950f075070740e040400c0001c014000c1030003120700c206480c2461a0031459618120b55030600d911913400703a01400703034652030020035000704518415501e480000d5040391080c49524840c00c40713a10000340d107041009040c60001800c01030304003598090320300c40c0290402d030764000012400c03c10003266038100da0318250841c1e0055440060844002080a80c1081090409880c01e41080c3c1c0c0e540404030340e0749501700191501902d02c404141c00a00392076070064440d60b1001c1034140003904880340c400c85140070400720f901d00341041d01c3c0b40c0c00040c0c0543c181903000180100000c881c6c640a0717420b10316038507150400f0110140003440c0003000a0761748580603503078001482c1c00248605581d1111056840a0120101084128001800000003030b00d1858400d0540d000c01d0641c500300c071140e0b600c2d101400b030281d102038980d40502c0084e074240313000100031300350341c00103000000e52003070700d80c1004e07a65140 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 60454157 1250 60452907 60452921
    0x304060507090812120405120a0509011205040b060d020103021b01050402100f050318010605061803010506010305090a02010305090a02190f053106030204150609090204030b01031209050907080604 86
    0x1480342c0101206000c4407030360205517032201d014003201401507284c0f440d200f03107460300c902c20b011200d02c0c01151020149801034041d00c4090400c0e203d80100400c1140d40c0d000b00c5074111401442001301c10041452410014144034403580b06040c014600070048941500411004c2000202a03441e48108011401c0c00340081d060030302d80342082624004045070103845c600006100d80305110300c40141a406860035040407008280250120380d544d5026a554a000c10445105074000d6003014086042540710303120340b40c80742a85801034240b03c0e010781c2c01140500009041d008803845000c2e48000907a840c032540c12202d81c011004041c80514045000c0000d103c982c1c01144122030340901c4041030104201c85040d0700324a50440440e51100082c1a00145456000039411030320b000e607043d824180e1455000c043d6442e0341c807040c1c0f02c25a9451031100760720850100416014100c001003000500039181036a4260700c0e401c00e90441c5880e6408161109400c64040000a92820034032101d4242446129 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 60455407 1250 60454157 60454169
    0x5270102040e0f091f020703030e070b090402070c090f0203180c01020a0204090807120f110c0d020907110303130308060d0c050f0102010905010e01020705010b18040f1106030406050709 81
    0x15040928110109160b034500820419080e901480001c54882081c00902c60b141d5110310580648010711304508025041000110042841c1074040340a000c00080c040c4102c9410012552926150100748400ba4104010803100e03042d038106d011541c00000e006501051220210050b12071600300805488401a052444159004804800a5640d001c030702c000c10301d42c0680300403503030700501d1500300c0700c0d403181700005041003490f803032810003180d402010011050460f540310002c10f601a00a03544a4400d8268550300513440042c220044c103204144a03400505400d00407150346000180600b1a802100c03081135290740070a84604058001040541050b410ba520f00d8102d011950789407440804c40c085c0328410146c60014000baa0b200350803480041c0e503c0300003440451890310b6070764040e4102c098111021b500b8203a80e80090300b4484000e108404450f0204501c948880e01c4200083c5010041a00c0300c04080c2280103e036150b100041d4060780c41090000365510381041c3c01014040560004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 60456657 1250 60455407 60455411
    0x10914060a06050d0c0c120f02010507020304050d060b01050919050a1a0714011d060103020a0909051c05070803040305130b03060f13020408072405090108190f052701 73
    0x50201070783c080b0503207a18922107000007441d0300c51400b041d560308103040d01c014a0702811094000c0180c1d8001c4c1400d049803459002032056488810050b40c480c0228015180c10100200542d001319250350406505030308181040d03460031020501160404400e4108400d00c0e08500000f00403d0400c030200d0b0b40144031000800a00002c10300c0d0a48151041000c05800041c4685080b140f00b4802e40c40b180e5262070092001640995000c40583c80303880921050307110764040100001c00071301602030160500d501001826115682461500b00510304071091020008107200160000305804021030003030740a41c03030b2681c99a841c040f2107049281160040c42a204c814828490035032109001c21001c0001183e010490281c141d51110003801503a11000307040c405d6181c001341018071010110044162200148010240020180c030a07100d07141020b4000351b8210002020142111002c04101e10000d0010030103000d020070344000e0b034400b80d40d007980d500944c070b4440d50404c48001721411007540903002 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 60457907 1250 60456657 60456659
    0x4120b0a021602100e0a080c01030e060705160314040306050603010e01060f0506180402031005030f010c02060c0a03090b01060e010318051203040c08060f0a050a05060d0201050d0e06010914060a 85
    0x14504001c50b0010000780203d00000000b2106405075084854020003c1d080d05c2d000f540e41d61010b03a542420f0010b46000c2841d29850407001d000100309144240c103e41c5800340b40502038049405185042c03841034040000d0804a41410401d00b0700400086000d45804a0305040402c105400c4070100b1070f0150032a8075050b010080c0f146001003010898000700d4040b625a00041c040c4000440c2c8905410ba00c58800002c010440c40c41041304d03000d9480580407a0b82c0001c0a4500031308981581e14440f01592000c0c000900c0036002d0401010399158610380070070145190754517041110f400707030130020100703070521142c0083e942e00d8468072401e809003e2200039a1030907510303000d40f00c0d50b200c07c1102d4600c030004006000e010740c4075107a8000300a0350048410718a4000c1030f00200403401e442c03410581d030801e00416840031850047d60301030075005100e501818056801911690710010b11111429107920030f04c0070071041031050340e008050710381c3c0c00b01d00030000340505c421180004140d644104d40c0d1000c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 60459157 1250 60457907 60457927
    0x105060903060103060f020d110301081515060306041d0a0506100308090d0203071a04050108060406030308540d080a0e12030a09050601150c030e0a030804120b0a02 72
    0xa990383c1160303040500001e41003d4803105001a21804850060031070420903a8800b103140e150045040f1400c00c010380d8401a0802211802c1c114280c40040303586003000030f04801c030702e00a001190801ca0007400018100c00d021545000044021412101178001c99a00824040d0a2004503403110403050b0700241e4904598446c200c81c003910344414010b00d4415010003c54400b0480d880180c03420403c5002500280141c00309254007d0150701e00280c180701c0455580d00349170183c0000d40398103850b1003240f60b461701110300c0c000781d103040003441e2400d103500d4200d100444540c400100c0c6005801c05c1c1800c094101c410b03e40303049445441e940d02c3d4030500070600007941c006000c9801c8540240c010950340032020390311f860645400e94400100703e000050040340c0c002940709240c4c242c0f003071082e1542a030740c540300e000916448904030030104690381c542c840000d2242c40300d20040c07500200010750322901c4c0e85448001d178025800c03030300b80784226206060610a48600e4294082e414490a41c6813244c264 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 60460407 1250 60459157 60459163
    0x60d0906020d0608060c160804050a08030307091401050d091a090d0305150a0614070c0f03060e0105100b07051e0c0a080a0f03031a04050c0405040b060f041502070902070b040b0105060903 82
    0x100300e202d24013015540c03447c02c00104808440c020070b001014003d440e910381003060349940c800c3e11584d0210344481800a804200c0c00c01104c2c034000140c40701e43c18604113240c1c00f030103000c030a10300700c5002580440d92a06038189003c4d00340140444401844281010071020301250b1010300901a64000d2140000031a5546c0d001d201c161109860300482c14182025403620703c0c040d6100090448440b004082159090000300c0c10840b40111010320401003490320140c00c0707480c281e07190782500c1c10108083c08100342d110b0060079514800c40c00c841c800401034805900c00030700900c041030590040d00500b011450b0078404440900715107009414040030f15a10041a007040c0170004081c13513118444004081403034142170619060241040c030031854001220140f0307501601a0a00c25031078003030015514181308060304c114100301008a403815007094034450001400f0100c0e0402c5101d6100c0c0402e11121358000713041c5103032003140c0b103110300d0803c2d1914154440050b0003c40c0107510510404500765000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 60461657 1250 60460407 60460417
    0xe010f0911070b070c02090105121e03090315010519140108100e040f0312060609030f020604081002030105040f111207180608090c0a050d03050306060d0906020d0608060c 75
    0x200500080d8500a2801030785280070304030000c0c0c281c1c40c210040081e06500400c008a00078800c41d00c04030141e032100104030042a0307000100110398410b00001c00b24000301d051070100364401d201140d0038900b40b40c0000703191586e085210764021408600403c601d08113407001e01c1c049102900c07036044c128203100f0002c4913400d001d4652130402c03404102046074100b030622020007030a00400c00ea482860306080042d0070100c0548110b001a8844082111d8640c0780d1007440251011681d410025074650340b2040444005d86000380ea001d4410800051061404c01c8410f08004080f2400740e10f9600d000d040104a1302d6204103080100e040c84850103941c130302c0601300c3e40e0b00e60b0b8449001889858847c011101d0040340c9103118040c0341812804211140c0106445208120a0040311840d40c108010b109020781c1502c100b9030085c8580748001c00090007080507584c02580902014107080c003001305036094568244007626116400180522101624040c50028088280061005043c8003040242130b00c0f039 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 60462907 1250 60461657 60461669
    0x20a030f080402041b050c06150120011401080d030e03071101030203040c0513020c010b100c080c03090a030c030b06180c070206090402030702030a02210a0f020a060f0507090e010f 79
    0x842000604540c0c60fa48200140302e0704c5d10428840d18154032024103281d201011092507446860000781130140c214641c41c10300401a03641c60020b01c4451216050062030303485680d065501d90129081c01c00401e100307940282004401010f101d160302202800300c0e4840405100c4a400400904003c64440c441081e054402031a00599a030b030381c3e0414524440b84d5400169110389500c5000045c10800d030060071780d00c030910000304400c0281408001c40e420300b99540e18003003520711024ac0013040022010f40b2901850780f0680340b80420150000d0b0396000c080d0412228050200420700a0111a06211340d005106503149048200196900080349800402c043e1b01075200052400454942d241560440000071b007080d0340342c1c2040e80001c1c2d240c0c0c010b940460010b110381042c1c4031b610011103603682c29460102134814604403200104449043c5039200040940c03241d0001d032000202c00380b10b0500d002c5140000051346e414401401042d05c005948165000301c1404014000d81c00301280120450305 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 60464157 1250 60462907 60462917
    0x7060f08130510050106090e0103020a03020d020d05120a09060f080103020f01030b031501090e0304030f06020304030e03030a030f0501090608031206210a061103091c091509080607020a030f 83
    0x349604403401c0190752040d004046000e045420541610b681d00150b060b280191510b107400c41d203d038101280707201b0901c006503003c40040c40401c0503041074490720f0401ca0001c1d10308424460b158030350340d00c0c0c628264008510050000707104005c0d00d900c6850800a45040d1500300711108280c1d2008062410601000e031141581000e005d40a131f00a61194102d818060103440c8a880002050040c80c1801d128000d81a801c046512100000c080100da00341d80e402040c080303407072949480700c3c0c00075040100102c00b40045440348d840c080c1d40c20005040d98510b9036401281c00c51106070705406990040c0e004115003824000d0500420f1004404c0d141d0b50b14800840c041c0320b542c0d13000000e200035041131201c82204000110881c06000200324108440d000785c0d428421440d807426280210310007250450825048140180d048404c50540b0403410741e21854802c10303c83e245d043c900c41d200742424480021554221041007540301c14042070307500100600251030005800c3d127015125481d40000074007008 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 60465407 1250 60464157 60464161
    0x3050619020d0c020604120801051813020603010305100605120c151603050c0601060206060f190503010c0e030609070506040e070c0503040902070614090c060708160f02011107060f08 80
    0x140a9054850600c100d810900c40c8240943d00603445180035541600c92110000c4580f14140c041d1503c141250030203444002c0c0510070b0340030400250f4014080300940955902c1d10000359a031903000e98084e5005001034140400f01c0046141128816032045001e0401101c24102141c408280320750004020b6a052003240307002c4110008610410300740c00c0c0d0100004000005265100300640140700c51300048a8a690b04c0c0c00051703941e814121041944415445041c0d081404d001c800015040c0141ca205282075032144006402d4912001803500022540d0031104164a0304200c2550000e2180018200031410100466400d1055004010b610540e4202056005200741d4a051031070b500201070343c0d261f64031a11804d005c1c0d8042003094402a04000b998049401c0c40700311240100c00100040100d003a103a018408550090803040c0d404450031710100001b82c0c1500c040f01c6502d8810b1909004090f120301c0054050b03c000000d5945d203900c060300500041d44c000a40e24030307100c02c60030f0000440d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 60466657 1250 60465407 60465451
    0x10302090103060906030f0507290706021303061a0a030b0708090a0c0306060e0108010b0a05040509010906060306020702090702030309030304170c0a0317090a0b0f04172d04030506 79
    0x42c1a0f80c3e8407044030b032440c1003c000705001c42d592200e9005880340064444803541d03080600f281480343c0da01d041d000c0c08803041e041510030001004010291284902504042c02d03804180741c0c907080c1e41d1040d1592902c801189211105408202840700700c112040c09583d821500e800c8902d4100400d800244450040032511036a000c2140058441c2e105400d060059181e00e05080031305904d01c15450320302d481c000040788144041c0641d26460358007526041d1030614010810002e0100640071195955131074141c403010840030700a170340145024440140c1d5500d20780c0305100000c41d0040c003000454100b8024015400c001204994000f60071401c0d0220b000e409100020a5100391070b44205e203072080c80707002c0e400c0541041d20502910008456110140e58103d07405884981c00341008102d00410000621000844d00640d070f0824000c0701c282181141040d4000c82c150301c4002842c0800303a102c0300344081a05084400f900b000d9180d901d25041900e10390fa0f950352410050000c003000e614851500c070003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 60467907 1250 60466657 60466661
    0x1b01020408060705070618030219060204080a21031512061e05090f0c0a090e0a020301020a09080106090213030809150412020901080115060c0f0b01090b120607020c010302090103 78
    0x152074408103581003030502c030201a003e540400011681c0074201240c000150b5041c113105031206406030040c01481d0f00440f40d040c0c0d10240084105c80b2607078244408203c0420400201c01c0300e5102e03259980c40344498010350011101c40741c0c0c1d142d0405040c00880344802c405441c418044486040f8412885070301450988058410004601a0308030340e1000500d04040c56003010703000707461100c2a11401940f80ea621038840d51300e482c10035040862800d081109101e5036205d62070200b012419200709000301e50009003680c0c4010005000201204800d221001d000c0c40741070020714944c0c0d811842c2043c2d400043c1405403003880080c000080200310b03158603440d0003000c0821005600341540c0e5a903110341400c603000020f01c2c8160301a030411030010804a01c1485000e0001030201c1c0c804016500c0c0190880303110400c41c100b01c8054180d14008000210740b004c065004e892904008a04001c0341418000c0c0c1c1815242d001d20b403039118000341b0862940225111100e04028030b07000da65a0172200050300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 60469157 1250 60467907 60467909
    0x30c060a0605101115040b0402130e12090a0803040602150a060302010f080c160c2919020a050d02010c0f020309010e0f041e0c0e01080108061306141005190b1b010204 73
    0x3c10307814440c5c208810000b62000032440ba5100301c41d004402003100792020102c8000078000364a0394480b0455009404180f8090046004000c2129500c00e4960300c041d410750b041640b100002d41c0c002420400b411500421455000c08421820001640356400080c20100d0b101d04020911400702d01203036889403c0303000c55007050301c2c10320040000c0146282c00580414035215100040100c51810b1000f043d0b11689042d444408400c0c81e410042c0804003004040500181702040d841000d00c18800103400380502c88c00080c0c66000003941c0001c0f10405800813a50104031070442d08100060070290780c1180a140d0302c0700b401c0c0d50f440f41c004c0b40440810014089180c3d404194645500c00e0500d106041d0000e40070aa5030396601200c0c02558030054800d4407003070244507841d03000f4200207120324840c582e4500c14280500e10119420740702501d49640000c0544a01580105110052109090003422021495040812066160726020820003203000c0d84c2d45181040080140c204080182501568 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 60470407 1250 60469157 60469183
    0x40303021b0c040c0e0904060507020a021306050901060e060d050a0605041a0f090103020d0f0201051204061a030d0e0913020a0f061b0b07030207050a050f030c060a06051011 76
    0x2400076004801e4039696110014002d910550806103260030080c40345000500c144009041045142c549030745860180000a01c400c04501c5443d240c0c81c0943d840980401000810700740004c0c86c241440107024002c41c050304900103011418030400b0007520380e80c08846880c1c2c0d00c000c00182c1c948400340110050216a03003c82e41c881d0801d8400c01c01d442038542004038601c1c0c110f80c946810104181401001e0000b4800030350b01404102c0200081a0b170b05e11120b0303880388145841c0e403030880c0071260395411503c151000e17101d107a62888820404060b0042c0b03120100c0c011001401c4c0c103011071074000c00c3c45a0656045010762000c202181c00101c0d002406007a859004190428850f203454612032001001e00ca0400040c0c940c40c04110a10710324003c1c1754801d50444036001c00c5559468041d0007a502c14107040380c45101c2d10525501055051001c0c1d2540401000030350741d6040c040d1511890544081c050800552030001c08000315907030b0040940041c901d906005140c5c05072048443c0c205500d41e0861 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 60471657 1250 60470407 60470437
    0x16021003151e050415050603070c0602070f030e010833060304060b09010f0303050702010e0111060901020c010f1503020d020a090c0513090203190506030102070c1409010611030f0304030302 83
    0x8a42045001505040402c00142030594580e44004010076140060038120280348180c41c144103074200b8400641e4000402d00b010512400c05a441e0000c030781c040681034481d50002405602015880040d92252040c00d00c0e01070941d041c01900c8115050520503140c0742c000c100d4801c06a00d0003003030080d0910304001841d1f942c492520b030070501c02030202c1491003440303000b0100001c01d100700c0130100e41c0301356a007650321300c0c0c18050140d0066890851541c2000d041c40750044610307408603800c006440c132401c52a4009a21a5a1107040a094814030a5548401810603800100d0308000103940c0044a0b0126202c00c428000c500224013600016000043d16500b4405c428022981040c02000300203241c610041100b030740c135a1303258124003066070103003484800c1d000d07602c80503002c40d080350740c1183c0e00500040c0f0b0700c807540d51031401c0a04103034008822000c030101200220b283c8a10315500401d5541006144020810082512072146600b400c10030b04001c0041414980b00c0d80c15030f1442070804a20f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 60472907 1250 60471657 60471659
    0xf010b0c070302180114030708070e0c0403020d0309030b070912060209180702010c0e0d08031302040b0d060f060e070f030504150507230c0a24090b0901060603021602100315 76
    0x1000c80302c0034046d10f0909410b01080d500c82d0700b00014454111802540503000c1c81c1c0c02c00f90400315208010340a0a141030040c0000300141c0e940e1401c50f400d00384079440e803180b0a4910b151040800100030061003d109205c03000b0020500a017014590b003a6000d50b00698601d065800201c540e42132913541d8441c18020340c00c0101258055001b01070400c180c5d100c0d1103180c0300080800450403011781e0000e010f54420f0001c075140085102424100300c3c402000411007400f41008120510b03c411800d4490315103400b010340d81e50f0844d1156602506040e10303440400c3c900001d000d040c15030020100d80070103503602d0014041c4071500310307103050784200b4420501075403e0040d001080100510740c0611148601076400030254112400c552107a85c0001c003506014055455007407004030394540c0c0e80341010002c4611485a4040e2007a403680c50b1041010b100c250401844250842d00c0d40d80082040c11b10400030880406404044400a1079044452840b0120400c1c011009860760940b12039140d641240 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 60474157 1250 60472907 60472939
    0x30609050a031128050a05030d0b011d0a030b0403050f0a03020909070c0210050705070b0d23060d0609050309090114040f050105060f0c1603030201020d0606080f010b0c070302 77
    0x804001c454081d95a15a8031031451004640780d842c1440c0300602035000d00c00d02018050f01c44441040719005609403074445940d038960a00350ba01486c0b0320300c0010f035901c003284202e680004189a5031240384e403440200d081c010004c5041943c0b10300010f803e01322610006801c01d8131031000c0700c0c1211051040c20362203c05503034001c0c01075040145010f1182031008006041d052181900f00021a001000182450401030040c3c03482c0d84140c60a880901410740041a038a41e080000c061610070450300240d5251410041070220400082181c0d13900340c00c105000c12a602c600860380e610b500b1050026031300b406443c2c0316141d841a640c4845e046030609000003020070000304100c01c40101920144140b203900e102ca4000c4480034025203900c030b0350610411103181d44240240c00a002c1d100c003101c1815281d116500c80c510090361003100103039000074030b030916803149010302c0f0300070600390402c000c890528181c0701e01400c005000358012101301142d281c5c0d244a0030880d920007540c02405001402d04100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 60475407 1250 60474157 60474163
    0x403060b010305010b030906010e131e020f030706050a1206080609060105010e030a1a0705040509010b0307120608100b0604051518010c031d01020724120203100501110703060905 78
    0x118001d01203498a030000852140c11030460340b0034034624024201580c03e0502e60301802e480940311480400740d40c0c141200054660720200302807020001d1b8001d40051510401400c1f40c134907000103001c1d030098502001130a4102041d00d25440c030398202000c24407020303100308000305500d51082405104901c00d100004c00c020403c54141e40c2e081e81c0e03c2c500308010b142450350b1081d00400081a000304511070b40c01e40100c0c0c40d0f80c150000d5603450032600d040d9442c40003c0d0151000c2cac005600100703002040c005056000440f80030560504031081c04024600040c00752a019050320b1030481603100c1182d44140d03a1038070100e5020b00001007400c0c1d42614480d12039140c0c1e40000c404107285e03502400443d82c03d5030107200100328050341603860b101080d000c066503007011100c201100c0d040d8800d0800100712a510701d8102c8200900c40c01140200c00c01e0210010400c060040c450030b030082c410001d0103800450320707400400750344081c205054000d0b0039481162414540398000b400940c03901000004011003c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 60476657 1250 60475407 60475421
    0x1a0702062a0102160204150806040b010e0601020601030b010302091306020406090f081506060c010f0c0f0206060f0303030705070302070803040303050405030601271d0f0102030901110403021023040306 88
    0x1030350801a907401400180c00c0303115030f030b000743c10509806034a40d00502e0680c01040b07854074140301d22182c060fa581c0146103081000c2d40c0840310b80c5084801800070703000d00180300c0d90040c0700b440200a2940745803a00e00da8401c040c00b010717024000e914001454014440340843c051076003c0000c543c0c89542d183e004001c41035034000c0c4121206103140018030751800003580740c42e40c0051400503685440388020003807135922051004049540702c261140241415100b4000802d01c80d84602c0361b01030005900900303100d03000b440e8611031580484c0c1c2d54421f0720f000003602c0d40300d02142089650b40d0010b0405a28191040d44004040e10001402000305640080a0400c698054048400c1030b601e584081c000d138501000c0f14590800258801030500d131441e040043d441c132000c9440820f11000046403130070b01c860180e2444260303400000b4030400200910031924080300c185001402c05041d0f40c00100442000b810310001c01120008400c0d641d03020520301407004001000d46a52035a0740e1030034001601395 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 60477907 1250 60476657 60476707
    0x60f0902030a03030b0a0803070b0703050711010603120e040e250e040c090507110303071404030506070905030607261506190810061e0e0a09020c251a070206 69
    0x806c00001000306d00002510308042e4040035414166840103000c40c01010020301c15070400c4450400d020409400384500c0c00514044c40700344200300013444000c0c1030040051000b81c0101c0c41c1c464500342c41350000c1603841c0800d039090120305d055005810720780451000c680014a1044c450340503c1b0030443e401741e419084800505090240c4e641c0c1aa060b01c400d0018814007119400030800a48018841c0b2450214240e807034800d00c0c00d050b2240c41e40c03450312030708884c00d030003013030208005000c9890708102e01c0354000300c24a00a000710a58854032030702460180522408981d88102141c281c8142c26082c1c0044540540351076100c00905d00d003c00b4204c041c0315440c003c00e00d0b441c0400c0390310864126000954400d91200d0940c006140034000001199200301801c104071607002c09580d41e5031000380300080004070b1002d40c45070040302d580c0f030030184102007903070b08502c1d105c034640c0d41c1c01c0100c00c00400310744040920101a1502d0080c415040c42100300080d03000000040800d0304c0c8016540140716020 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 60479157 1250 60477907 60477919
    0x21504060e1e010801060c03200609010e03030702070b070215120412031b1206081c1803170f090d0609030f0e01230c01060b040806070e0904060f0902030a03030b 71
    0x2240590810072035003900c4a20f80010b50020040c4109401041050009446031401c100080303c0040036a004020841d40c6e401c07103801c0b40051040c00d10007402488501120800910300c1d500380508069038860340791003074541b0b1032404640c0800395603c15a603000402806001c43d9541d00000501003600c140447e0215407883c0090703a283c0702180b05e4458020000303901200000b101c04500d0054817002030315200c13040031640358000800ca0074018840c01044a000c2e50380d0321b51005143c10054007074071880c007540510b04945501080403903e200b504c0106030015198072640c0d001c035000007a40510a0140d042d40020743c1034608003c1200650000340341601a0783e6911640c1441c0c035088810384c500a65036400101a0351340600c1c20301014001e401e0f40007002554a281c0510111140c0c203403009540b002054003030100e81040355000500180380d000706075242c8030900119000c00512456005400038041c01c2c0c0c0c9001400c1072100d10340c481c070748464004040b24a4400540740c0240505582600d40703008031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 60480407 1250 60479157 60479179
    0x12150905040b0c04030308070507050316030503060102010c05190302160605070509130903020a110301230702070602120d02030a0603060e011a040c0c060e031201060302090a1403060f04021504060e 86
    0x643c0c403400361030580760315640d89540340c0c4801404540a0700022010b6515010800801070b2149090740e503200464480d17154540c607890f01000180c210740c02d0150b075a06005081001c85005000e6a0380200c550f8200e00b0016103840c2981d203401c105901020004000c1e40c6400305001005070490040c020328681207030030314031110306038846c0c0050751101c44c0001c016a00612508000404044120300c9891019000240c0448902e660405e007508903d000e0381d1141941c0c0074000140d5060224901415071800107004032055001c0c0080b01d441010005607440740c1c0400802c805820642200000316013181c4184103602d94525010700a100030520300030b80700d00c0c0d6000300c0941e003040d0054092881c400e840d40a811502c60319440302410789820300b2131450104115500341c0d9010b10301082c4c0680782c1a500140c82d98140c909000400590f500408984400c1100703201459400040c100e6108200c82044c0156407914804280c45050410407030070740920108000c40d049601c409031041c000401c5034031003011 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 60481657 1250 60480407 60480421
    0xf080f040e010f050402160f051903050702030607030e030406050a02010219030c03050703050606070f08040302090709060905030a20010309060f0b1302030103050c060a02030f0304060b0f0315060112150905040b 92
    0x1f80700b240c1c0d00c000088141010040401d0b100d50b01d05880074000c1085e01c03582000300600e0001c0f001c10701f0049010505c0411440c055040801416910010380d0a08000c20010090010350380d01a40c4900010040c000842c0020b1610030f4054880c200e50305106403140d402034510280c0a0007078046a64002031900c0b00040c07844c0d00c6401202c0c011180904424904400e0b40c480501c00c889026050391080307001c1000100607120801114840c0c20169a100a010305180c0c005001000303550100c2d1280e400510303c880865444100e00021510300306600b0381210001c80182c1c0501000d080c050304041c6458031546d668070998101c20500b02c01140d841482d501d4030b8006000b24042808080c0460b8072501c84070711075080c0600101450807050048031300703111032a031030080700364400c90b070450300c2c1c5884000c80d101074180b0840c400c0f00b444040b0060416031005a0b4049100d07280100140d040020082e40c0c0380b100c034810703400090003120120b95140b4454035500020007a040c05d1f502107510062040c005404 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 60482907 1250 60481657 60481661
    0x30313060219082d0121020303030109060e0a02070201050a05030601030b0d0521070512030606070f060b010f0503070f081b0c070608060604080303150609030f07090b0607050601030f080f040e010f0504 88
    0x6441c1c000980704c8501d9090049820483d4200c065284910b489201c041016030342c100040c50017028031440104407207040c00f00e101000f00300500700b410654014401000141e0b0020180ca01080140c80c1241e180da17944001200500014009250460180c0000c101800400300d10040e04005404078030b1001d02092146100c1c07442071100c00350682e00300c602c1c20140c00301c4942c0150f800000050605040204035211103d03001021001160b469503035000030661549c000e4400c101109042c184141986800d08002e0000400c0c80058003c001c0780600080214041400e0b10b110800c03821f8507261144918003840340e88940034019080455540340c0054403600d020411501518a008040d5042d6103800840d0562898814038599201401b80500790198808000c045200500c1030002c20b9164a40a00201110302c4224440d010301000c01025011070000214213044940c00800f0542980980c10004458025602c19150340329001900103540c0e00000c000300d0581d1807484041100950314420401 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 60484157 1250 60482907 60482971
    0x702060d0e160519090f0e0d090305070b040303120b01030609020703020606031c0c1704051302030703050f010f06080a2403030905031f020c0708010203090a03090806040503031306021908 82
    0x13240000c2000280b280c1c102c0e40d0441e0704664003944000c140b2182d070390509401c0880080740f00c000500c49420030030900008008003401004042181d0389402e0840d1401046211044103400c10340d0345445000d80c5991181d4031042c014410040e0464407940276207402519a0402e8905034428801c0d00404408041506c104261200040e25030b0f241078003082da40d10480b20341741c14040c1183c01c02840005103d456a14000c2802c02d51240700681e245044a0302a044803005031041c0e081420020050102d401d03000304540a49159041a03911503a42800c01d81c040c189440001612504900a00d8005024240d40b18156403183d11814460f90303c4805141e0b850b0702640142d044040030702c903034004844e244c2e40280800c00c10b01c41a61100c07521280300900703aa1040c1d440c80303000d41c86506400d080c1544900054054199940944014103190f00e5042d40c3c0d000190a4001c50415201400100541c6034102d440b102d280d41120820403540180140113244129100b85884a5032805094604003074007000c5c0b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 60485407 1250 60484157 60484189
    0x90c030c0f0509060a050d120306030b07090305010507030e030a0c02040605041503050d0305090d0c02130509030408101107080a170f0406050606090109060e040f1e0b030f030904020702060d0e1605 86
    0x348451f600d520345490b1070404441c040700303140d0345032800300108105084452052001c1d45a00b03e6151943c03070400d086840c014105410145050a065868100801142c0070f01c01c0b64030304401c030344590707000040042103998001d50380b080c0342c00051f40200790b030044000122030040c4260307421100e0038202681610130441d01c040b0302e500300d9400c0c801024000d90030002800c5c0003030700c046c080d071540400c0d140c102c1d14181c41c540d49a43c0b01040401400354200f0ac004500300d403904083c00310303a1401f44035011901554500900024000c9601009244a501c5d03404641c1c00c090304000d194248803003040d001d0030301514155207413418400010a50300b041800c0f1030348e03600b06a4921401c14134024040320318203401c01c44140d2090321015000b100c821140150142e04901004d0000302c8600314a0040884454000c00e1b402500512007031224103501000381ea20281007a540544d64514601c00104240728038044200b00516020344840005000560201d11603518220203598540b207030704010307800c13409403011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 60486657 1250 60485407 60485419
    0xc100801060905040527060f070903020901170319030507020d0302070f0b0a0b2e1106190f050403030b0f0f030c01031802040504080703080a0506010c0204090c030c0f0509060a05 78
    0x4001c50b04007071707000603406403c85c10300c16140d00007004181c2c06203900169289056024000748501b002c001c596440d0450560b08052403031a1441c1d01094440c001442120301030002c58190070407409040c01210a0080703110a03050031444d0500016000708800e940040061182170480c10100b4080c1c0f00b1030b500700da000003009005125551760b21505030401043d0080c56501c0d02c00c01c06003600e4624840240500500b22302d0b489600b000e082003289001d03112490108042d102c044101100003143c1c4a40041000c0380240c1c400400c42c44040c00b401c040c202d081c000915040400041c164598001064200c0c200c4080c540104210100180e2054609140b54503800c96000030005601990184c0403006c4108040d20081c019038000508945049605507501000010720604241c0c4c840c400c298080c8000b1740404c26801c0410008210703181c500002030050f980c42601c1c40c2440707460000180210741c08052002c0003600c41c9400c01184089102e441c2c000d1350460040390241c64502c0111041e60400f80130 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 60487907 1250 60486657 60486659
    0xc172701030203040854030c0d020d0f020d06060608060d0312020a03060f0603140903030106081303050d061502120405030628060803091c0b0106050a09080307050c1008010609 77
    0x80c41400e080500803014082c2030940341100c00304150101d0191b900000d03104281d000403086040200c42445030725210307812010b0310100595034a2003103e0721540658141140034820b1800d2207186007001e4003c0d6000c280307490722600300106a00b00c1000e0b100e40c0d60340d540b1651a0780d02032041c0c0c1c8000120050101c1d060700790354015180281d025000408161401107040c40c0c0d10708240c910340c0301c9a0810310000392103418070341185024412a03600326400000441c9550301d0140f0007000800007030014400908120076103000d240c480d400392055060850301c00c000c61952a5060b071200309840202c400503003d9521b22001c00142c2005a0301203800180c0034180c0c507078440101c001402210b0b01c0c0d80724440d040340304071240a01301d0310420028040b0b003002180d5416102040014a071040d07183c03520074601010382d02001811100080d03044505a040a42c0c681d07116030b0007918140e8030b03600026020b210108560080c44400034000c220b151054075a2103910f03011013021940c0c03007001d00a1001081003028 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 60489157 1250 60487907 60487927
    0x513111c0303050621010203040219031110030e01020d0608070605070515070201062115021602010c020609030a08040906060806031c020a08030123011e0c1727010302030408 76
    0x11a50040000b825000807520308110f03040101c0442031740031101da42c0030041000714181400d104030300c0c0c94186030b0103c8007840c550300c50003500c00c0902054004c00c0003818402d0114003d401183c5100078101c02035444070030303002c1580010400c03445104070611a9101c0040c24034081c4080b9810103400c000a03102181402503001c00d903040180c001c074115941d401d00091290748000b0102510354910103c0740001009003420340420400c081982840740c410410410351107012894400030b07640c2828040c40110003800001c2c5103009910082c0c1e014024141803e08101814000700183d0341d805030100903107503c580f0112103001c03080710350030b4160340000c04140b4030422030b0049845650240c4111000c0f41c0059403646e010350000e038450380b2500400003104c00e0005281d143e00007106804c1c60a288090806401484117950f00e000100034492250009000d0000c140d00b0258120a585013882d59508210403446002417010000c1640d140c44030144032940d0f101b4002c5034003842e080074801e410601910 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 60490407 1250 60489157 60489161
    0x1306081e0103030215011a09010c0c0e010605070213050601020c0607080708041512050702030a1b050109030203070b0a0c140d020c0604050c010311030c160f060513111c0303 76
    0x1408981100c1506003100e003440c00d821800034041d40c0f0070b501800000c03402c2c410107070b18541c0c1a04440802c3c400c240040c1e210a040324141c8854000c2460600c586100310f00f00511558207940024105035450302c004038030740d90050700521501d4402d550000018100310562411100240c68141c01604580c14041c1a4608400a454814001c0c5035052402040740e41d9880198480c0e8000b00c0700d080e06440c3e4942d140d4005503200008806640188124502204002d4891103036402000922070007550001c014411603500c9025180e100000b00544400c03800c000e5034a401210301210071140f100001703001d0b158140146180711440d6218000c554442100321003103a0051101544520703801d016440441904000d09409179004001a0246100450004094400c15031080c46101c00c10404c2c0241000c044048680c84503104403d01e4240f48a407038500300c0640c0c80304000c0c1010303040100780a04040065882090304e4071480e08081d41d0300501042c000c81c0344e0300d40c905c000c101d007a1442040109002e5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 60491657 1250 60490407 60490411
    0x1a0909030c150601080604020304031220030f010306060b04080706051c05040308010503060a060f09090203070b04090e0105010510020d03090c0f030b0a1401030503070f021302071103070b130608 85
    0x112054a0a04034508545440c103a441d03034828185082c03290921102e540c001c00800c0c0c00100c00c0d20150701d14a8a51009003450404801d1540240d581d10b41c00d40070401d004080c6030f1b090000c400200c4e56405c10101e0440000c0080c0400c0c0d401c2450554000b0b100c00f0f004040740c003242c5003480a8003010345454000c0e125500711100180300e040054503180140d5074507200c0c081c81184203071502c0c081941070405142c03404400500c15400f1500e007000c140200121401b05404454000e003011990000610102c0d0400c1042c1d4005102c0c82030204000c900301500b40c0260440c191024020400c9aa82d01c0410002c4c20440180b1405170300b2548040c00701e10f200b03030400781215000d8074041000343d0b512910180c800b100c41d48240c81c9680d42009014503103140d401441c948004004d0204400e5045807241c0c2d0b202c1c820724a009140f4007103164244219140c4401092140b4110349045403541c8aa040002102e00540c450f04c2c468015880d02091101640f01a00d07c03210360110080046070410300192010100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 60492907 1250 60491657 60491671
    0x50417030d0605180f15120f010b04061a0306031e060a0f15030305070c0506040b070c050a030b06010c050709020d020703021015050d02030f01090305070308011a0a120207050f06060109091a09 84
    0x14130078401c50f620b6400c200d87c0302610300001000c1d4400308480450845001041003442141800410001c05c000b00c82c002e9410304040d000542d40391a5200081d2825842d070000c030b40c0441c105201c481000c100429607521803128100244148190b00d0602411180030741131401c069115040140b01092140c40036102e0b01e4401c0003090403003900d078000146103800580c4606030440b000502c0c1c0003085440c00718a0010601564162603280c215503c0720803408009002e1410403054031400c100740003080103100001d04d6088021580d8108121101000e50701400096001d8400c906542101429074820812118000b01c40c500070a82800200304104607030310820303681803190580da0305014100380308003441c040c070940b11381c3d5848881d8034020341410300580c048400107000043c1d0ae44101800f1003102c02740d650038071309500e095001c1218030000b80503800001e80319104502d18030003d00030008000340a00f0782600c503104159603400c40c90b01900c201c2d9400d082110859040e003c954140708041d5608106 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 60494157 1250 60492907 60492931
    0x10060602150c2508130902090a080703080906030c0706060803040e070f020703150f020f0706060e010e0703230a1401120503070f030c0b160e0906090f07050417030d0605180f 76
    0x141080e0310b46500710707540c010000140c1c4c0080c600d1001c2c0f9048927500d00030512200a4032030b013803660700c1340b201c6405100545c50140328000300065043d00a90101d40d101035029004000c501d0311040d00caa40c90300180900d202240ba0390010440c19805004d2440c000c001d03d9000b0455541103503209130711481c4a210000c41c4a03101e40c01c03d02d140010340040c0001010045c4403035140c0c480750a20000341d91040c0d0091203042010801404205525548154000a0313410042208030810701c1a007800401441c410b200c5110040130b011402910f900704100c04694214108100c3e40c1b2800407018045824074014001d074801c00110001807011606230904034002d087ca400540c60544820340080001c454103104000078250031503520750030a00c50091440290b40140d1700d0301d0400d01240c0515400b6280d254440305030000114018880c800b1140900311403c1e04060808180004507a00d410440702c0c07145650400c080800c0394200b15030801c51003564614020050344601c0000600c40c20090100c150102c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 60495407 1250 60494157 60494167
    0x605030d11160e0603190201090e1308030f0601021b012c03060c19020c0a050603060f060c0a0201030614090f0a060504060e040b070c0b01050f010210060602150c2508 73
    0x8544981010081c0710343c3c081d0040e00e1420104050a01c0c0e11403101400403420782c00eaa6003d030742d22200c03400c00e862140b00f840727401c0d031141200210740540d1088024644440001080a600a000c0390180109020b8084440100382e0340144c9480045841c13400d4005601000307846400b000c903411409034220300c0d00c1220020310356100464140b40044401c6160f146002179100c044121040710541102c84c640b0281400345505000070b509004103106091040e0000306c0410329917501c044c45601140380041c070039940c6801080c0c02607141c02c200f02d82a40401e00d0180d0008400996242030001140010006811039890040780f601c1c400c006020a03141c556908ea012031217448a2280201400c0403007040d04080c5070502d020929a08024081710410140e098450f00103030b0741507091419120f045070704000161884c0f004074904940034a5400c105800c06100041d82500800c0c1402410301c40026002c0640e1400c0582000d482142e554030f40d0902040001c0e40142c0c51078114526003031052002c00c0c500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 60496657 1250 60495407 60495433
    0x40305060f01170606010504050607050115030b0a0c0206040b0703020a1701031b0602010b0d0236010609060c1a060105040305010212100503011103010905250306180605030d11 77
    0x2202085841c098610708010050140882c000580b401c5194144024007251134030f8030008209004034403820707008a03c0850407104200f020b41012508030380480b122202c9036070701d06000c640450250707030254003185010000c80c0e91030b00c046800d62207190004061b01c50741d00c41d0700b422802903102d001900c00f000390521100d080c10034002001030095008411088400d00d031102c03040040c501c41c0e800030095a24005000036903444010401c0d8007590125100c41042040c4044440d5084020354040f1181d480415580078000350340c81344034140d40080d5200c9001301c2c0c80300c4040e87e40d0860ba00c40500000c0d4410211500510403414070303544644103140c41070600340d0b280d40d8542642c11040d0a00745c080c042c0c108002c9070800c0b1180120042004030028030209941c983c201d0010b11041c010203407074a031910001040e46041250038880e08080d4a40e4801c0091202c8004004100c1c40c001c0c02d00444034400020940c06184c0105016140c00801500340743c20f000000365450031070201d2042c01c9008011600140d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 60497907 1250 60496657 60496663
    0xa0b15090a020a17060f0d05030906040b0706050606090d06020a02030403080c0109050d1e050906041e14010806150d15081e060f07080a09050303070c0b06030a0206090411040305 78
    0x907441040d00540c8030070b0248005851650704003460714000b07156104024140e52001c8a5040b0601c0580b0107028115840c00c01c1810f42c4920034103260030000009000900102e404020819140241c908210a840b100100300003486441c10740d07170b84055140500740103e0101c0e1300501040c41e140c01280c3c03038a070340ca1341d5407002c54001728410701d12659a02e900c030341800400c5c410012000700c0c620703204003010100361406a007030002070344030410000082200203494440c101164003070007183c0480c1ca101180f601ca807108281d55401141401c4110050b03542c0103501448800d4001c1700000e00d01380b070040c48640e82e907040d038218400c5124555114079900982d000d85000300d1014000c02e1025164800404102004441d1010b8650740c0940c0000100310351b00e13002984168100d046850895580e407a0207030032402600d20303004086c041c0c2c00700009004070035420150030041e1a1140b59128900e0f6180400c05444902c01311001c0c2d0418010410904145080d500c00312a465142c802a4241a1a82c86070383c5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 60499157 1250 60497907 60497911
    0x30f0e1005040e06030105160e04060e09010518010209010903120c0204060f080f0303040206070f0c0b0408030406080718180e06340903030804080408030a0e01090602030c0a0b1509 79
    0x4944002010312000c181456204c0e40071000750f000b800a803c0560403103500e4a040c00300782041010701515070b07580303954030380100c8002c00c4d4816900b80340d8140008024001d000a9544480050390700d12106803805040c02920590390058454440283c656101c1054101e00c5107a800c0c10428420b00c5a00141d80394802d00e805032a0f80c41000400d00c0c07d0414081c90320015480c0601c4aa01c00d004020059444804550241c2e074821002000d243c0c8070b190400c0c101d42d42d9000ba0200034008200030030a01c8000002d0300c1140d409641e50355040c0c1700c2c200e05440d180351008282d21145888807040c000030010540c488644c1484120008940d1010511389050403010394502c0080c1000c0c0840f882084102ca042140307114ad6141090406030124030050500b54451200a00744080c1d00d0001d0280030035001070701c1c01001054182c907036502007000000d00c003245100b40107012032603203103011401038400401c2d500e5811403000200300025950701d501401d440020000560641050b88141e256200c4100c000c1c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 60500407 1250 60499157 60499189
    0x220c15020a05060606251110030509010c082502070510020303010305010b0a0b03040f080f0408150c04061b05030d060605030f130f0f060e060c04031704080a030f0e 72
    0x1081c0c45409290690602c1c0b4090600b900c10601802940c070700281d054108080c0c205910840d902440140c600039031721400d5104265482803200d50702c4030b00140c040d00118440c104000c001c1100d52110301040e114664140d4650a00d00260508090313030b8034046d416491000c40900407104000c2c0c1d55000211001c01c0131000d00c1c0140c00100c0100100403090051840c120411144112aa030038000b049400b400000d00c040c1030000100003030f105000e14003040790224017400764900e54a40c0c8503502d6076074034204414038483c10500c090000b40c402462a0984060b11400d0380e411003a03d48460014414201400050341c0e2400b08206040084c4110311071070300100507070345030340d5164541028221102c4000a01c4605641b0f80d14032140b0004421310000148644d10072030316200396405041c02130050a00b0794500f03801e80f04070303c03e0040c284580c00c05001220b2150b2003c080c1048500560052030040f44503045080c0c0c440c00b524000a4000c20613190050f6140c505017421407400b0340081d10640c0500d10384 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 60501657 1250 60500407 60500413
    0x1a031006060305060301020c120711090c0a080609060a05010e03150106090501020d140f161b15020a0c0506090102030c0303010f180207020a091a0406030605070f0206220c1502 77
    0x40207520703050300500e0ba2241c0114021410700300240b130300a40741c0c0701d000c42c0d01e045000005150b80c104100441010201800500b10016a19007001c14007200ea1100c0382a0380490f4011002401501c0d14200c19449140c000c0c01303200314a45030038010340d5000d001c0840258940100c030b4440c00b0309914180b0701802459965210070213240344c2000603050000c410050010481031001030f01d154007200c8112101c0035000d503145642c468404408003c80407443d03c00030a002d01c0001c1503001c010010109000b6110b05480da050303980110801607135502203a9100a0107415205410401450410b000d09002d010600580e890000301b002118215403090300900380040b40a2020301c65002480700044c5040d10600d400c40c030707140950700020380140040c81018010307038541021200c061a01c0c081001d50700406441032082c1c07030712032401c0782c040e00741188c2000029040c62416114144001805c3c0d00641c500c00100045007514001c00401c01600c0d0815180742000c94000030f600303a03070425800c410005540c06 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 60502907 1250 60501657 60501659
    0x20f1b0405010b0c0d081005060c0c0118081f0b090405060f070c0305090d0201051303030c02040b04050420010302130b190f020c0103020904090b0103080c060f01060f031a031006 78
    0x100001c650040e00220301c0c0032000e205294240100090500d110902420119a10703039440300a05a003141d107800041e0488404200d4070362000c0c0029400c000d0900036268034142000001040780142d07144d00c154461503201c064886441c41c1d60b01d410f030800d40b0340e40d00f011422080510202e40d01000c00c4d41e04030b4041d0710110030082456007040c01690003440d90314100c16098a280c070010700600458250501c52072144000404680c010002c4680070306092280c8000d03581e42c0d0402400c40c4480e00400d0f0300031800c10301c1000240c0303064840d0714880d90703008000c580035490a0071325880c110818170801c3c2c107041d400c222044005540b4050000246031801c0b84541c2c0b404d4012002494100d5038034003001f40700c0704580c03041905030085075544d1203080a01c0d0060701c0c2c00d0007200190150500c07060180045515400200034000c0740802884c2c0c2c03100210440300c4a071540800f1075950701e800d12844000462030940031840701e1180d00030700c0e07500810203003103503601c2c90050010b401c0c0303100204034034051562410 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 60504157 1250 60502907 60502909
    0x4021908030c01110901090e06121209030613030903120504030503070c080d0c0506010b07030c0c0e010815010e0a09080c01140a0c1b35040e0901090c15020f1b 70
    0x1d13001da05484150910306125090002901c07901e028004c40010304180300c0099134a0f00c071100f440e45003001c11012140140903403e10450503034071040c10fa070f010380203a800180c1d50310302c011b0b241c9081c42e50641d684210546180c45e07081e6444418400f01041140c104000804a00104017404010f40582c641d941c2c0d00f8903009035185002800f00001c0d06010b10600c1680108001099941c112a1100c81041e514412071504541010040c9001494030704840c00c08203000b00302c0420f0b2816138003414100c0d03c2801800311442c5c280d910910410001f1445600000c2c691101904030803039062040f403100d030810321868140c0e820f42e43c074a541d2021168ac1002086521007643c0100035410708641080c910340402ca101c180c031700e204000e0015121301e640d0407552641500700c0204e04900352400614501300e1071144840030072030b4080c1c401c8040310b03c8040d020030003402041c425103000301c0d84540b1512985240a481441824540c40624203500070406821a18001402902148d5440250780c2c0c40015601c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 60505407 1250 60504157 60504161
    0x201020a03051302100302030a090213150f0b0306010c020a050907020a02010e060a050f131706040204060f0b1b030f1809130b0c13030212160501110309060304021908030c01 76
    0x80c0f420410210b500321082c05a00d5840ba0060210b407603240141e5a82e40300d01e1090058081000025040010810b008a809240b584000045406400051100e80d074501107a0342081042c0503402e400786041002c00d41e0356000d10024088288043d02c013806482e076504c005080030504032130030340c05600103220303100456174020440400d8000481d0000c2c1041e8101800034424040c150762030010b000000349000b00c10440d481e800c00144815505141c10101c41794a060b120002500c0481c060f9081140106140105424507026594007031042c41c2019528a4544000c488011080c0c0d5203000400c10f20102c03591810080c0044520420300000703440b80003051099445008240301400911092181c0010b1000e00c492034208140072078058507081d005240419260b010390000b5807000000c42800c00040c00421012000c01c001030070303400110341d42d80043d01c4a00c030b2802070400301e8204100780295450540041c5422a0001d800b0080c04d0004424181005600b50081c192541c0013045030300c00c00c0e00074 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 60506657 1250 60505407 60505411
    0x51018060504060507030c0f02061b01150e0c0d06030618050c0907050a0503090f06010e061c020102071205030c03040308070c0801060b12040203100f050106030b061c050c13060201020a0305 83
    0x1500c1c19502e440e00d0700700c0040c01c074000d00200601b000508034200e82404402c00000c5287d079001410650f650801c80c283d07070144501c2404051007942000110444d107a1a240c440e004c0b91501040030031305a40b52000c2c82442c0d2300041e07501d190187c3d509c50200100704a0710075030f411190f00068014031a200e074223040d440d000d82c1c0c4890360700c112101802c116001c0c0d40f02d015500c9000b07071810705c00c0c0c50361203001e0580e0800c19500310b81d03002c0f48605000080d41302e08030f95125000740000c1d00e0446030b600c2c2c0180c42d29100d000c6842c019026074810001040210403410703411503501e000f441a6400c2041e9000003604503402079006450844000c1a007009010968501100600744880204062460b10428403d5401003254031001450842c0001d81076440c10b116501c46851040030400501301c0d11450113005100c00e0140348000392406900450a0504404071007501d1a4191900001c4500d001407070040e1000401c0a0203110040c0042d44040d04540c2854010303000c680c00258441048840c010111080 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 60507907 1250 60506657 60506669
    0x916050409150b0d0b090705011103070209150406051206070807080121020a0b0a030e0d03021e03100806040c0303080f04030e01030b2b020f1008070c020a051018 71
    0x203414001070000344140680e00b20500070750000309071001c070307500042d0b06032400c048003030211309503030301003114003000803e070308068036000d89540710518240e2040907078074014020000d401200b03010110b10301c1180c00d0300340e4103011001040800c0c4552558089010103c030b91028182e00d9001500740300c0500d030000305c1c440d485506441c00446540c90f007804c40c00700c80001c190405109002192a100399200e00054001824070700044680d10907010b030f0010010403454002c08054021728500d5603000d4480e000f00d401c881e100303c007c2c4e094122410045401580054100e0701c2880d0b1246000072120424401c41e48681c0c02250030400880c03540c2409001c0c3c180003885581400c46000401001941205005100120a181c0051100081004079075078500b4205011038072018800300f0f4007004401c800b0441424400d541d0601d00035010014000550301084486001c204184001106d003886500000392040c0000d107651039295992010416a4040300c40070381c0040c0c038500e082d00c80044100909401411 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 60509157 1250 60507907 60507911
    0x151207080616021b0118060c14010213170a0609030215060306010f270e07031a070801050d060209040c050307262e0b09032808030403031409160504 65
    0x140b940300094030b03002405076480c0820301c2540e083c4416481045c0804407080c0b14403040b01c01c162101c0019061103a18001250760f06c3c81194240410036060003501c0c01040034203629000241080c03d401c0000b200401c580f104c0f48628640c1c0300203c0e086000301e0003d18025005412003005550b001e1802450042c80f2501991110004200e80e1000120007001c0b140030103102c100040079404004c8550458290607040341d41810b0003080e45050200760034044a00c245074100052000e1030181c004200c0446a98001c5090a40104a17500b441010f480c41d252050400619220000c40010200c0e2410808200050f0010003040001c4c1d0300722a1a0004070712a20b90001e032003104420f00380c0000c000a101d07481d56002a003070070903010010303940e6002c4603c0c886895025545c44030180d00440d001607006034441d01c1058224241000764120b00f460000c1195008034612a9589616155501c048c1c01101016612044154200c034100501402419880040d0032003200200c8403202c540000d0704078501c918 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 60510407 1250 60509157 60509191
    0x10b070c090209010e010f2003031009060b03060d0206040306020304030c020f030a020f010318020303032d0112062c01051501030b0d120e0a03030e010f0903020f01081512070806 78
    0x103a000040c5c218018401d10f00b00d2040c4410b18402c03030303880502d40a40f050300d48840f1103044901ca004400b031880b4062010b069041c45039140e000e68140c03461403080411407041040030814038145820440811360000e41418940340e500e41d0381c20200c0c0e20844095001460362080f60045142c800c002a03c42c803000c500400c4c4a076066000201c0e01c00850070303000c5c1895955401c004009000101c40c0c00001e800909903912480d000244042844401e080741b48885100c1c4207400c0044110884141641d84205481c0104a0707213603201781c010074000200d401d403107525120380d1151406409041390f440640b1000800d02c0c0c18a52000c0c3c03180200c0c07810840c10b00d81003541400c015140c079406a00040d400041e481d420710702044042c0d80142250034207980101946c1c0003c0149170300806046441d413800c0c0e0758640426101c0e0302c215a812110f02000794882c2244c070b0392700307a507611650f905030300449400c00c880e04140d0200c00007190b2807451142d40c0c02c13580024000700a1003100388541984801204d4a400c00c813 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 60511657 1250 60510407 60510409
    0x616030506030318041104030302010f05060a03050601061d1f120204050105120411040207050f070b03071422060306030201020106091b140f0304030801050907020109080316031103010b070c090209 86
    0x30b008601c01c0c50907012400d02d1a643d10b64541e00305048109040800c11f5480e900d030b060003170103030080e107028000c41810705021690a00701340c9003a000300c83e0004050802a424050708480e29104450b2205d1003549002c3c00e1003466440ca0103c003035061451001c0204007100c813501820102d03240000d15039031441807004101e2a60013100300d038100040c9000d12413090791945410307103894144100468100344045030b004100800068a0650340301400200ea1303095640780d180c0c1d145480b085881c1000030f503032140130309204103051014101e4902d401c20894200e44141c0035440b01c119603039010400082e00c070b40c802c006658084c0f10706805403483d280140304105100d0600351a01c400801c0b55810032400411200404a0748401e58007050401ca6540c1c0d036a060600700204410700a005143c480c942050105070740340c1c0144500e01c070082d440b003103080c1140d0303400c244040c030380a0210403a024192648900e1404030119401180a01580f40380e0300d45440450520022048a0340c1001d1300c001d00c10000d034251 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 60512907 1250 60511657 60511663
    0x150f06080708010b180301060b07030e0316061d0f122404120809120706060317030403080a0506010c02040e06010602010c09080c09040609060513051c0c151409061603050603 76
    0x380c17415050762184d000c0d18101103401045141e005400c0d01c2c1001c140b02081540c05011130240c004102e00b203c507070340c81052103510301001032310400000c5411400003911220b1407002e205241c02d00100450700d403d246402191901d440700f842c201d2280c00c00d0341d9502c254003d000e41502b000d40f041c03540200324600303540c1307000079290b05040e01c1041c032030040c0c000381018100700004080d4040e011081c5840d600c461030207101a01507408125442c00c00034000c0d031100ac942e03800f601d12540d0142d035802c2c0581c0743e0740c05180041001a01450410a8482070f80000d40c5940c0210490381c421840180b059614000c8000d0840e1509500d01041000850081240c03640002c0c0310004c0d5142211001c0068440c0c4c90140020043c401b8014901401c00342040703005c100711002501410f00401c00d44080d54000e9582c0285910304410003c007080041140b10b011980407e400075252030b481400081400b10b5420307101c0844011241348a807035100b070080181010b80803802071800e20349401c0c140024101000003c1e1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 60514157 1250 60512907 60512917
    0x509060c010e12070c09020703080a1517101103011d060d060906090b06060306030703140a02091015050f03010608040c0f18061401020a020112150f06080708010b 71
    0x110844020801001401081d4051007a001e00700c0c088a40701403111a11030342581020005458104800e200001c0b0030500e40200c590040e815074901030b01e0b91b81d40305440001d00d41d400840240c019024404209180a0341e09612140020700050031445d007013001840076034895041440c0340c02d40c240b00401c0705034005509022130042c0c55a44018594900d4045a00c0e002c201c00041d004c0d5060407214030610510380e200c20501d078020303400c0c07060507900d51007803052501c41034031002d405511100c000c10104407044099130503081c2c02d4013070300c507106069000102d0680043c1e440082000042c038080204511408101601d00703c0e60400608040081030140c105000503c182000e02150900180402492224100c05411510083ca02d45521080403080d003541411421038079034a400c90100e10074100217120110400160b001340000c6c2c02a0b801114004808006c0602954550100310152928144400d0180840c0184d2007011460007000800c445000303410041032080103c0140642180002162 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 60515407 1250 60514157 60514159
    0x40b01021f090c0320010c03090603020f043b0919050c041a040c020307020603130f050a08070201031803020a0206090604031b09060f060806040f0b0301050f04060507030c0509 77
    0x7030111041400009441007020081c486200c3d0b650102c20880c4000380004900c1410900e2202809502c0c01900c2006604402070089000711070100703c828420f0f002003000d00c0054101904055549805043d10344c80318000001c840c4228003001c00010b6013035201145036010340340c0740307072036051600140c0d440b2020702c1105200440c10f14904000d00104025402c0700c600d0107403003006103203d80c12030101207101c048034803807045040100e10a0094400410b645416800030300c0075145803a09a40b043d806c49141a046404c44103100c00d0f900814806d0110003c12401456803d6075680c10380300040c11510510b9101c0104a540000c000c042039000030030703186444d410ba0703040741d54400600000e0403e010780c0e84020613548c400b0105081d5940b440ca001c01c00c0700d00000c0103000040e280d0b41200540312442c020800021019000a0301519140d000f80c0e17059100074400040500d09140030900b502d90413202011102840014041084064440d907a4040c0351407504020320040d0300b02c0104a403003542c0e041 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 60516657 1250 60515407 60515443
    0x702031309020a0309050a03110607090b04091505030a030206070906110c12010f020a0201090212062413090f020a090e03120c04081c1403070e0d0c0504020a030b0f040b0102 76
    0x400741c3c1d00a502021100e500030b001c80385098194038005002d9541c3c603013030081c240121800328003400e02410034030098410b81d1071001c0c201420550701d072004208190030a88041849480061140c905004007852a4060741c0900700c1447d1114025011000e158030450401a82ca406803264510114056140c043d00f2201406110010751030103025014401c08d00000360f10004445900342d40541c04040c12510941c0c103800103500303600e41183c50b49003c444000c0e55010030741c0900d4910700c1080410b04030f000c00034030082c040181000c14078110345518408a40c040c9804004d441989055001c200c001c1c041c0c144240b0045a100c203a0903105e018440450780c00d08203076000f0842050f007030000d441c003a004020864056280c95048242c0b5400b4403002d03440800c03d4102c80030b07040446441200d1023100d441c0c940f1200080444140461190260340c1942c85a10404001c01c45513242d00041400040c660380105403140204104a0105a02090304e0b20452426864680700d076004119042c1d2000d2030070315 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 60517907 1250 60516657 60516667
    0x32101270b1203090a0e07050316050c06100e06040603081c020705060c031b030405060103020f01050c0d0809011d060403051309020d090303050f0702250506040909020306070203130902 81
    0xc04400351105040d8141c0c40400c0e80520782103000c0c000301404070300f481260800c903250341e1000564038194041d02d5410002d081013000496194807030340700d10a020b2161800e10710701032650410500300103003601c000300c00e400c6001c1c04000c0104090340640d0080320441e0700b000842d00d140d0310446244101d42142c511070048900c0c0c8031a4850903070580b039416400505503111880c1200180c1c2c0f00b0740c002c9600d0b002e02c8403100c0c4004a40ba00c03100503244550760003001000e4907429502013128500d04401c0050420804005d48800701030144140001d2003c81d85890036241001035141c0c2c01c0d900c0443e1290002c480309017004c46000c2002074155081360709403c1007039a6002d40842c80101110f5604003c0c00d40c0d00004194010848980c85002d0b00c502941d010805610b030204500c030f004500b40d40d4040160700609a10340004039641c4c480c84203484080912201e19540c40210b1001d40141d0302103840c0725a688241003c0d42824040558042000d101646c038000646a0101d4802036070300440789040e6020035 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 60519157 1250 60517907 60517979
    0x604150c0807080114190b030402190b030a0b13180309090c0e09060a030503040e040204062403051512030301090e030f040612090c09020915030114060904110c032101 73
    0x80110100c620146d2003240c45074070307142c4044080d802683c0490045c0b0710643c01d180d004220350443c000381c0d016007950901d90f0b00d40082e254040c0c61a010000d50203429030425410508a600c01c00b0400141400c204c0b0202030b5504025021100c140e00231040203042c03103421082c070f6070320264058440004441241e11a241c076800b0036a0b40340280c20041880c4800200841c100da4240051441075108503018440242c69101d543e001e48444940d03103100404012210324514000e0f0441d82e800058801425001aa41e000107107079a40e00c1e4a5109a0b0b400000051103a64118040c108140010200852070302c082800381c901184201d00c12202080f412491200070038503207400c2903205c0d0340c00141c2040c0094231550104001c1d808040d00078415004201080e84140d465010741f41280c0c0550f00e140848810042401038652140301500e03072007903480000f071090b50038040282400e040f09400550711408165005080320000c2c1d030f40040d807074030500010051010680c1c2103810241142c2500004030344444 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 60520407 1250 60519157 60519169
    0xb030c1020070f0e0a05060d0215090414070302070311030c120a020106091a010219020f04110c030a0f170c04090e01020c0106060e030c04150b03090703050604150c0807080114 77
    0x24021400403c0707402400a0601e000b00129406042e8521081017180c0303944080003980c9a803000004d4210341b806111281d2410244060f00461034082d002080c1420750001090990504503402008294041144000e041e80000c2241c04051800004d51400e80300c40022980c0381201a41864401000115104618401c1d04688020b040948082c40584491420f05440440020520b801481141003800f83c01a507a40c2d411041900030b0031801105512000307010180860300c48503a40300740308000175044030504000030300d00003005540c3c21145900fa543e0047c2076400c4c2410485c8903180d010240483e00942c441150300300c85840400040809d1120301442c0a40036071602c40e160340d442c1c00000117809030408010340c00200128182e401c143c051070204000c079660a40100f0403050300344024070500120400842d045100030041b030b000e050b83e980c1e0795071408904480c02ca81d0b02d004082c403016102024082c03c0b680803a01c0c2400d0b00c0c145010b00c0010510a814840c010401001000022058450b1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 60521657 1250 60520407 60520409
    0x4090201110708071809030f11010b0303040305070f1a09090a0603020913021201180f05030910030e120309190201030e0d030614010309020a0603021317010b030c102007 74
    0x40081e10401c40c0d68100709915103070b151041903011790014980c1807040782c4030312865044d01d03490f441d200c2a0001c060400c070303034441c100c40c0c0700d20300c640d41c0d0180b000c0181d9080006d04000e40c0300d5002454250304100e81d164000350250300c40881c094000614008034021031080c2c80a461082d5000c004580e65070300d81c50f01504490740069044190310303040c0442c0902a101166410f402952a0f00401c10142016401c03a1851f06001026030250340304000082c01d0103010803c16400344088034201400d40001803226598403880f080406d644440719040488280304040214140000960940c900f0b00c1402e0344800d88111000d48480c410f072860301c01c40e03000b64030040344403080384d04954207a2803610b40a40101014041c1300d001c0078880c50408519842800f5180312031364003404843e0102d2601405501a4006a07105507100c2d5a000340400d00ca402403103940c0b07034414404004a440c50000c1c091609005c1c20144403409642a14468825180c102140a80c41d0400e1184101c0c00e0012089490a001403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 60522907 1250 60521657 60521687
    0xa0512061302210604030e060306180c040e090307051b0a05010503091204080a0203060114101202040905070302071b050603270102070b0105100e030a082203060c020c0405090c04090201 81
    0x103c0ba800f0040c00a0500d00c034a1094540a5141a490040000038002282d0a5a1003910b0180c0e482d010004140c03040e4108036919581c42c2855100d0b440000302d5181100d100c0c007564404110002448402c001030f2070032100c81d03003c000303c50300ca550100c2e0701400c2a01030342e4140500080415030100040011020013030078404615160340c1c960003295102c89044800b68481d120f482c0000c0340c0718540059a00061600405555002d6143d0740c00342d44d14086d1420300d40e81550300344070003e42102103005441c4925929500180c0da51454a404140d100ca18411480c07103c003204d2042c002e03500c41e203040b280c00200c070300103000304c00001000c20740302900b24050090446d4004603a4904100800400d14141c9500710b601c18601084480101d0300d402044c8891503140d8041c08400003c04c0210f001072410305507a040d0b840d04075454608101d040e040980c400c80d03940e562062081e61603641448603815800040b1824801400c204204503a0f07651000341e058401c9a0301c00b90a401c581c00b0710214036042c04 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 60524157 1250 60522907 60522949
    0x9080d0509031b06010e0f0405070e1905370905010614040617120703030b0607050706030c050a0207090b2701050301060b070305030703110d14060a0512061302 70
    0xa0107042168403a00050000a10001160390070058031401081c0300781a078074040718080344c0d40d94500e184000058041c0082e036590290090102c0c2c001007102c10f2502c994040700d02c8104250080c40100100c0314010700b0b854202100c48080007130204180106401d1180e0f00d201c2c0000448030044c500028104020002d1aa61070118006540c02d038030106410000001c6804000240d9110900d6411a43c003203d40030b150340280c1c0304400755150200103010700300e004c0e140c00a00011344002050055004400503681a8001f0004000d05545030013500d0703190710980350103410180d03400c0000e55900824011101c02030344a2410300f60944406404d4203440c0c07910301800074405d91600c440f902401e800c1c051180294201030700071503003d42c04008c170f07003841c1d90660701d603887c40d0385000b170450081c110410b4007203030250200040381c014000d9020f5800c03428a601e040205904010b0108003201800e45d000314040c000aa0900d45240f0010510310790080e00e021911764550307250700c000b60b00c0d8691294500750b044 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 60525407 1250 60524157 60524161
    0xd061509050405010c0504050306040602071a0a051006090513240618080105040b0c180909160503070803041e030501020a11010b0d08090f0102030708161b14010309080d05 75
    0x2981045002d28001d40081228644404007103030544a103000b2140c05510007804500003c0656000300f1156002d1001008107507401415000072000035600c2c01161a100c0c000e100c40c020010342840001e00c1c17541441c4a9003441c15001c244502c20091b110007926035200e007500c2c1540c086c100b142c840032140e00c04015207142c40f4100500516164500c031200380402c4400490080c20503c213003401560040547e2038659550300c0c200c2d10f00c0d4000201348800c0c0600140075031481d20f80c0400d41b0b0003404102c024040c50a265040540700040b9039220510a5000110400c11030f4000b0085070140c916000f440701111540c0b0703d4407000060960700c010055032002807098843c90f0311038142404020500000c0c0131007d1140d040100780313040c010b00580709002c200902c2a0514211a81d074182140c18010b60b03041003141c2d03c5072942504403d024018a03859410600d0402030000449100050304100032504a800d040581000114504a0f9030501d9502c0c9084828030a1680650b209014641028080c074 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 60526657 1250 60525407 60525419
    0x2040c050301060f020303010f090c0e041a040b0a230a0e0906070807020a150509070b031003050f12030406110405030d020f0d05090d02042703080708070905010804020d0615 76
    0x503500074419000000d1100e481300255510104c101d03812503c42e070b00507a440702d041071040c200825039002500240103031500014400d0701d5500800c071440445112034400c83c1c0c0903200b4802900c040d5441b00f44201d541000030f004611078684940c480c0003070150103482131851440414a000c0840d04400c206200030420403408110001c1c1e02486100302d50380b2144c4035242c0800c1613075200b2301c0c540000d101020110108100a9581d8010740d480b5100b03404407072006903600050720309a0b0044d24500d80603140d1450502c14480d041150041c03a90485000746218001d000340c4c41c985000141c03008081a440381d60503401c102c03118061b1009098014240c40c2c008141000c040d5580041c1c0b0341c0c6c03450500030200390301c107050700410642e0024075000d801d00b000301001d80e00704401802c0c1001c203800c1e100511060040d80155100e504c174204d92190311f40d8001030502c50005420004010100c42c00c00882c184207100599201003810380241d8143d4440500000ba4070388680904182600c114890210070800900 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 60527907 1250 60526657 60526667
    0x1503060509150a08030715061a030a050405100204030c031b052206030218060301050106020d0c080c030c030a080f0a091205030603120a0306052d01050f0f03010f170105060901050409020d02040c 85
    0x1111a82e41410802541c0d141c0c496420000184071507113040b103091000bc0d40d41d00050f04148d9005119909489580140c1d00e0f10f0401c0b6001354005441540d0010307814002c0040c0d14600b44200001d43e403041c01500e103003600295506140c2d050f01c0318884004185290800e1840d009500919801003841c2e205400c0030b40003001c142400c88200388a50f080000000e80c0358004900300140ea12240e5680760030400580b156407003a071180080130003c0c841084403e07105101840984081b4240b5603900109041201706e29070600009410780d10081c1c038182d4060f001400c00c00c0e0280080700c490034815283d80d02c0e2000207040215628034940100030000e503031001c00ea81035010000707991040303030a40038a4403807200c81c2030840040d040040e0007600c2030040c01c00c95030041016012100c81041c070301d0b181120f0030403880050b4000313030701c82840900c1d40002802503982c004816007644920100800080c6411400503013000b00600c520b41c025603941c43c0c000190f40355075001d4545240c0241080c4004810f4a0000b09 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 60529157 1250 60527907 60527933
    0x1206170307030c0c0302031e16050102030f070201020c150316030e0c100e0a080309030106090207050709240e0a0506031902090703020405030115090506090f010510050408010c091503060509150a080307 88
    0x1024049da035000040402ca1600000603100103900840c18955401410700c50340d40050000d80c150b05c2581e40b550250742d14420880c12200d20041400e481381058405800106800102402498245282c044401c0c200280407851940201d60741c0090302c0e181395090761030f10341c181422a08400104d0004c82c18070000001000e180710203030020040d250f9991510b42c228020340d1801003044d0040c640c100228840e680003812081540c8645007000e0000c1e10f0b900740c0440117648030600781110700041207042c8540784a060303880308041e0042c2c203404106401384241d201c20071800a00c07645183d8003103040b4511a50540c0c016040107002000310010940d00f09002c10b140e403081d001000c1c1080d00242603410102c005a01414680c0c40c00c12083e40cc1904214020a240c001002000300900c0006103840d000d0040d1400c104a80d12032404050901402c03c40389014000308005044c103204c0c04000c41d4a40520ba40d038040306c6041c100c0c50f04890351001914607042c40e0b21441c0c03203100c04030b04c06003403000d5208105 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 60530407 1250 60529157 60529213
    0xc0703020f0402070308010e04060e0d02210a0c0b090705030109030504030213091509060f050414070f06020d121103040309170606010906030504061b1206170307030c0c030203 77
    0x10342800070a2040006034403c1c204020000f0f10702a0040000b06440c004050300180f091201203031559020503241c0c6840c0f80040703c0300041e80501c50104072007811821020302058500002d038540a4100b0000c0d1420382d43c14402804803400000141003100c0c180400303000342200400a000c298482d00303009100b50000e00099100e41290000c3c4030181007180b10380d24000c3d80c0306003015618014000c07110001d00440d1025540981c071485403910301d20051265900c07030351090500c0018a051684442d180c08071942040628400480007404110340010f40c1c1601e000075480d08036985100060010301a1000c0c4c0c400f404102004000c0c0010581c20030344d45019140b00680d20b040d0074555580c150ba4840c020f59223240450304c03000e403e00002d4880c3e00181d520502540003c0307409a0f4604441c40841c540126040c0010101c07103281c02400401e0042da0010305445040c07440407a4140350709038580c0f24031500201441200d50500c42003200c100b01c42c20065400506546546142020a1411445442c544 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 60531657 1250 60530407 60530419
    0x10816020a2114031e0703090f0606180905250b0f040608100e01031e140601080c030a0c06110f0102030c0304020f01180306020d020f070f020301060807060804030804080d020c070302 80
    0x50030920210310b084e01d12441da00c84001411107520000780303294041c090b11010415881704e0100c00810019020500500e1103544009001c500e03100c458502c0003001d030804003c450030090207070082000001c6152801c041c0360300400d204403011541c0c0201451940c040422030001107142c07040402c14001800071250703503480e19050703691080109440e0032298050201307079030040070060010032100c8034070040880d00740c28441c5078190346d40c980b0b141d0f0114240707000010382e000380f00501c4041d1051151001015003074000b006851100e03602e01186500c03a0052000300401050540b211000401480c20020020380086650303003881c4c000100c1591045034107a01070160b075803417007013154441c10040d040000c1241000c0d586c03d0955031541d01030352121082c580126000e00020748400205802003084038440c054a0442a00c14030605095482c50b51240c040c2d07400a803000c0040d181c00020095015916141505c41591203142030380c80c6015180c1e21900d0184080707101c0b01d0440d4001071103c1502d000f1144 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 60532907 1250 60531657 60531677
    0x9040605060a080114010306081f06060e0a0e07020a08030f07020c060301181a060d050114060f030c1c05010305030703020f010b030a03050d060e0c04090606030902010816020a21 78
    0x18000c042c0329064107a40054880001005064040f4800c2c0707120610515011900d0b075501d40a07140b800000748162881c8030260418841002c0300e0788030b090010032241c202564800020b02c0080c1680e403452142d0024040c00a0006500078400d00a01e92100e50000b0016283d04182d01240c5901e802101c00c04050700c2210040002490401d0980b81299001140c2c14460034032905200003030600081034241d0b540c030b80b80c90003040350f4402c8007038200c0d28107049001800c0e61400c61030641242410701c40d40d019800130008001248284000c41e54072440300740701c01e541c07200d0b0384a4070301e1044078051004034030a28000020003000303400b00c02080039074000d40c00c650300c044155205c1800c03100b98621181e41507129015840000b405103010f40030f2540d580d40002240380e136404c0c01c124900c0044502e0714072440000b800303001c401c115200b01000f6103420b240420643c0703800d80c0043c202e00009406240b60002c0d1583c0416224402c01038044a01e60041041700891888642d070f034040000c00348210040380b01012 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 60534157 1250 60532907 60532909
    0x30922050c0c06010b120a0b011107060302090906040204050d0b040c05040c030b030d09140d140106061e03050f010506030c1b030a0f0c0209040201052206090509010501022a010201021204050309040605 88
    0x1551b00c0100c15414050f960b48407811001c00402c41c9071500e6050100c0c1c00800d408240b0140801401813826032809aa691110300402000103070080045105a10510050021b915405100040d407035004c440307100240c4072401d1100201c04c0d03651250f0381c441d0601030650021581a0880c00000c00150101c8071011f4000314182d8881500c0d000c0d0304c00400001a078076001345401e080e41028140a03482c5401451103419189080d03e2417a08031303001140c6500709513060100040844400701400e0310701042903003810480b980d00418184a0144104008004154044040d204031007100c0000c00481003044002c0c143c56460b40c00410038200400c03512246401c1a5004000303aa42a550081c1012401d45e1554015186504101e00d100000e003501c5201480c00b0f0b0030420500082c10f40c9803100742c0407902e05810051043c00507000b00f41150804458003000c3d00300d100503480c88804811410110921010040b40280034030903d00c156400b1507400d010901102000a20102d201903406001080c0c80310 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 60535407 1250 60534157 60534179
    0xa14031c020d0f021615020d051611030408060f1b07030801060810050a0b0c0c0a06020705030106090209030a11060c0304090e01050a091505040512121006020d02030922050c0c0601 79
    0x2a0300c0d21601414400007030000d03482401b9010407070480d40006052071800845003044443c110340d02c40e0301081000c00c00302013036080794020f5a4030402d48000e62400b402c0001c0e6607140d00780940092460b004c42404501c43c00203900b4031040d508003803105291a500da500740140405c41c280300b403502044401d40801d07050820008508260303600036099550503031801809116951140010030001d000d00030240310566034241411008085990003460300a0400d0205401c40c0d0b200d0b8407600200f841013005428a1b18003043c007904668010071045000740706940401c141f4481d482c0c0101043c000001c1c04600f0441580c00840c1c1a40144000c10031036444090b002d00312101d50002900309801300c071880c00140c0083d0400d0742d109124009641c591050108402416040952070100e0086680300b042609507541a440e00104064402003c0c4128501c6020b52640300b91206940544a603010b07501000b00c2050540d041136059100401a91400d1610010b160300010411345680c02000d0001914000d40 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 60536657 1250 60535407 60535417
    0x60f01021605060d27051207030f0f02121c18020f06030907260c0a180f0b0613180209010909050403110a03050901030c0207080a14031c020d0f02 64
    0x480408001c40c0c1000100401c1e034001242c241d4038581c03030310200012044074041c4452003001d1400600c020f10703c9450300c0c0b030503d003800403044400704090000b42c010030b80c030a801c01807100d50b41c01d0803200d0600d04d05040307003000700481000542d007100003900b060114829105426043c6845020803211005180c400c17a00880194041d5200ba4803105602e4607207420300c0250b42142103141107491180d0344140f200d808e0186402e0480b40c0c02005e0160804440d4140212200e0a004803290030005040c074040c5400707800b031400c05800c0380d90343d0b0740c446080481590060401d040000c2800707890380c2030060340d854003800e140035002074040000d00c45901140c650003520319514051b100c0031140c46c10b203189079006010042c01031b41080344040801451542c240003086682c0d01940c3c80c20341d240c155078000b41c107680c20348140310115800001d0420240e0b4001c5140031442e5404a59040311490489001d451030180d0642c100d881001f0704a20340304002d6940c018440501007201c00d124101440101100300d0042c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 60537907 1250 60536657 60536683
    0x20a06110f0a050709050c04091a120606092712030103032309152a07050604031505060307050a06030221010b09010e13020c03030108071208191202030f060f0102 71
    0x3c14400c0c0805c82058010329403007a034090449041907610958030054a42c82144101b8807080c14502d0441810300490300034602d03042c04020421414140c0204a40340300040001c800c2c0b18603150502380b001c0c1315103100306d011541c800441d0310701c50001201210f664003e00c01100403d011130407800c42c00000e014606012f45034035410130b00b00344c0000305002810b400403144450308641002064500814885c05e50000c0120031071800501e9031104509180080c640c01c514440ca00500080001441e950103040c41e61a1070000482d00b92035290129203000303000c4e000a540310708100e00101c2c00c507500d13501601a804904103c4482e1142d19000700390300d54003c0c02038083e00d240400804c070180d402400c2d01142c188000e0b202e110750500900e540c4003241c10900c60313041d0a400000040107034000c01c010003005081000c540300344940465450f607401d0b00c2045a01244241e5041c900041c3d24020b454164949440031019550b0349000030034942d21440440340e441c42014a07420906e019480012400c0c28400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 60539157 1250 60537907 60537913
    0x10507081b0a0203040f0b070309051c11120106060804030201050112031b30020709230a060302060d020c1b090a0f0204050d03020a0506070314040605060607020a06110f0a05 76
    0x341e03010200181d40014081c9055200400c00002c0caa03001e01852401040e04103426a150340207841d00400400c11540828411107424130010700c18a00e81d4100c0c032159500c12100e084600d10f64021170800440002a9140da5290a41c0003491a800210180c441c0f4440d031300812240e0303200c0b084090b490705912070150001c1da000c211600d44001c1982e541c00e02900403610003c8050b500e0890300020000207817038108840c002d11306c480145404220410207031000035020700014103a205101c0c040c454030081c0d520b905003150042250944075074000009960098081c3e0b5440380ca02e04424081e40c41015160250700c128000f402c61040a003030060344110340100381009585894100c2406045c003209000c0030b1a40c00c02c0b00181c1d5a450010720541507100e90085c1c8281030960500906040e00184000181420300c9003104404000c00006a80541d0040c3c0c0012562149802700780c59002e5004029040b420991380450343c3c81e080400e00f4180c00c0f0001c229620300603084409038030341d02c0300079000b40382da4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 60540407 1250 60539157 60539191
    0x1080c070b0106030203190c18080c091611010609020304020a0b09030c04051506030a0606030c05040b090105030403030f0504140705030a030203071106090a06050301050f06070312090602040801061701050708 91
    0xf42c030136002540c03c841c07202101c2205001603500720040342c0e0310b09201e0020501d0307031040301c00b10000901404000c00c11403024023018500000829500c180c0204444107044060007800b000c40d016543c0201c0440c48500200001c60310340001f940254400d030b44c141c3c82030304034042c001188161403046880c00308000d4098800248c1010511001d800080d00c059290a807000b49540141c8034040610320599005501003440ca10342000a01280e80c070a981c803080000c2084144104009501207441003c000e00e0000ea40e580c0303a080071030007000100307001904070341040c0a1100b072201d400d10a07000c0c0c141c1e2805030b03510207035207208155403100f4007440113000d80c0081c4041000f14001c22400d00904201600061400d880b000018009810340e40064012600200050002c1d08003822011144001134801500d80841510003426048540014055054881c4010010008a501a1002020014000c1c02582c3c0c5030010050003c502d190090354544c80c00e1b0002d11000d11542e0f1240c0584406c00480c8554 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 60541657 1250 60540407 60540419
    0x70201120902030c10050304060f050606040e0403140304030e010f1b1719080a05060d0221010603080c01060810020403080403020108040515011d060a0f061b140c01080c070b01 77
    0x242064074030981e8140038124460303d094444502400002d400c994981e80e4900d800d02c0c01400700c4410a0840344014a00b4041144035110325080740d041e203610000320a80c503542c80c9000c5529450504045145030804828041010f40003401c1072403400c4241c982400c21300d02a803040310180e410a11040d07920004400080206241030000782c202403803450503d20b08540050007803071a066240c0c80303e001078000f00421070116224400c40d134024408031100807803200340d0340000f1061500500b41040240f0350138103010f00d20754258031020003194800b51a546414041c001d65000784101d2080034054040c42c3d00e81030350003540d031007103906699020341424106070860b001110104802401210f00303200f400c611081c82c8142004482c02004664141c809224040800419050026207011700610140c141030288458401d001020b8502500d000361204900e003440044d00508c1c060080c02c60b076850862007100071804540842c1041080c1c03140801600c0d1381809003401d12541e2005400903a0640c014424 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 60542907 1250 60541657 60541661
    0x606030a020c01020906040b040503070e09030307051b120d18020d0611220f0501020115050f03030706050f0a0608030f07030f0c0503031303020c03010204050a030b060402070b1602011107020112 85
    0xc1d002d1020001030900c407104000c10310a602540051407001c4001c607041002e40f404003d0030000c4e02040e4a0340c501810500106692400094818018440c0100c0c4803056203000158681240c10000200c40c111200d00502c41e6a5034880d940602401d400c1030342003000310003201d0092021540c0035102c0d0304a400e441e03d5050003006501000d41120600f0000d0b1100040c01e03500e00f104103181c08408450403490300b50080e44d4802c040e48298196414007541d020f10503480c06c41c2208484040c0d9402c490010010000b904503c02c1308401080d06240006001c0700d0743c0c20f141e02c2841140100410051a030b01c1d240742999038001c00305543d0001c802003001100180c0320f140b80e0110b095103810507000d81c05031981d03150300f103400403141c68000d49041c1007600c06050b4100b1103036036640b105038000c42c9003a04002c0410b503904000c2c0406000340c0b402101003001a2190750480e441c3e65080783d40b2502c0384c200380040040042c55508030000640c2402a6030440d42c00401c00c07520807550503150080000f41031f21407280 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 60544157 1250 60542907 60542917
    0xd0204020d110301060203040503010f060501050304110a090903031a010e060d0b041d030c060c0f0904090203031b070e0a05071b03030e10020a030e0303040c0b03040f05010908041d0606030a02 84
    0x341501c440b02c2c421000050000346001c1c2a89401070b58403642803005060171611480403444640e0305182040009980104c101d9400942080c0a056144040804a6403014140e4003820310f103490f00310705200741541035225040c48c0301c001841401c108a0342004551040e202079070a07600c484108100c010010603a480f015131a01c0282c00402d4040d40312160702d406a140010590580d0400180260411024031005034021200000c01d81010320219100c00140200150980655611003110066503020429100c0111051001070040741d1030300780380f5880781c44078840c00140c6103401c5c0120b00404840c4c00f80521a0700301e555044140e80381500b501003c1e0a9080b4107400b0b141d0b035865650800d427004d00040b60755188410026948624000008048030b451091a9400e500117009000c0042d000388595011603034085112501e98466041008910303000741e038000c0440d841e00d00d503030003000f8803400500101c6540201116000740c0c2c1440d800780c1c626088a807140c0c0000200002052400300f03501806c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 60545407 1250 60544157 60544177
    0x1f05030d080c070c0b03160f1e030c0504090609060501020613050c0d02010e04050705041505041a0304080f070b061503100303122d0b0303040e071b0f0f1e020d020402 73
    0x44021691214017242c0b42d80305a80010070700900c06141c440c5560050307590750410b0402e141100030711107002110b80c40840c240c55000109501d0b9041080540c0c4510300380c80c05050824410040c1c5561050710000800051140c680980110000254501400d44c0302041e241d4010025041040c41003003003042d15041002c0c22414800402e5500d040e98465100e018800d00640c2c0f10076a445061468921610070b04166450821804010501880011540c690502070000d5a41503c03500c41c5e02c2d140b4030034080d0000300120300d20089901014030040700c59a50151f241510b1182c01100c64200710f90084c40100d5241030380524500c000c100003441800c000340445440c1400095440000c0400481469240d00c008075641a09442120203082807284160b4030004500840c0340c140303002c050011000c0020710f80c800340a202d10f41c0c001c0f200c00159030101c50b9580064489800c0300c0c24039040140c0c0c000c4078400e81da0740d9845000c1602035000740352038105540e0002c2002d00005140d13400c100107540043d00349 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 60546657 1250 60545407 60545423
    0x20306010c0614180c030304210218070e0d0803060d030216031109010602070f0b0c01060f06020a0b060901060504030b060301020417151e0105040f090b1f05030d080c07 74
    0x1440400c82e0751151a600200c0340e200c1d034000d42002140d01d0842114504000c54a07040411881c20b943d80003c04c650840341d6032104081440c070304000c040783d080902c080c041d400100207a00880b0411010f0005403081c6d0306600d8482454805c0424400400a8420001d1048200b0400311701103103410b400c4410f0f002d10910450b5404403070001c0120100116900880d1040701e4448007085500c0d20001841c09041144000c0040b85d01d0054086100511071060100c07010002500120003102908028085c040c041c040040d5240d0300c1c103000796292090b01050390890320f0040869910f2038000292130480f00d1076540c50341040e041d44c880b12618140907044640c50740d42000006a00001d89100040040a807406407101c81c00d5801d260440750780084c000420ba6665a400c0d040c450400e085440c195281a01e00144480021000c8002001200805044100b08500308826130017024a520454500f01e9098190550344030140359440d0080d00951011810303010005102500c03800107003e041e0301410f10 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 60547907 1250 60546657 60546677
    0xb03100320041b021005070503040201142205010f030603023a03020f06130309060f031e0b0a0509010513020304050a08030109020a17070e0126160806010c080d02030601 74
    0x2d411a41c00c1d070b4291100c1c0340e40c103064403100d039014040103488100041e020f100d80d14080a0041c614440104028140580fa086a040408445040e18120020f60314000c44501c1c50000552100a940c0305050015190b88440110b0901c0b0380220400c0307c1d4041d054402d1041c8070700400c19144409400052805800c248070708825401d0150480440c0c041d80252840c0440c000000c0d05100703006025800f981c0501012200203648461503008072201d80c5820104140c002804602030300c0c40988407520f004175204420102c885c507a002d01142038045643c115170503900d0701030081100007442035541c088142d48041c4002e031031540095a001d4803486c2612030303401d115070720150719407c20382007000903035400f00e07240d00c8898024855154800101e1024102890080001401c501d0702d04420f60400a62449000442c182200010700c54014103280c840c0518100703030f00003402ca01c01c581000000703480307201003005035028201650690741c00c002413030f01e040405028480039600c084c00c00c40c1000b580b000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 60549157 1250 60547907 60547909
    0x1030303052e0f0e09120a0e2106061203032d0a02030411040605030307030f0201020c0d0c05061807090e150106080915060d15060b0708030403090b03100320 69
    0x181c4071111104201c02e91030818207244400c011919a07800800c0d00c031000c0410310142c0440002e05a12246000784429034030308568000b02c9101440700e120366008203101010340041c0070036240c986601c02c14103044802a580e400c003040f0b92885280400c5c0b11640080006c202c480310341c0c480000851700b03510402d450708441d44180d03007004c220850328800900c0c0d000c03080c40104021180c2c3c051884504a8040c4030140c10070000946078815800c00a0600213141c0c00f501ca598000e4040c0d4014440f507101762418802006006041000c082004840900450b400203e203009805040c03120828060024244503050102c190000e060380090b64109114480c3e031145a1070621200314003074201ea54444100741000685c5521781000c00f2094844868030404204076915080c1c1d40c000440e0b00103564001c040030004a1038000e11341a080000f04501c0014a00180027040005500580c481e54420008941d41c03e0900303000e0109490301954980395000400224000021104220396540e050b48110403100d4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 60550407 1250 60549157 60549211
    0x270803070503030906060301060302010e220608011e1b12090818010e0a060f0507020402040e010801020909090705030304030f0302010213060201060611010207020a03140a080a020102091c05060103030305 89
    0x100c02100c0d5984000b08200d108041400810f420010540082c00318a00310740c00a4214418444524000d101e003a030074102103102d00c03002010b0702c1e0212204115060301c44800902921110305024540d0040b0341c5508140302003482424402d5649001808a04504403800c4401d00141c0034609922910f400306003002c150088000e24030683c08580034000c075494007002502010390a1400352250420f000e003003040b10b8124803000c0c0b200702d0390715006523640000d20008009016a420100004024000216007004154000c02407030504441c5047c0304d6840002071540c4190b00d0040ea50581c006100800004940980c072460080c4240009410545034410965291030a0340c800d60060303460b103070b0400020b5000b20080c200240c0c000020342c41c1203042c0c1c02007000c0d0315003884002e20507403203042e03002c50101040c031103c450b05a11401715a910001014028023035003104206502c5501402c028940c081140c070302c6800c9030340c0d1000150042c0e84c40d40d00e0990060400402c840268a11080309049684a070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 60551657 1250 60550407 60550417
    0x4050403050f0c0a0c0e07020705040e07030501060f0918110103051504140703050115081503120706091104060311040b03012012070507020d060203100308040803030a0e010c270803 79
    0x380042c0013002d00781c1410350140085030300c409001001c140511141540c045040f10583e201980c000c10b12101c11100b08c2c0c0341502c1a440a021946014000308040c0150062142290b110300c0c000e0004001c49140300c60351440500005010000034032100903554025005580e020081000c5900e0111001d4041000c2d07a0410802141f0754002000700904c207500351050a002d031405441050b0420b00e6402c0241c03a0b1380e40902003800060070f100120105550030403041c0c0e030780782d0500716003034440390301d440c06074050803203901c0c201d443c410007190461050a19200300740460707400060350171040c01900f042c4401005418440364040d501e4100321896212009020450703980030030f8200c1d95400b200c0e600c4000c01d1401030414000c01c0010400c41c0c025a5030a41c1c00e15000e41c208400603500c0c0c682d0711182a4030403555100a0080340003142c00a054040403014600c1141406802d104a0014120342800c94080500907004212500054540750005400200c500b81050b074078440003036100c1291034619045 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 60552907 1250 60551657 60551677
    0xd05160f020d0f060e07080c01050c01060b040f080111090105040308090d2f030d080414070e0c0a0e09010b041205010e030d090317060d0809011b030201020307030605090606030604050403050f 84
    0x482c01d83c040040030b108050340131407224050040e150500d4519038562040301c0b1031904200b404030300808614800c0d03000c900140180d098131075441f40e03110401da011142c2e40c4030300b00b03030fa518159800854101c11000c03a070500e001655018138190459036001c1898000c0c2c41446d421002c442926000516030381c00401011004080d82c58520600d170106508010b5565051070098100300d031a8600103802c0481c40745c100d503100001130810301c8a40c800c0703440d2001c0c0c0d40c00003044440c04018041c42000d04d80050101c0c070515614403299682e610240b0108030b10a201c0c141c07081c08200020041981e00c070f11030f4800f1034032600020880709a1060640c0c0f03541c01090088007010303511514041016003020070002440d100305000e01075031034441e001406034800e04001410004002a1344000e80c0e200364940c1481905035007070070107001c04d603043c024000d4104031800008646810300100b058a014400c2d6131180000502c0c0070301d1940c0c0c680601026245c090801c4090000c01c0c030006820b05a0310014204002c5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 60554157 1250 60552907 60552923
    0xe040f02040903081b120115021014071709070513060506030408130608040b060103051e130308060a080c0d05030f12040606060309050a03030e03040f09050a060501020d05160f020d 79
    0x2d100e4601e82d0b4005c1c00c03403c00c5000d220304102244042001241e1641112241d01c0c0030340b4490b00c001020707030904030700070800360403e494034104415029101101da40140d200f5983c98911444005404492a00a64800050fa400240e0400c06450a40904103103403a10240c0400d40300e98403400f0072180e410948003103451000104008800250340c020040c024031143c5050b84207810503032683c551440300645507504150b15640044d01c2141480446400070402140b005880d140c00c0c0c1c070641441c070a0910490004017001c01140540c0b0707080c0c0c004016070f81c5100c064241c0d04d050b40100a0121007800048030f150005010307104180356814080c0c0101c840210359501145003073300e412421103906800c007500b03061402805401240c0000394101415030715007400030f5040d195400340c03840d60007a64422001c41c01001d02c08182e125aa4220034081d54440109219058a0300016a00d50b10502c48100004400f400300c7c0702e0703d021102c81190324038058680c103041e84900ea00810310801c0808010f541d010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 60555407 1250 60554157 60554161
    0x20a24062606010302090a05060a15050a0f1e0c11210f0111032409090307030201061202011431051003090b06060d141e010b0406090e040f0204090308 66
    0x58400109440c0c00d90306200940510342c19031740055500320b07010300717194a1595203030001641e9071940c1e4400782c040d1840e807004102115803244010100e91245217100f000442c00d0341102900341c020484018450403c4406605824031407008594400c03035403100307450600411030304407031607103841001c1040c0c5006004260440700c0800c07004c0786829098448846180e14181c6451060046841600c0e008901c1c1c0709148010030403144130041c1d10001c0b60a040c1d01c10749140601401003000001044010f1007500280310f50343d40c0d0031102c4801603038980081c2c00715085002d000e03101d010b0a40240a42122002000c00054030000780d43c0164404880e69a21074407a12414490b510f4000c0c140d108045581c51305024a01e81581c400704800c0d0043c104034083c0c3c0010440140f10460b0f074100c00302c280070b511450328503850044094a103030030300381030422000c100d504c001141e01182c940844094420541315904440d150603616009060000d10a503419185190010010b0350b0314041c1d00b501c540669500c207454 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 60556657 1250 60555407 60555449
    0xb040507090605091305011e060f0f031a090f150909030304110315010603090b181e150a0b2803030e0111060a05070201060f030213020d20030108010b01080403020a2406 74
    0x494160459003c0c00301662b1f44030a4079512000ca09641711841ca00410450402c902204481c4a04600c4030303070002e9003904000f9500e030b222170b0350380c4915010b81c8001030390032100090040380d200a0302c161815070001c10000317010900040d4403409292001d0100c0da550004800001c0092100780c0040001a803100444d4041c07018030343d202900000702d01c0c5190450540d00141c00e582c2c681d01285618804100c8000d4000c18070700340035450b0700c031591011040da546041c0c0d205000510803a800c051103821526200b403007070109603419a5007007001142e000549030941d181521b80112010186041200c410019604d500050001c14015803544501186c2c0341044000a0309550050708504410f0b1360301001040541d55651546030401412000165184940d4040001030b0000101680c19980c40d8030032081c00c038948400950403143d070031000300700700b100e50001100c0c11001520007500684c4a50340400c01704540060740705103010b40505403614003015540343c801f03070340710303540960029158500002e440e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 60557907 1250 60556657 60556709
    0x203060a06030b090703050406020c07080309120610300b040201093807020a06050403050c0910060f020c0901170606030109120f030b06030f0a0b04050709060509130501 74
    0x207000c56040070301000d03664101054600703000624441c101911440811300b440310300d60494541c04604000d980403c2d0702e48408079625070080040a000e040c9407000c280c1055008a03e09010b110740f60805001c003486c180d000c00ca901d441018038006400c030200c2c0ba5090b030480d1902004014070030807800c42580340c2400094040a420b520411815001c80846140070300654031407140700011300c034031001840911034038544c140101c0e00c000750403081c070000100f101ca4010002c0c0040340c2c405d604503422104541c090000000d01524100e0551183e0310050000c00d002d170512490404c40380c070484521110342000580c0d5070400b0f90240e81c00109180551f1401c82c414420a0341c0054207030022301c07248140350348401d59140c103640504204580d4502810145110b0b420008904000921140d181d081a040d24040e006064620002c030700e2500200030001d05060242c188034040741e84642001c9484c0c40303001c0e96203900c000c4606600000d910082200202e251180328042d10350003090b03056001c00384002e480 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 60559157 1250 60557907 60557909
    0x90606030e0d0c02030d050a020c0d06020310090603080d0b0103180605150103020c0c0405070504030506070f030e0a03080a020906070c14040c021b0f0607050f0c030c0d02010507020609060405090a0203060a 90
    0x100f004890001016072000101007031031001c3c07407610a98440000c1000ca0402032018000c03584076240c03815000604c1280c1c0c01a5000d9600340f811080740c80d030380b42000e80854165210041080380280f04066441d01c00b0760100304100700c181008030b1194001e42026500c417900004c1251a15a83c5060203011209820344501c42002800c01f1850411a069440c4d07907694007242081c41252104000b0305054401c8c4147d070002e6601004941c9182850300029040350f00c080040310009150142d02e440b20000091040026030309071b201c441c042d413220803495010f94481d201103034001e407007040b0000000e40d00600e0754004143c0704002c54000700790740c0c0400080c2e41101c0354400c2190310100e4100701400d009800440c0103242105c400303040e50141030200d07043d405803500c0a49140210071448400040106442c40c01040840580e44542610010400780151440300640000c0c800d002580040c1840c0d0010300514030000c09140c00d2070ba40702c0000e52820404c8800050183c1c000c0148a080e00f0070310300c240 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 60560407 1250 60559157 60559183
    0xe030102120406021b10020a0e060a0c03030507021905010203060f040501050306010b03130f0516050a180209030a0804080a06060b0f0f090109261006080705010f0306090606030e 78
    0x5880c20a01d4030091040780d0016102400a6034009807224400642403185005000040b06456a081e508a01c000003500940c4007c1c0104503800200015450300d0340842d8101b81d19500c4030080d11046440c110010f181c000e03e01c1c801d510031040c144000034002458140c540d0f104000160b034918001d02400202180c0d000c0c10f0740034908100c01032080b6940840c0706410b491351103181c10784940e640d0903a2001e10000c07450181041d0b10401180060110102e5a1040c4140c1030090303540e116520307001d204200055100310808150000031000140cad10030303002044003040007012200c60000603240c188141d80203900451701d030780c090302d103130801c0084d00d0050a00030046510a00d003490210001101c00d88121b01006540360700001c0c2e0407009030f01a11214016003120580c000d2680382841100200c4090002c007444907200b101c20014001415014010503102c143c3e000c2c0400619110064501500a8201c4801d05407194008071348002c05200d128001c0c046950040703500c03500880e00318100700e06a0022 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 60561657 1250 60560407 60560411
    0x901060f0e040203070612021303080306100c0b061207031703070906050f03011203030e121b06150f0d06022a03120c030901090804080307020f01020d020a0209190905010c0e0301 78
    0x40541c1d400301e007140880c2d035241400703490204c0c0c7d810954001c2c40f4107031143d00012032902c0040280840702000d103101e004180d4100c0c500250f21201901e511030380410040150a100e400181e403800d01c5400100d82c0003441084950700c54880e40c40c4600c8000703031142403200890100400c220103a0003a1844000d1800c0d044c000d00d402707072000d114419403005000c1da075140e8142c0c410090405100f540000401001d0206442c5404010b800e0039450360b20202c5c29005e44c068001c10680c01e0580480c00b40d012b41c079040603a21902c01d5040620440c002601d035801d52108800d03001c0404a42d09000600112141c0d11810b900c081c15058400c803860001c0b80110402c2c1d0003408184003520040000c50740042400f168651a5a1031030300c003d015158260f0001d01480012900084008001010b000c505208498032020003450742c0049946821407840140184e104030000000341c18410240c1d5046400030341806444a443c0d105807040d100000e400f2211a075590b41501c0541c3d5101d041c90503203260850007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 60562907 1250 60561657 60561661
    0xe0603040503071209050d050a050d1d0906010c02090109090302060a020f0a0c020303040803070b01050f060a0f110a0f0302060603100b010e0f042c060c0f12100803030901060f0e 78
    0x40700c0e602d0203034100080c5854484003800e0034407030140c68a240107000040c0340081c4e6280391725145844078590401200d580c8140c02c3d0859149000301c40208005030b6580100c14000d135050204030740c003400030700013a042c00004480580503854801c420343c00707410f862401041c40e0050303107002440e1004c020b205000161061210081c008400c0c4100e901039819464508040001d0b400000d0940c451070b0b204508512002036908204170000040078101c0d03004448108040c02c040c0240180f0784100c2c5d040c0c02c005209518001081802640d1810440e4845c0d001c48080706420f07601c00320111070040055000d0f0b400281045024076040194011580c40030784280121071044001900621106440307a202d4440151011100d0321240c0c403101040c0d00a1520401005440d05910f10000720103220548500503500042c0d01c002ca04400c4480c0119015525460076810303a545d10a0820701428980d00b000b05110700154a1030100060340c0030b881c20700300000b005441c2c4004642c040b540d9a0000f50307000f0080e42 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 60564157 1250 60562907 60562913
    0x11401020c062a01021305010e030d020303040305130302090a091b030210120e0d0801060f020721140d030b01030608060610050c030f0d060f061701170f15070e060304 73
    0x3921441030321810a84483c0700300720032a0b042c84054143d0b02c18190310203d0b107100c424210200010440301d080c0c0b01c071070045800d00181522011a0070990f005a071041001c180020b01c17410040448250403030140804649036400220f295000f07480044d0520b40740e002c0c0000348620306580d0101c0d800c00c000c0c0326600500e158045811207030b2506000041c0304a89002c0d407440b8400d0307000441d40f07242c2e8400ba2250800c00d41d4010342142802e004100009201c5595050f00034000070b0008141c411417010780e000310907880e01540c1c0005030034400301e49005115100c1d4258010800500100303410584000c54030340d0f40d180004046408962294440c1d62010381030007029181d007500a07064800d81c0c90403960310444003107190720b035128403900200094400140600c12100950112082d280e8110b00c0d9000c0e65130b1048119010000710085020358842003004205228105600355044840102611451600701a1890801d12100100d84101c040320040000c00d590000304042c41e0a4103e904a086043c40c0c4c03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 60565407 1250 60564157 60564169
    0x2040e130c030b07021204030f0b090f1207080409023c0304060c05070b09060603060a11190e03070e0a0b010201050103031707180303120f0509030f030c090a0e011401020c 75
    0x111000c3c005200342400329103402c0c404e01000036140409009150342d02e90f28134080401e8001402c040c1c42e0140a44003141c4000000300f02089104486070081900c44c1d0007074120343c240d81c810202100d0744e0000704070006140c58107001611842141c020710062800711380909400003100240113214103240071803040034a0184000f03803a001501304100066800d00a00251428840c0302c001420380c0c00036200300044554005803051040d07c040d0150758060312a1b4103140c1c00e8402c80d5010209504d410700ca800d040c1038101200b0240c5c2c00241c6001c103422440c40020900307040d4aa040900d46401c220102b141d044918010350101020a1000300f1996155490080452204408035820840355201280c40c00e40300d44081c40f001e00118070713041d069566070328002c1c0100f090380420900460800e40070307088400750b500c9014400c903800d4000d549404081085141c055000901048104a091050341d810383c84100201c0c010b0582031801546950500017000c09001c9014180d50465000b40d9025400d900c1d06 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 60566657 1250 60565407 60565409
    0x30f0e0d44181504031a070e0607060f0510050a08030405010207060c060906060b0909090106031203020a0210090501090309090204140d050307022e020705090414030d0c0302040e130c 80
    0x9100040e2901c80c0081c8903114a4099450702c0d5006241542c0300450650050050003102d1242080c64810002600107010761941140c081e13001c105e12410b00c0b01b032400c1503802030a50500c0750000085500100c1000003ca45043e075020701b6038401d1103001d00c40c60410901e440b000c0d1901000450405151000003035440d000ea019403030030811503c04200401001c1e4106001580d8408000d00c400d0351502c2c10aa143d8000020081c07041c9802d101054102c20103100e0780c0e040d2608403c0004038843e40340c0b001e038041d501405010007107108003440028ad500042c880c2c83d145c01c1c0700c1c07000441c0c07410083c180200b441e46c01c3e400081d01176204120400503c1242c0e604400403402c2a18120240255070a146046000300b0101035005909100110030144056505110a204600c5416810500305070120707501c54643c0101c40c3c11084640105000c1081e561a8494013150300045920308880001140c043d03a07594130000d800300c0d40104003807002c21151a1020b50100c0c01000010441c1041d0700c6241c08640350f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 60567907 1250 60566657 60566783
    0x7140103020c1009050a061407020a120c050f06011a0301060903150e0d03060905010807030203060f09010e1006031109090d031109041a090603010e0a030f0e0d 70
    0x7000034000d9441c542031041219001190b4010010080581130854489003040c008030b8540340352a403500380401300700c10124090302c8961300038190a052075a0750b0002002c0c0b01060424014040c0754200004c20400c00740022007102c1014220551500f400184441022020310460300c4060005101081d440010b0000712500890100484503050319048018500740d071104d0303240c0c02416855406107405800c41c00171141d80c3c4508000b03d0780d1b50b8400644a01c0d10380002549a0090030205414840020925801203145000040d110306e410802e9403401103031f6284030322001e40f030f40380070410710141c11400c1e280c0b00015a21a0018900f0719030f80f5859440e02409001499510550700c5071081d400019101540000350041040711960120742c02e0b01403007441c0042c4a8000b50340000c0b142d0034180a841d2010302c640d4001c00f2941ca09a034103540e02c0399202c00380c5d42000742110040e455641d402d0b030103a80980c0118003241824080d080b404003034840404803040b90070600f01e0300c082132000c1d1030301c3c00d061041 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 60569157 1250 60567907 60567911
    0x1020a02091506040e07050a32090604121a010501080c1b0111040803120c0a0509060a05090301090b1f03050730030f02070f050607021c0c0e01051207140103 69
    0xa0000081980c001c54002e882031710060001c1126039500280100b010401d00e41358521101c0e413003814001d0307800c00141030358803600310100665442a070041c081c00c0541c1000f0042e03800c2c02d4540d00c040000840102c0e09580400c048000c0d014007041c1042501d000d04000e1130031b08654544459001414403c06036904424509000c150415035020760004101051145629640710340d6110015681c3d0800082d60384506810310101d54200b0408040300d24541c5c00b03843c1c00c7d05000c44107042103080c0e0040324000060002c208904c032083d07a420300c500c400a41c0700e8051000203050014207022000060b00007500c03c048600c20909c00b280d03001170708204484074a01d411034402c10a40740c049803a900c41c01044404072500d000b100406802c0441d010b40c0000d29821102c240b50381d140000e0484c2010b00c1440e070801d10400900001d03003414503120040384007031880c542140c42d490391400b43d00702a03071784440b1020381f1900041c07045140c100b1020301c4540d4403000911710780d070400200d0755108100f08113180c1456 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 60570407 1250 60569157 60569191
    0x40b0304020418050d0f05181215070302070b011211060a09050306040c03110102070614030406110c010903030e030a05030a051506040b030105010336030e0d081801020a0209 76
    0x1540e00d0f08424805a40c511038282198081e1a165035140000300135580071888024408000324498801d40304401d0005ca402c0303550240031400e001011680418072540b82c01012102d04001c0ba0850032940600d050340c0d4010394500803824002c1d4540810781240d1003004081a820380840e00c085c1e5800c40f19402118015a541a40c0900b6034104800342d005903054081c10041000344a082c0791041c01300d90207402010b6205900c4ac00481e11040300b8010700010030707400e54030030a5407060440915070007489082c00240888520034032070300315048481e550002d03030f440345018803c1640c18001e247d09841000c008608058140c04042c0c264000209080c40e801d03a107400140f03803410045030b100640600500042ea90703688444c4441c44540c401d014031804642080c6001c10800d0044848a03858000102442c90f412300e01d441c402554086541e0079410002040e03c09806907990400e5490310a11403503c55a0b43c840245805100c1c03a1402c0c965410740d00030305e2401003d6120020025809420b014600600c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 60571657 1250 60570407 60570409
    0x906040b06041b020f0c010201150e040507121401060b1c05130803041a0601020c060403060b0f030706050c0106050609030606010c0510020d050106080f2206020d090501060501170c040b030402 84
    0x2072081c031a000841000f4250900e0324160003168494100046005803402c103014400107a081c0c0e29164a03000002144000c20001010168003094000d889402980d10141c1d48400c056420040030f1001ea55600c102d0203d501c508009200b100c2c01040c02c034420f5810305501802001704214000d801c0c4510603120f000080c60300b60351104071780308268407400f007d40340c1c2030a0030b00b44071052411040c0309084000c034001c20921340c00040c580c22016402007d85d4589411507075030202030035600210941003c0c038080c1040165805005283c050038482c2c0d00c5545491080c0a00c500b9685070f1740c000c40c06000200031950083d00c002c540d65510000a081803100b91541c0d2810b14a000c0c40f0549000c0702d01c0c030119581c0308000e1683c000714126001035451040d030741c5a030380ea0624070b400d00740e0301c0306200d00d4809a54800d802100e8032402006010313120050a0050034001e40054ad5000502251147d540d101c1c18007407036800c8001d0703c00741d004030707140106d10381f1702004068014891400f44a1413000040001130031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 60572907 1250 60571657 60571661
    0x70b3703020a18030606030203190b180c09071e03060503030d050705070803011d060f030715090305120c060705120703020304020402090409030801091a0a050f0103060b1803010609050906040b0604 86
    0x20f005a0303500b15509155032400c0c1800100030500049100c0d005043e46c20003030f072800d808042d006030b4004003c031080d506c0700008800503850b00440c0050724014122100750f5541c456081c0b80c1700d03c0c40d03074a0322100801da0301c100c80040018a0a0402490710f848070500c000e44000065400d00313034855070000f03120740b0b6540c0182c074680a1468020503240b400400444c03000303690003044002d0008181c26804c2030700c510003080114190f05807000d415a00c03400d030411400520030b015106030203190034850125604c039118503061580c1c0071844005080d0000d010300340014104886640140340d85442e5045c58030802c1800740105c00507186804040e000300205056654590442c0d400400c010700c10442c40c002c515000d01025002d22030101103601d040c0d106141c9030710940d0520219a8010301c1240d070242820100300884428900345410181d031040701150300000c06004200011103029034100f014210340405094621503040310341030504200034410a445c0000b181030304036500880395481a51341d0408240 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 60574157 1250 60572907 60572927
    0x5090f01091e050f0a0501150608010513150b0711030601080f060c130b04120b0c03060616150204030b01140a030c06050a02010b03031606050105060f040308071103070b3703020a 78
    0x240d0051145d80c41c10040154000500301444104156101e0360300c5c5000d46480c102481a240c10500c01d00600001040740c0d4007401101040b1040181b80c0c988800042220fa00704410032217402010510b00b0352a850300b04a000d00401d046002004d921034004a010344a01000d80001381075407020420b10300e2a10282945000b41c9400d132030640d100d80e85c070310a0840b81240c4502c15500e4600326404241e885443d0300440c0d00c6040c014141030300d44601900c0001031700003624019292840b21041100003100e460008000440c000d000400d01541044946043e20316230070401c0e4811048820104005000c414104003113032600d082c19500c1700804541680508444103109074940030024040303801440c8202c10900241c0500d00c02c004036a00d81c0f007404801e20842040116400d014082000007500d40001010722901c18608220241d0751140400e28000b640d40085d0010040401e10300100300802607040415007800300d8030070480c03d4400518505040c07a1200004040e000140e010707289005040b800 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 60575407 1250 60574157 60574183
    0xf0609020607060f050603010b01020718060f030c0f0603090506160512010e07020f120306040c0504080303040818012d140408070303031407020d1b02030f0105090f01091e05 76
    0x6903101c2d914908440107100c6044006020317842c000110b401030034144954070740c4200680080c05942d04241c95131100c490500a00044541c8505011502d40e140040540045204070203c480300383c05c00c0310740000c0034240d4104030105442c040b950408241d0001c1c500d500518080c40448440403100c0044509100e94008404ac003000000005005043c001055103d01c600e9401d85c3ea41083c60882940c40b41c50032400507081100c14400f01e401841c0592003540c5542e66030038240e28103640e03405014115002240e0039584080c0110390004402c0c801c0d0040d0b1041c0c0740c24a803995140c1789401c400580c4422160140b500780c01c4441e034281e040e40c050340000c0c4610500c07405003501c030359030740340d02a546041030b01080340080e00348039484518000c1c81000d140034422640181c540c860881c68200c880d500461189013080d500440c1440c017584040c001c502500c10780c0342c004940d42c42c3c0001518a088071550403190640e00d000940300c08076140c001c48925090840d1a1094074500c01e0400600e4410980408 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 60576657 1250 60575407 60575419
    0x7021201021308010b12030d0b010903150c030507030207050a0b09010b0a0e090d11070b0d11030109150e0903121008150907060305070806040e01110307110f0105130f060902 76
    0x31856000c1d410b480c840450700c00e10024805a6515001d02c40031441e201041000390307000740b20079103481001d60405902020b040c50490301107980c0751280c440313038800c030780000c014035948030940d0010540c1405003035448040c5d41020740c64503030180e03500d07592421440707030140c1004c4400d00400c10300c80b8290881d02c06000001d141c40c8007980c850030411105039050320041d8080c03040c1c0f80d8602c0583e005910b0f07041039860440c058601c07180b50007100da81d40c0e444000207130151507450710360034000b84085010b9406492086400110788000310117040503290350b030300403166030084c035400c120180e20000200c40d07030f40d120885015001d4031002260103051205400003d590700801000030000c80300b441013944a002d0304011940c1080c2d03140340940172140152004400180701400080d41420141c101ca070074001440d000040c0201074141a0100d80c0040c0c814000041458122446850b810010b007080c02c245600200024140300e0502100c0c518540310007840c10707204091840a0080c0e984c001c0b0840743e005404 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 60577907 1250 60576657 60576667
    0x504060c02012c0901120b040b190603080d050601030605090a0908071a19020a23130b090310020405030703170d0f020304140606030a0201030e120708040305060609040305030c0702120102 82
    0x500d109150f40c0f030301c02c940602c814a000155180c01000d1110038140c000c0d503038030314545403070f2209102c0c00e000410007594403010064000000e000da2080da4025800303041c6403501e4041c030411078000d55038064402ca0400d42046400c0c070156031201e86140d0040000000080c40b010342d898812002c0c05440b4000e08030a101e10501c480c03090100700554070400340005840300051803030b000d0400300d007e400e41007030009071905065034206044003510f00b2040c170821001c50030072510346d40b41181302c180b540104645072000f080300f44050508011403503d10131524400d41c1000e0901021940c0c58485220242480b610050b4002c00501c441c01218448082454140080e10151049001a50080d98212071a050140340500c40303030808103c107801980b005000e0400f500c0c050300110003525050846c64090f0080c0500c00701c4002000c00189204d52017426059240d518504180d400e0420052007a4051440344042000280c0e10004881e8403002401d1540c3d11080300f800031501c6164209142d0200390304c0016 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 60579157 1250 60577907 60577967
    0x6030204060e16110601060507110d0f0c0b0c03030c07030314070e1509090a050a06051c06050109060501050304060f0207021e040b0105090f010c020409210e030105070504060c0201 79
    0x300c01441940c02d1503140e0140b800451086944130710741642c180302a000000103001041c42000201a91400b803503940d0303504c520000c000340b02d40c0c1d0098800c4928a040844110070030031286000c000a0517848206801d00c1040030003a03449202c000c007031102101000404a08050295202420718441c40100c004980b0b4482005072403035424480151084165045203280044400101e03058007001500304442510750400c011b01400c00a8142804c0c039840d40c00101711501e03444541c8000740c082c01128042d05070917043ca00d0440700107800603050941441d00606c01660800b00316500716034010300009074080d062208000074051075200960010f00d4581c1c1d1004103a1f140d120454000c01101d0401064090200642c0c15100b07150a242d000a022a140d015030760184241405080c000351001c80c085005603a48100110035628007004c0c01c3d90005903258550b0f2100e104540614154000c02040c20001da015219014610801040001d4040742e0002c6900c83c210b50940c045a59101d82c8030492484 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 60580407 1250 60579157 60579179
    0x10e07080c03010204050a03030e120f0d14031506071a011401030b040509070618030602070503030907060e060306040e19030e120c090103020904140f061501170a0506040603020406 79
    0x842440c0c00391190701d10300300c0d8529040c4204c80880700c00602c0011603a1a40d0307001d40c1c0b9801120700181d4445c805503448040c9400c20300035404e03c0341e0580050950b01e400540040c114420790b40072080522001d00c00c0262202e102445103c03842d0702102e000340c46607140e00d040b0600e60351603916100071844c5000005068400d010b81890a400243c0b8188174484000007880115203080b00d04014503880030904002c098020f0005407030030603283c20105075250300d9844801c00d0f41c0c055141224140d00000070010422018454200a00742900e0080b021480203000604503020140c0302c0707481074ed61418105000001046070807121008940801c0c48003656080150006c404120024000c001e4100c549206000c0403c05140c150030060420200c4d90a603024031415a0000b40b04a9100322000600b1710b051500b00b01028048586000030082440c2c45001030a007155450764031818408130a00d61040704143c0e0255030b03885130750720000040c1031ba00c40000030003820503a84041c0d0003501c0c08101180103811b035 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 60581657 1250 60580407 60580409
    0x702030f0709090c0501020a050c011b0501091a063304080a0309150e150703030207020613031208060618041803030501031703130807081308010f05060306070f110a05010e07 76
    0x10002001245e58aa005a03140d002d60b4100070a950000c0c80c40704c42030742c0640c1c902c0149030502c00000311680815540c0d6401c4039581041551a0441a6060645c0d05c04550080383c0c00003081da07080090010305805950f400003002c0745480d10046101020074000c0340c1c0e4095030000e0145070219240f0304401d04010b481c05c411030003107880380810030700c4582000780148005502d25001a2a08441e0b091803078180c8800d0b00801c0048040640030842a005692244090010f01d4900e4010034035070f0386180381101451650030b821400b070141e000100103459035040241ca204010203030055112100c024009030043c1a16544400d14a90342440c42d424190b141d8410360589210701149025030070824000302d00c502086680501810415100c08006405030024200091083e600c1a040000c40c580e006070060507034105a0b600ea40d00c0c01c81000b418600d00480d074110303c2c141c01034405801c040c100101350f0191450000180090100e111036003440c10022202c42a4010008114074500220030355218026 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 60582907 1250 60581657 60581663
    0x5070204051e182e060e0901140708010303080406060803030c0a1b05030702060a05090904060b0f040605210a140d140a080a0f0b0a03050601150519050702030f070909 73
    0x2118000070003480107408031024010034035005103800d044030503590004c040d1341c500c51320b40302441c540c01812010f040d0140340050884040409014030346a071103542141c101960191a400e9541c0502000c40c0e00102c01034192a010b192001d6a543c40341080c1015240c030341d11190b460301c000403c20101c1c543c504060141c00099075541070710203400b208990240b401025003e0300e5500f00300701c07600052030400000e001000241c100282080b01650014403245001c60f4140c41c113039200c402140c034602d04992003099a490450f41000766900f0200860a00c0c0a44c0e60b803402c5520358182041070741402004110791003a4001e20140306030180c00b0300c041d103d6010700782000228098280800001c028001a20500542d0340e8039040190368590070100500b6070030050700180c950340c3c440c81c0c0c280d41b506c03510b00e00030318003030002088154901840740b1030f04080c9956203810454240310211540c4900340342481d10741c0051a00c40d031100c800703000080c11b1211013070076007030170b4030078600005000c0303e0580044034500c0c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 60584157 1250 60582907 60582961
    0xa02030106031508070b03071101060608010f09020a0c11030709090c081501140904030c0b07020d02060a0902010909090615150206070302190305071806030e07140102030a0507030507020405 83
    0x6a020f000010201c5000b000d400d0380001c5410b03c40800320001440c0e00107100d19010f9003400204a0550031078005401c80c5000640c0640140241502c5002d6031009140c0190110714026000c3c0e1b00505082e08030300001d041103000c03c2d58035101e940070080305010b0910b9144c2003010b41c1c041c0c5401354070600d0600c24003040b40600c1d4494440707a0f1700844118121741c0030310b00404182894004120340c5c1400203000310140082c083c0007401090500e44103520941c008c0d0003c103502200008041d241902c001d010003640c80c18030307075003000607603100041104550400c2c80128413600c02d49810b0006d441a070400642c00b130120704001030000081c0c5910306101405030241e80b00c6444030301c401ca003603201c3c5001d444003c0d80c1c004152840c1c28400d50106a1012541c508004509507041c56008099043d070300200009444540903c680401807203448028402c424284900c0000c00b00041d40b03c0c0110315540c001c0c4900441c0740401c1c0750081c021175500030f90042040200d85030001e420301d0030040503000307492800 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 60585407 1250 60584157 60584171
    0x703060e1c03150312030504030314100603051504050702150906060904020d0201121a03010b06120106140403020604090f050a0b031b03101b0210110a11150a0203010603 74
    0x108042801034290286001c4244216000c2005602a02681d5080d1030448a0014004081000c005004c03440901d903640216050a181c01d0082c02d80c0c180a20100a0314000c01c1031180081c0f901e8107840480c1c1c5503040114590341e4020381406003400d036410058210781800100007250b41d010071001010b0224002880b01a00c030484420f5640604a071407e40203070303148020a01500d05012600301c174a00c1450f0000d1318040c1d4900820a0314083d194030310030504000b201c0300d100e00c0c0a00482d00542c00c15201c1e90b09101007104015041103062107004c0c1404038142854516000d58000c9502460300034000c83d030b031560380305110310003482c041030a44102d80c035110102d82e016a141c0550070910314018010425414040a6000f02150940c1c4440d858407411a00e0102c6011602404002044858081400588580010f81481c3ea0200e02e44100703072034000044220b14400d800e0340c02c00441e03858980a8100c090014034a8a40d50010303200704010110104409204a6002036060302c1c01590140060 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 60586657 1250 60585407 60585431
    0x1030317070e011b02030109060605150702060306040e07030807051609090c060809150108010515090709120305071407060f030b0603060603100506030414060c180904081b070306 78
    0x5400381c80c0140007941403034026803558031036500007020b1051088040300e0700c0d545600103821983e1000e401c0300d401d501d45400308000e140c007032007880701c0c03810405c0882e1510788035a0018200e444010702ca1403049076910600156814104150400303141e000c2e41d00d40e520603150074030355610750100c400e004078071002070b001080e08851030069480341d60b80188c4035405203003824016124a83e0003801b10b40a8451580184441d00c01750312014000d00305440009890b003046003d81e2859100d60b01d1550107880c58409000640d41d2100a0008803024540007580c400749524080300c052007090000b510507444061003044801010801c502100d9007503d43d81d09104083e442a0180e40c03a455110f0b9010006000007182030900340d00070361780f21401018120045c3e0304c40e4001416030300169400d50b1160704041341085e18101c1040410f4100307150042c401d0030082000f510807600e8241c060034501456462011504105068040e00c014a0303040e130315a01540325001c4000c3d650b42d0144020b0311001e003040000482 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 60587907 1250 60586657 60586697
    0xe03010b0a060e0d060e0d030e0c10090902070203031902030d0501080c151617040608010b03010f0302040209130c0c170a090608090312010e06010809070b0307030b03010221010303 79
    0x40700c549071101e8080030050804c00004c1840300009861941d120003450300f20050034803010800c910140c40c0010074060011001d4680381c8040b0300309000710032140d643d0a5040d040011f0800b190b10007100560707100307014400320b030444c020180c0c8605081d0742c49c2d0864450360340110291507458881002000303141c1e40e0f12006950340341443e29864015100366640e0120445440040039143c040030340500241030645e50b03401c0710315101840036000030000328042c404690b000380c440b4010002c5051032811541003d80b030003004521440000e200c1c41d800148884c1b107886013100ca208503003131100c00f0405c030400104082c01c0c00e030000d64116945050400b07101c41410040703041e903508440310b540b038003040384c10450142c942c0d94002d400c0c800d0a100c10f01c8403441082c204030016018041180308160141000c10025204141c050700d4800d0640040c0c2e07040c01034016a030141c9600210516011813070704001c03c01301340240308644925a0104840052404c8409607a80780c604a030f104c0e640f4009070910340101c2002c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 60589157 1250 60587907 60587909
    0xb070b070201060b1b0a2a0608010605180d0b0109020408010f1104030b100b07150b030102070515060406030b0901060806100f06200f01060f0b09010504030f140a030e03010b0a 77
    0x1035958140b00b240038034046469140070000d8000205c0b4201c46090316111468000007013501f00078020b06814a1000c0d551881c0c1c0002016107050000e11941808070180503401041c03207203a105010350194007003d40d00e4480c58140943c000c5081d40c42940c44460b070b40045d50040c058110158281041100000142d10510505d000c8581026043c2811503460051002c40542024a0068151804155118014010101c1300e01c51001c0c0d0208010610a0805803004c80508030310a91043c003211010a0010548403441000226050480e030b8400c00098010704141d00041c11000315901048540c1405510400a5030401030403250709039140b50020642e02454010040501d00800080000034020756800d80100c6030320230550320b031004010b1801d19149049100720180d039150001000140007140c94440604260116586000408000600700d482144070041082da865039166041c0a80c442e000b0740301803051002e4504284150800031b04640400701501c0c443e500c0c14003207254910b440d0100074 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 60590407 1250 60589157 60589169
    0xa060212030a11040b0d020702100e0112050903040906030b0f01050405010506070803090a06090308061002010509031204050a050601030510061d01180f050903070312060503060612010212010b070b07020106 90
    0x5450756440000b074030050125280011055082444003080703000c0300300c000d06801c01c0041d20040e110400ba004010301c01c4807120b0000240100d800111070282d074001005a4804a250b001240507250745410703500d58802c2d980030350103081c501300022041002c8100d10328040c522a400303d0503940d03260003c1000300e520a10580b1760006042100c5000140d1140246900031500016101c460900340c55001c15618410030413400035017a441049401e2400c16103140400d00240f00801092500111043d1b07070748100b000200001e000f202c0002c0422a04100b80c0c1c207404d40c0001070340c945507942e1501a17643c0c01c038600e49444a030300384400030070601c1c1110044d0f08449440310120545901c3c0402c440210800d402c10202d04e0707505c69080a260010034090540118800001103903a038006040c02464540a0300b900d0111906000e8104166900001d0050304101c2c1194800f000c0b11448007100d0080c81621380072048206840d000040d110003050143c00c0450140010906554410100324202c2c1c1c0a40141 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 60591657 1250 60590407 60590443
    0x114070c020108040606030b010b03060306091b12030408120c0d0c020f040b0d020432011a0a0915030203010501030f09030c06020f0915070201020c03060c03040303020d0f0510050a0602 81
    0x4200507603c101070903a00907004100020b07030f10740c40b6220301310884000d0f0414083c3c031400006001c0e450800b0000c90740c0c003642c9080940700007294456074003400d02844180c90b03c110380c10302000c07030040401e1048500904081c0104c1d0708a400c0c0c803610034503503000321000c102c09000354400d144440c0d0048200e00300c103039030042c40c2ca142d40b000c9008000c01814424045a0008850324070100140c81e140700c4ca429003044822a26117020082840148404001d520340e446002590010000e60b810091203003411545800031070344a5810b0941101c00019551107001c0c2e158034080d1008800341c01d580158142c0e002a6006c1c00181109201070b0255240b0b03840c000c001030001c446071004900164007500540e41100450380c641380d03e42d000102c1c0d0110b00040c04800840010b081021983c040003a0989101c00350041c0c89903240048400c141804010005030525030000f580c4600380d19542e00143c44130012010401903424800b10fa0325110040f8000c56000d4403c005000c90010b00005144003100400060 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 60592907 1250 60591657 60591677
    0x1b06101401080c190507061e0c032a020102090d0605040c05100f030e120d050a1503080a03090201090e040b040b011a0f13080a080d061413051302030d11011407 70
    0x25a44c2d88440c412804003000410b100c0341c000103001d0b000c0d0020040c00103400071100d032883d01e1070004480401070300f2742c245450101e0300f02c000002049040e00e000b204101c1c12a10380c0c03481c03000f070740681300360340070287d10086200c42d01d01000f200390700180c007a50160202e408141d86071010301903000d21429941c40807130440c60000c6500da00c641c004580000b405001e46410000c0380010062640002d03036070315403c0303880300d007000700715507444c844da038118400c840c0710002c124910b0311400828401c503501e40d410503440d1241502564020150309004001d14141a00545030604103100720a40540c0c04032140d1110344000134001404403c1c00384e142546200c582c2c9095502c074640d592070b50101044050154803520001081d01c0b040c03000020080c0a50003403079031040300c05c034610110b40740c5800c8000c10b00782c50b0080c01d800707071582d8a00030355200380311200041980f50311207600c00411948500075890310400300b03141d00d21a4003004a10789841040000c1c05101c1044005a80080c1d0458900e00003920303d070070f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 60594157 1250 60592907 60592927
    0x1391205071e1a01090e06090102090105030106050a03140a0603050d020f0606061303050303101d04050703031407020907020d090905090303060120070306020a141e1b06101401080c 79
    0x81c009001440386100300c000c030358156100841c1007803d0340b2403001d0544d07885255060b25070a01030356908c000300000031807030034644100180440c001805020200400403660010403030007a480303089108071402d01c128840c542007005070081c0070240412990360003070b040078080060001a40095a482420113001c00e99034440900c0b0041d005108a0700035182014030001c086030703090000b940902c141c81c0c151000c16041020384290303512601e14054440348070030100404200b0100301201a69414908081c05c0b544c0d020800d1143d0064040195015200b0820711914540016683c002080035889050324566507080c0101103402c101d07a010007941080000540540c03207a20a0920304c030b4000a190301d070062600d5514a410000d8108440c810390004401c03210a0700188092403c144001c1c4003841c00c4191008865521024070741e1060318800426400140c8061a40045626a20301c2c03c0340c00b249402d8407010b00c900241c1c85003000900300040c1028440d4400e802040c800c0d542401058907000d8841 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 60595407 1250 60594157 60594203
    0x60c0a110102010902060c06150306071403060109091503020913020d080306120607020309030115080c0d0302030f070308040b060f06160303061203050a1e020a020139120507 76
    0xc0403840c11551381e0301d11880160360b220054000d10740803100518140c6000952440403c0034201e200388281e12a4042207545644000303520150306044001c16200d4072900c0041e6500743c0d060304420f9401d414922074220603000340b1b002e142102d000310341d541c4590306d03901c2c882d15400c0c1d40428065040803281481e2000701c2c031854010341d0040d401428000041c5e401101031802d04c101643c1c2c0b2001600b000942644a1400340a007458814206405140c2c1d02d05d48110a070f5a1100940014080c1c054039250b03409150003030041c0c1c2c0c400c82c501c0d0328032655228a45801415008100d6044804c030ba0500007140d6079042039080c8048002028003064039000c400b015100740028030340310403020141c0300d035000701d101c000310300384c80d030006110f5203995841b40b0b03075401c010f0400c41070111380c01d07442941e01d813041c44599070001d0121500b94080c01c000c00002071092081400308820030440d2000c0c0342d805094000c0b0340c0e0003184840d45134000c1428104030808160308480780e1141e210060881c0e2052060b034000b42c00390b0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 60596657 1250 60595407 60595433
    0x30906062b1112030c1e010b101809020a090602100501030503030c03100902040306050406140603060115020c1c050f07050609040e100507080a15290c07030f11060c0a 73
    0x10607503d141d0810030141c070700e15401765241664981140c8441001e102d9041c20301841c84400500900c42041e036000031030031508001d45400c1c104419404401440c60903584000003138600c40b0019541d0300311080001e0042c040c14410200103118800c46108d5801041c420141a41d0f40007014500e55102e80c204040180c0000c0d10020328080c81000015110400d48020402184181000304991906041c00400c9444500c6a02d403840100c07020042613640104040c0d05594a0342e00c03504410b0503442c01285056907468100d40c00034000400c81c2c038400046101603507094896030440e040608140c0007151980b40174440d40c1e030806414001d0410754603054101d106c50480001c111910b000102c1c008609964043e903840c00460720040c284024160503010382e02d0409503642d13504841515040c281d60380d6110a00b01c1c000108403004440d101003c881c02101c3e1704441103001c50390090380b84d0030140303812019038500315040308a03160034007041c0c1400e00c150313210b90507103030060240303800f40d5120f5140a100b0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 60597907 1250 60596657 60596659
    0x40504230f010903032306010f030515040e0304030227150402070b070306051903020105030402040c0c080c070e07090b0d0b01230301081513031803020402030906062b11 74
    0x40c2044926403040700344582c415260190380d010604420381030103180e000d0001500c1c2000061a40b081000c2642c100410901d040c0a503d40000c4555a41c2c05581c4051030350080141e11504200318220040300001c003070419070340200e80f002c01d9003001c0420340118503e0300181001e13004d0003c000a55908400e01d00844d002c40107400503203441103c0c0d41d079068829045070810042940c0303110521182c100746003001c40c500b5a503041e601d032140c2180c00203031840c04000c1c0020b11803510fa841e00800b143c441c42448020f140d104000d16203a0b0144000c40d92a0f252600408a41c109032000152220348941005002c036800d5560051520135104120005804c00c2480075061140381200140c0f0225200703000346800101d00c1c007207a16035050141d402c1c2869008000e007030ba44d207151014042502404036440305540c4d03260424005048408a03032418400a0707510280d881131021040000c860b6000c00c001d841b4000c11500d050240140d1141c0385035580382c1000c00804400c2d1203540200280305040c20b0090640 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 60599157 1250 60597907 60597913
    0x5090601060e030a080a031b0806031b0312030f240d030f140d0b240415090e0f010620060a020906130f0317190806010509040903020f070504050423 65
    0x294681c2030195006c0310b0001d0020350340d80d10107000c2e851030b50b494005240d01ca240c903454906003040001d640729034540a441c00401220784100302c940d8100034265402d87c02c908201d8613440e141008082000d4200d411083c20380c001c0002c4441d848202041000d000c00c010024030801e4080c0d2011500440114184824402610180b255804882c00600a0300e100380d41e010800309880005c1c032203a04160350216032840c0300c400e045003001c0020300c03d4505444103028010328230028030404483c00f4541b80d100c104400007003024000045000c5200c541614001e4442110300307960890a00c0d401e921312030804005400202c0801c410038401c0d0014030050900408003800d000c40901f2940180750560311445006ca21400c041040041c9a00402c9131030400003200781c1802040300c10303111507662540400080116900006049a008505407440304030302410070020850709107800703940d1f00a40f407494400c1e8461660006140e01c0c1a0103030358840e81c0c0c0030500745141e00c040010408540d1280b230071a85940 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 60600407 1250 60599157 60599173
    0x106060917150411150c190f0b0a0203011505071101050a0c02090906040606060503070c02040902010903210e2e0207031202071a0702030312070306090e0303160305090601060e03 78
    0x10903800302d40380250b014200c62000d00c0340b81800c00145a86144110210400a11035000c90040124045d8041074082c0e0030040e5141443c501103c921340c2e64180288411166401e001c640715a41e0702a40c10380d0000c4044002814801509580500520400800342200c20140c1c3c14554400d4002c0c20b461007030350409030450001640040c5c0703105011580a007407036202c5420032040c42020b0213604024a101c1c10805d00d18109148001d0800611480203030043d40c03219003100459204140400c0256000011040b450301040b2a6890080101d099140000e271b031f018490b1080c2c40c040720390300301e603d0341e015002c0e21111002000305000702003114060305500401c81c001010461409111300d41a00950203005c401e030401111540f44140140d09010f0300d98207000490060702c0001c110360050303070740369103840c02c5645d1018101c002c3c103402d4008807049418603c0082c0c0e024030020295015203020b0703900f0a04000300901c01c808459045929842544c0b1510040042d140143c0c90701030032980144c20f8503410 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 60601657 1250 60600407 60600433
    0x90b0603061909020c030c071502060a051906080d0e010203040b1b1207030903060513020607060b0a0803040609080601170a030804061104060c0b06090c0f0c0a020a0306021b0106060917 81
    0x20b8105c80c1d40202d043d0400100240d14071000d00541010300051141c08111001081c0002d503151401400f00c1d04180e5150f0200e00c207204620a00c1c0706405549600340300e85600d07684a81c0c0c4a02e00c3c101c1d01e0000c00c0800c0080d003582e60001c400c0d0ba06646d00c50b1600350610030030059148031864031084aa1090290b000703003245030346405d0b0044c0705003402070b00c4840700c1c41e1039454914100c9000410000e2040c0c1c07141034080069540d0011644013039004100841c203054010002000c50126902100c901d200015000030801c0d00051040100d40341c3c40251145030303917901c0507800941262407000040e508426a600d00080c000c840668000d8001c0c0000a00c0e040e010000029980c0f00c0c0d04000f01107111010200c1c10003000d00c0107550b0203101624400154140000710a940b030048004241e1440e40205441c0e4060320104562140d0a07001451000c2c0b00b41d490800343d0096104040c80c14110f01e0300c1215903801da005018210403101c081c0c1c0d403050850301e0807510800c14104800a24260701810b0410a40c03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 60602907 1250 60601657 60601661
    0x1216081605190c0209100509040609050f06090709140c07060207080f1c0e03090307050f1201050a060e060105070507050603060406050907030b040b010c0b130614010e10090b0603061909 81
    0xb01c0c5501c0d25404101e1045004001e40000010550070501031045410320090b200e600d0019040f55001d40c01091130f044618246092030008070955140e4401c001c00c00c065040001540070449030114010014812002268100c4100071542000d86060402c02c150002d60668000c0c040b290041902d241408850000d00342540d000c201100c023000300f0080c000c0020007640c41180c1200d0450b000461a014072000840d032605800c0c8034040c07041c03031010000c24160711000344505084403e0b900802c00c51810380c00d03810040c9450700424604007000c00025410b940503400300d5004da50468000d2000034034100410486600c0248801d400c29280c81c1d0000f0a6180d1481083c010240354602180d102d00410600084131030300c1c11018100180d01c0b01943c08154189003c903005400817000d4072034241d041c20460041c051340060384852280c084000160101c81c5085140034203403084005002c555501c00c00340607681101c44842d4056402c20124000303140142d01c0001e44800201c00b200074507a00d01e040c0003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 60604157 1250 60602907 60602947
    0xa030209030304080d0f0503040f0f05070909080304060c0206010b0421021c022d0402280c0c0602010507080a0b12030408010c09081b1302090a06051216081605 70
    0x10840d4000c05010003d20707040442d06e04c1d104410301d41682985410707268241c203886c6089000e40b414000840328014000300b17011071005065000414085051390789020710041e8800c0318180c80241c50030440000c903902c041095812624044001411f243c205080580402c042040080c04921034241443c01a1908105c09401440201114210f42d2450041c42540c10166440901d04812096200082aa206484010403105031001070320760114602603948a8200600b600105007581034903d08a988000300c3c2400e58400c1800110033590740304264207a8501380c840e44089a0200001882440c4980c044040b841d00245980046000d2001e154110b0f03205810600c602e075140c1b40c807102d12680204145004088002c001c05503a07014035461404607039113985d250300c94827032500c41d5014156582c050703808018005001030021980c0e00800f9000d80d02102180106029070000a0080d01909400303441100c8035031180d0350f060360b80c0d40031890783c0c807048804a005e01009018080d030642e42011402 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 60605407 1250 60604157 60604169
    0x6031e071b061a0d0201120e0a02120a021c050c040b0102160603020a0e010e0f090c07080f0a110d080c0a020718050105121207020103020d0f0c03050a0f110702060a030209030304 78
    0x3094400c085903012400c80203c0c040d030068a048024100507680701c26428084000807030002500b9a140c21001d003080030401d07005e0340c01100c42543e0a514403001c2142100948200d0fa202507500c0d000355400b44030304810030040e100d60803c20030b140c10303420643c01a40920105105403110400d8215138000e40d204150440d5002950209078041070a4102030ba5800c039110900b0031140769010400001c0914081d801418083c80101001c034500e0860f410643d8902540203858544034205030309810310320b422040c500f000103030081c1c10408405001040d40c03000c0d02000c0d038440c0700300c0c2d03141c1c00400b45541c080d2110404603c0b03480d40015201e6104440e04035050920100810a545060108001d02c440c000e44014983c000703900310301c00d142100f07048408056082c20051380320080481000f009000c9490762401c050f04000d1544450351340340d03000358418605500200170030480511b401003110078445568000c41006c011500141c5000310252000b01400d04c0d025180c103440741c000c01d017990840d0b4400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 60606657 1250 60605407 60605411
    0x9040c0c0b070c0f060b01030e0f01090b1003050a030305060310020711030c060a080a09020102070e090105071211041205030706090803010f0602010c09030f050f03040b040504050606031e071b06 85
    0xa1001c1103800c12105801c00440e00d81964498181d4541408001840340010800d566926580b0607990098201d070314903034110b609030340c10111038083c0c807800b800d03204008462003456540042c20001c524549038041c0c0e81c2000c01480118802d41c1c00390000c08000d03006641c58483c070300c00d080d01c010f0540014800d4602c40c0e01c442d088000c00400303141c40c120300c12110611038602400355203050b42d80030100303e40c042d10482010a2160039800141d0a003462a004a240858060104035a60005401c040d0090406981e9680400100040c1da41206e116555218801508000800c000d002d20410f41c1030305401034047d00e01e000703503543c3d0308012140360302404c40742651b01000400010090400ca00020f10041c0001e125441800314014404555130100402c0f80b03000b5150f00c0180201003285181e038041e038900710303681d4540b030b80107625407908076108081c030aa0800d00028040e0405d402941c1c050b101c0300c0e500c45429400d0402c1e50300d02000052200040182c0d4440c80c55446c1900324120f15128025200 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 60607907 1250 60606657 60606677
    0x3020c0901080a020f040203060105160f0f0b06030d09030b011401090b03010e090f01050103050c090c0c120301090e0304030c050616060204061805121002030705040e0a02040617040305040306090809040c 89
    0x18040140120320506206e60704c184100403159030400121090a82003003044149505689408141c04031001d40150091282241e00c408221a02000c14000c050440c01c0707411048000004540030909404014410309040004209045628028124500f0305040006540e610b558403803800350002d900401000b43c3d02804d000e00340301c040c08200308901040b0028005036056498075941e03003a4449003540291044000100c0c02c082c00300c180e44120008006480c42e510052680600540081c040c0240c01031400442d42c1e85000000308680469034046501401d40d0319200410815401c0614000c001c92540f50241001544030310041001d014036483c2c41c0f00c007500022200d4100d440c40e0304641c2c01000a14520031820310f0024401c04000c1c101000503035179907990762045405000350f5020041c0281d850082c0301802c0400e401400503100c2e541d641e00d040043e440b400f203103855420744001e00130800404c0140045045900048200ba0084030103034503014120022400b100d450840190004035003600f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 60609157 1250 60607907 60607909
    0x20f0a0b06090c0301150e1807020109020102070f030b0c030403090b041805010f0b12091908030615040b04062a03031a0303040503150a1103091501120c050d03020c0901080a02 77
    0x8081c3d4208810500d064215030415042124042110340720605000300100505082d6581d49071408618040012030769003414614006070103000760800490140c040e0380f101180d544000080746080300d030008819007030390f203e00740d10395081da01c05002a01008038056011980f50086c000500042980614040d054004800c1881c2106c0c0d0681045415005110041100501580c25505d10041c00000c0e00712940710b40021600d440300c040309100e01c2c9000e0005040900440c4c01c05140300d0703201510499804452140203074054030030743c0a02c000e074a80a10090112900c1404400082c000d40c98117100e0b25060900d2808520900304801c40009803543c0e46e85404a03c035003522540d9100c203500940c241070401d000240c4958541a4000c0300790388040020b00c1d450000c0d04815140840e40c82d109641e0306203244801d444042c0d514510303c0f10502d2100024440221300e42c0203520f02d401010300314140c0e041108214419242200030b81c1184038101542125076a210510b50080690f0301c000c01c500d41e5584 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 60610407 1250 60609157 60609169
    0xa08030106030c0306030b06010302090a05120106090b120601060f0908150a0e0a0215070501020405040f0207020909070b040e09030c06070906110102030c04050f0102340506070507060807020f0a0b06 87
    0x100f1150101414200200001941c5c204802c4e0410802d08016032580080804100d40400941c4095071144c0e0740462070300a8803040d8024420740e170303440d00b084c00790558501c1817001e02d041440e221b6495901100040181c103109803110000d104aa00c0c1071071183c1d0356108407902e0320402c8088406e82c18002000c2c050303040c0191054400c0031821002a04044680b600054030a2801d000c0820100d0070002c1d0000800500394122000340c0b074018010805108104c1d81c0b00025000500100e006142810104003420310005007002180c1144440700c0c60142407200c000390040c005065191240300074405645041001e2110b0b5200d41c54a54801800310324007880100110b0600e54508036691041003800100303a000030850382035a80136182e86d03c4400c00d41004078900f282201040c06002101c9005074564044010031605100d08241c8580880340c4581c00c01c0100d110350742c0001c2c0683e0210404101c4280260940f5502040c0d60050b0f40d04000d02e90111410060f401104545a003044030800001e443c0032 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 60611513 1106 60610407 60610421
    0x80105040b0105130810050606030f010308090105040302180601030516080408181005070605060103020f0706091e05240105010912061d060405070e0601020307060b120a0803010603 79
    0x5d90203860310751010290100d179184c01c10011824a2500c2420f0364000d001170b2049610756480c640c0c07040140d5111071413043c1442014800080503940d090fa24003224009013201c0c12845c0343c048001001c591004007190000d411074003d035100d15912101156010381d01055560355000d10790301c030b0000d0701240741405030710055810100401d560b0107400740030b2013413042c03006000d2503d07605e00640907070040c02ca4000111006200305804a00e0075000401b4080c040c460181c3c2c88050040c0340607880c281c8007015112036102c2d401d007410b800040341c01109800c0c070200e50031301d0550614000070b02007071607446824080400700c41804184007075540403243d040b00403441016001d090002c029180c2100f124182c0300c80c0036800c00041c41e00e078050411480392301d05034041c5150a0280c0e5030940244640304140f40c0008030766012405819040108204147c02040c23250703141d40c5008001010340364a = true := by decide +kernel

theorem cover : BRFrame.Cov 60431657 60611513 := by
  have h0 := BRFrame.cov_init 60431657
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60431657 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 60431657 ≤ n) (h2 : n < 60611513) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
