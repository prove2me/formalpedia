-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1681
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:12:00.659987+00:00
-- url     : https://prove2.me/submissions/e672109b-1c92-4241-9225-da9e9eb13490

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 302158273 ≤ n < 302338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 302159523 1250 302158273 302158313
    0x6050c0d0e03100c020c0a030b06010f08160c0c1d04060e010203060a090b03030c0118050111160303270f0b060d0201080f09010902100503040c091803110c1903 70
    0x2403424080109070f0b92058002d04689140d5520390291900d0f000704030044061a00a01036a00e0301d450b4501040205800e650319408119600031100300c483c00f4919003482410b546e2140b43d105138410b0b4080398100c2303483c6010b85550b40282008903002044800f01c5281540b1110300b08024182440c02d81304450032a4800c50043e48180140321903a6615030b551000c852500c8804150341c06101c000034114440c804040103158680380f00f211501e00242980d41420340520000c221005180e03442e1078981c41081d01d0102c1c0964080d250b000000c3c060307131018840d2200f610301503241c8110003e1900401aa5403400d65015451140840410107941603644d07201900703070b50b440d502950690010f005240f002e001141c85614900010744020f038254401c0d820075030000c4c000d860001c041500074119a0007aa410780c0c06e0303860300d00007043c0301d4014040c01d0006460b2001100d40240182c800f00c51072207131490075001c03030300600c0c5142440d0354070341030380d85012005a0242d070082851807419038402510b285503640 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 302160773 1250 302159523 302159537
    0xc0915050a1d0403110f01090212010606270b04080c130c020307021e0604150905040b01050a030f0f0e100506030604210207081c020d020c03120c01020c010606050c0d 73
    0x4110b4403000d4095564120900b0a10241caa40ca0191108000d500105034180b01d80001006140307815001625a503000761102c0410a4107024107a090741d03200c0c080c83c0c0202d61109240004180900e60510440844140300c40c035640e2106080d0086038406d6001c1c28140d4400118a200d602c1c00045440549003090310030401c01d0b10345c2d00c01948034021000301078450080e80c0140c80342c4611098030800c0301100248600e6407a0344605c10a441843c124001d00002500326001140030b007000d02ca505039440e41619018140b0ba4442402c4006d820f02500b268507043d00c9541503160400240183c0c9003180041020b0690211190b003200100c40e001810280300b60b000105100100340121000c2482004551a120106900349016850b2000582c00302c40b103407040304070a0031501e0316180c1c0d919000704540e0983d40e140040201c1242d480010301501c59158100a01114006600c90000c001e10140c11001504245500409a085821075413005010072000200342c1510601030100034018402403c142c6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 302162023 1250 302160773 302160779
    0x2040617060108010f140123040617091002030406090b01060e01022401210803040614090a241d01091205030907090c121b120e06040f0c030c0915050a 66
    0x29501d85c600380b0414080003801200f0794056480380c00381042d40c01c10840c0d0a4000160700c6a25003007640725204020014140c0e042d4102c0c404d500c0200c49005245a1000b00b4260032402d005000175803014008482e419561358440002460a513009402480309440c1c031000354078100c0001e41000d0526240d2840428000c3c8661205112800c107507055070281a04e01049000102d410b00b44004074020181038240040200001c001d4035404c0f40c1030030417a0002d10315940d01d600d03c8240e611005200c00402e11001490a001c20b61030301000c185610503031a074085048207240003c841c080e40c0c2e07070f86c22920356511030918000740495180941e1034408146011461845e2800099444801c2800f41e0340c0116113400e24955034501c121050403291b5440341c81000400880700c082f0f8000c904485174840450b02c0b1400c0390038006154422040c0c08003580010f041c4554442d0b440c42314406c2c0c100030450780c075101c0420110102e00c0306400c0d0000b90060800005180c06000303107141d0034803850750100b84581040d00042c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 302163273 1250 302162023 302162039
    0x50603010e0618010207200a09020306283203060615070c09020a030f0b0a0f030809240307020c060910230a0201020702040f060e1909060204061706010801 68
    0x7650f10a284410b01200c0b0f1001002030303806480b8410020740400c8040c480850f0506841c4028414084100c2c0d80082095a445401c81030340030848503294001544c540c207140f54013102c0d00b000000c0c6024480184455110907a0b84400c0d0140d07600020603500311554412004840b045100003490210000d10061406030005003c0c0c1d0101c0c100c6004d66003010a5000c1000030004c4001d01a00c44500e05544810766414000d00400401540880c007a0a101c96451142801d0700c032101922400c00000e5500c0d421912009640d0b880301002c950403080f24120b1075040025001c0c081c81c0c1904502c0c92641d45c2c1002100286404080e00090348a03000810124041d6501d0b900e1041d080d81490602e000e00d0b841041d45480080e02406200402110000f0034003c4036a043d80103012051080f00c00300103c020240011040307904a00582c8210204000420701c0b400c0030060486052610301d1000c03888100f9075a40700b040c0c0e041503100c0d2002c21002d40a4000702840039041c9688002c0070700c0c208101e58548a04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 302164523 1250 302163273 302163283
    0xb10020120040e01061b2003061608010506070206090a24080601020607110a021002030307090e16080912070c09050105031605040b01021524010c21050724050603010e 73
    0x1170501800416140100c0c0300c5d241d5200408100e401030603070740340a1180c010914445a440c02100c3c0f10f400340900180d0b082024458104c00400950b4414201da800e02043c4100340c0d11844007640e10820501c040096a5940450b02c4050040340e8602204000402d00b180c0da90301e0102c1485041c000440200406d45c0d03030000d51107034031501500c2e112501d0107000b80ca450805c2c0c0922406504401c00c0e0b40d4441000d0380000085004031400d6682841450f50740e44103d4094030300762010304917420780c3c40203807407030300d101300900c5400207900c406940c4170310004c4049500320741c081d81d0f0031207281520708820044204248541801041d0a45c00740c000b03c824181e0500d02e018150085600c12940c07041184110f03442080320b8445041840c0d052590790a00030741340980d100207105540d6210b102d4940407030b40c41d446580c904203403940c00600d40c4010031154455130360502118002204111003030003404085503480900b2413005440c0070710141c01c2d42c110341e00034003621001480c03180a40c1c10004841e20341e41c00000c0e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 302165773 1250 302164523 302164529
    0x2040b0d060b0307120b04020702061602120a0c0e04050c0a0305070315062d05060a0215010b090a140105070f0b100e0610030b120303011e0501090303120e010b10020120040e01 77
    0x1720000d500c803410b000040c0240070781c180c065000100811010f060f65200c40d14041040d00841d84142140b1501c1d00c215944c01c9040b2004008043c0c1070420031682d0001658560058811405e8450084095000c90811003542d4001c0c1d8507548211001c000344016000310106c00d0b124840c052200d142400030909080308090490f441111889a032200b1265a004603407001d4100103102c0c1d81d550303400c010000e654242601a55440303642d6200005484c144001c11a004550041e010300066445d02451545d44c000f000201c605002c0c0030450b8000091090120201252103044a01110b08124089606649050f0031007030001030380d03906000c070f02c1e40ea041c401540c1030420f00d0701040c9402180c001ca88500d03006040c00490307200120000c950f01c1000c00302010032682d545441082281d44000440d9040f0480c400500403860340f8411101242c05900802d1401c841003002041c0d6030842c03404074021080d20522940143d64418400010145408000800500d180002d030304140c2441c404c001006030600c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 302167023 1250 302165773 302165807
    0xb03011202130609020a110f0601080c0915030a290714070206040f03060606020f0607050414121006150507080412021504080c01030516200f0102040b0d060b0307 71
    0xe8501126882c50350400d101078000c43e00155242c5401b20700180c25050f012401c0c103020f02800e441460700c0100003070745138103e8005400602400c141d4805012440340c0c013800340009400203030f425080035107040000b01caa162286240c0f407006405031100034089001e24508407059201c00050000460340101c5a41041040d0507000359121f08038030006003a84030340ea102d82d4464100320800030600100e544060100d17a5941c0950303004000807408103460f03003002c90351a004142d0511042c403090b118001d201c100c02d0406491022074540d00b54040d45412050040e0380951900c640050041050301d1000140d1855181006814042c1c580d440071818007460041400b2070501c1d01c01d0505658802010030307180440c05101d02c0e607554403048090703110f0721400801804a8180f078003042640c9800300d074010b0624441e5449440402020415220030040c48000a6141c420400000103041c03080c4000c000030482868856038a1030200c1d50745081c0c540707a5012070746515051080050b5607401c1030061020032031a03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 302168273 1250 302167023 302167039
    0xa050603100509091005090d0c1104090f050d03060b0c030706020a09030804090b1507020f01030c030b1017060111061303020120090f0316060c081e0301030c0b03011202 74
    0x40c0541944901c640d10940e8042c0b4080c00b48140120042208540c420145006000d40c2c3d4416032420755400804022600147c107800000020a6102d101e12180703810040000c01c0c02d4a083d215010b41a68002c0140c03060740112020900164044c03140350300502c1c68800d210300306020341c4c10298684c0a04180945860780001c1d00c54213041c820644d0030091503000d407289890b43c0e110030404000f420b20250003030045041040d240d605c65822815122415030082200b20020b8500004501500445d54040c083c1502d49075051079683e244500080003500c1907032002105e030b0b080400208400c01c0540b125041c050510354400606201103284d41e8080c50620640c00d081000d454102d00500129001c0949007008401d009180301509006080a100c11a038444040544104050b150110407028034083d101d0040c00304210380c000d5007101e0910b40030300c0b074450400f2050001003503403d80f0a902103c0900000005100300f01803c05850040d00c850700b103541c01c0d0b40c149241c10b2081e034840c01020380b01c0c071300d4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 302169523 1250 302168273 302168281
    0x60f0605090a0e0714030912030c0c0c0a030f03030b010e0402180f060a0f0f0909051501020d0f0906030f1e0e100207050d210e010b0109050405040206040302120a080c16140a050603 79
    0x400c0020050121074123920996074580302c03112080c00c2e009200303004040e000b200ca903640c0c189800301024043c1c03034000c21301140c1c008895400390300900f8001d9486051044031a00c0281075503492010300b546946c0300c42039182084c4220100180301c011b000000e48610030501c0403000030b65220303c10b80d41250349810110f03004451000c0c00d903119005540562180b03803d0a0030044410703000740222007240b0080e000c81c0c0200c1150302c1e0555061309514030460000d0380e8800b040248500c40d400c60f40c0c000c220060300140c2c404c03c5140d00f040a103200624040c00315110132440209180030003110f01c40e034056100847c00d002c960340d103041c3c85400c0342c4500e0080043e8002c0310101002da09440ea00e095004081c1000512008000e0602a0407a2071609000c606403203400a194141409601d21542e401419585407605680c01c0000c0744680c428901c030a440b41450b140001100c42d002082c0c8075171340c100106402d03410440e003206907a000c1d401004e603800c908803914043d922244480002d80d2012164207440b07660b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 302170773 1250 302169523 302169541
    0x30e2a010c06020a03150501020c090f10030f0c0302030d08010e01030f1406040507030b0a0c1704050115270c050304122f0706110703031101060f0605090a0e071403 72
    0x5581000b4050390f01c001411180d19415512000002c0114074200c40103d6841005986440c7c3c00740d03600380c0041c40d400008450700d007815495540501c00d13030300245a003601c03622401c1c40403560030f00c211049076202c2800c0c815843e00b0041d01d00c0c0520f01c2d01d4610070301d40c18041300c2c612001040c80000d0240307403514084c0c000c1103400c8407a48020403103141100c00a10700b40c10b10942c4c400045c842a02c9042400010a00c0c840c030600400a4102540d201e411030341d0030180da004d000060040c0b050701d50b03541e41c0c2d4000d60340c404200034100041c9900710707010f0b4082188584041c0c1c078501031040810f02500c1d000c0e00c001d041d504002620703806504400c01207200345010202742c031041080d81a481c10541800c605c0900303074200c1002003940b055480c04407040a62036080944451081c1a5070146c50341c00a4402c10000f8410380e594503123448040000304006175240320038100c03244260032610200304081141c1e149400c0100e818002064252140b00e0325003405840a4180420b44400c0300301d8102c008000380f4910 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 302172023 1250 302170773 302170787
    0x1506011d01020a0605090a061a010f11030c1204080f0a02100503041406010b0a080a0b0312070c150c05160b09011b0b01060507050d0305010302361501030e2a01 70
    0x1a0403071414417040c94800d1515031550443c8204458992070580f070704543d6130300c054061841080603100d200003280380a03010b40c1c10410720b0010f00c055201c1040341070700d1039100748004400511b2012601d500c840c01d1036101e82c1030040580403010380b6403021481201690743c8954021089010b8100182e4944440c1000e0005a581441194107882450000180800441c005181d003440302d98503400c00e40c03208004071060b00c8140080580c160f1003903a0301e010301e103d0540209203161103410703001c01441d40c410039883c2f56640d940b070410206000424050500c54107029014040c40000a990046403c00080c040c060081c0c1440380d04008000040803024400d00b010320150799085032020250b036946500041642e07100b000c040b605801807403200c494440c000c0c068917060f258001e0142807280750701c2c5170b6003016070828118800d1100250501406441040402900919840307158640341400b200006d41a0b0b90b132005c20440d95401b0444610301408101c81c3c8408a4a01350380f4111900700350b1004035102 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 302173273 1250 302172023 302172043
    0x41a0702030f25080405041109030a020f0111060a050402270c0f07081305040e030f0a0309030504093809040206070503040308030c070b060f090f09160303030e1506011d0102 76
    0x99403803e0b90a801d0140c01005442114400c903014400751480c0031103007000780078074032030300c1e801d6405180600014940035003030f419100c4044c034082042d081c01501c0180340160aa45404185641718103020035420f00c07070090780e1500c0000840c0c00000405500910304c102005100d8440c0700d00c08181c0c400c4a00c00701003222003081d00070ac140d40d03d5201c10140089441e4443c40390603c2140303410410366007032001005456600045820150900780d80c2082a405030001c084120100b11080102041c504614850781e0200d481d01842c3c1c0c80003a440c00ea4031100402c0c4032510101d52440d0b4002071505a495400d041d61240c3d050700c81d262a0800c524216142d17004540008014220220030403505940e0503000d4031002d8000c1d44165115101c81050040c40c010b15591541c10184034400119451944441240c002e06520221101094903580202c0040003070382040f00025143e80d803000003240d080040c51254182066001c45d503041c40c074006000400d4169103059030700300d0200c0f08d481581c000d104960340 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 302174523 1250 302173273 302173327
    0x60d030207050d061d010e03030408070303061d090c01182702030c0703090608010311120705060a02010c02011b0f0f0512011d07320702060f03041a0702030f 69
    0x480180e25005003e003021700322010708800e03908080180000d050107007485400250021b14030b5511151201013240c1d119070381c190203043d251500000d8440141604208070207145813855000c1c140658030f2400c180303100300903038100201d038017150384e014460940c170700100e44211840d11500d400038419022552941c001d41900b07a4800b204026544e40b40e00d0080880612954038500c0507600c1d0102501c0a01013800080c0c5a040c0c000d20a01301410302d00790300580001c1041c202c5092035070307510003c0c0d02540200003000c0181d440d0700580c00195024011140f1448404000c44015240c41100030622981100b41200704241d0824002209000324119040d800d94080c2b801c0f581d41e150070240050041000e800e000c83c10707401001894072403107408141040003a005d11103030285004580302040c2040c64098052501041002d00010b0355440014601d041710004c1043e140c2c079081c10301004484400a56010b41da101c00e080151941d404000c42e01591064900c02e5110f101e150801650065413107071000b4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 302175773 1250 302174523 302174539
    0x3020c0a0507030b100909080405010c06020c1006140a0503030702012f07150305070818010f0f091707171b06131106070503190203090904140c060306010503060d03020705 75
    0x203220400702c01c40c1c8201c1c180c0e00da17016669600c43c413003000c451001d000a0180201400300b07010701c1d0300c29440a03080a00640000d81880713005103a03d810714800780c00c4102016601e100c10886800d481f0921039824908031164401e484c90480071907101e22400788000d04008181007024089203018062084510402c0c1101181d0102421003541d10a2103010700c102c075028901c02540118428040d403441403c195541c2c610341d0f20b50040325559140c2490703183d4a00d540b41c0c4140002d00f000e601c9149a40f880044001c6540015030601c615444907541416602c14010025038000c9140040c100c50300c050007808031592001800c000362108400300903075000707070700500060001c003120005402c210340303020305d0038903055403504401c21000e0b20400c90003c003c0d070820b11041c1040c4040309100c00c400c0c00680107891a01d616680001e4076081c0840d0212441030440b011400d10810400103124422001d44181d495801c1400000e050b50200408980c440c141100b5036408051081c440c040003000c020741000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 302177023 1250 302175773 302175779
    0x50a090b04121803020d020d0201021e070f0f060f08040503070f050c03010f050106140304061d0313060201110301030b1302040c050a080903090603010314011b0305070806010e060a03020c0a0507 85
    0x1516803144800032200140c1121586a140d40000100d00204c0e0750003001031403000051350900c4401c9070003090503815402090200030078480b080300082d1540950b1005000c0b041e00708060006502469007124105001508080c00047d40041070207802e80d1641c180381610355140d142c081d18602c210078000702602c03c0c0c1200c0104024000407a01c0c0505002c074020b1041050f803072040822102e007446020b0001e40d1048016549e006040010343e040750007000d0226810800c0b08240c618103144d244001d989a00c00500030b0010340c505440140940103920003071090300d1400501052600040c0805004102c44c04041606045d52000491010fa800740007801103995060300505107402aa4032800071501c2070700080c410303941c08422100108001040d031400c48c1d00350b442e80c0160300b070030701c0c4034064641d60f81c0b8401341d0141c403050300078650b40c0a03036a01040505d0100c1000346841c0000e0880c50500c00025140b18048c0d1b91807080d2000c41f0030358038005803640c40c141005807401c7e8040a003d000e0740200740b004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 302178273 1250 302177023 302177033
    0xe1902120103031b02010f0f0909060305030a110313180905100e0f0307120c030903170a0e09101505040e130303050606270a1e0509010902120a050a090b04 68
    0xd241200d000b91525040f1a80d2032003208094400510000d000070290340201948600890011142c00f983d45000c0c882a52a81c26074402c813081a08184c41c00d0380003083c221070059000440c2c0b800c0c0c80c14040a18200400d0030700c1c5d86200c102d60b025034401d000460200b49942609039201c0c000050b0000111a984d0b4104451013000300701c81da402c900c2c8c500540d1189008800000300721510a5807091340d00b11400c600c01004c40f8500701c050012000c10282080020102d450365610304148800c0400e419502c2d00303400009000494442e00d07141c007621281040000201c00c136006030003150402192542680c1112000701ea82d807040b43c0051100711017040038854041c5070307681c10140981c400d480070000c03507c829040000300e0190f541d104100b01101c4a80c40c941c001800350902c1c031000e0107099aa005501c84584107803a030070015600c81c00c11074041c401c00ca00d250010884e0300501d4125400c618005650811215066004180090341c1d40c4400104078100070303503844188015000300d0001e034a41820f02d04 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 302179523 1250 302178273 302178307
    0x6090b07080103050d0e01020a081e041d060d03020a0b0901060f08070801050721020c0c06190f11070e150a080307030807080f13020409021c0309080f070e1902 70
    0x100780e5051003005400001703180500b0f0b481030f009405800400e03100b00b00382d803007500d41e51003c1903240c00c41d642404080711303500c076640140c07000e48010442c4240b003420f4900c1c60100b1140c02002c840c400ca502840c40c1c00070a401141d4940303074136007019400c0e00547d110940b240c09801c15074401211081c0025002560b000701040c2c0c6400d4031240002880076450b0080c04842c1c2d0344580c1400e803245091481701c862000e040fa070040c0701c0711050700c0c107488640e003002000816981140c6440c4d0603810003074034444441030340f00e00c01c4100115141045840d01c2d10312401655a4081801112a40325800c000b05090790520f04c9829080c40d0000c00551641c0d85034404561650014001100440d1040c0302141c94180644aa80d100300400c8007a01655078600803150748545401c030090760801d689551410140e100c01e40c84400c50a0040030000f00d41e542407400404030440c03584554015001400340381e8030300d5000310741481251410418100d09440b11504c0f10b486200f2010b0140015200041e000104d40458170 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 302180773 1250 302179523 302179529
    0xc03200c09091204060c0f0b070c05010b0d150b120708010e0706020a02010c020f040914031305090c0901030507120f05010509011d0115200102120c0711010c06090b070801 75
    0x52021660307240c6444850303883c0030f90000718441c0c000500084c08800c1c41600355018083c05800381c02d03400010343d1140c0c0340160341514004005913000c2140424420309005291501c41c0554510080c060180c03104941c801d4804590b040ca580c658015444075a904a2000c0110f4610700a48421640e15043d0b1030007401d08891a0055014098000800394000704d0040a032a030180c4462222900340d50030011030b102c40a4215070710680d90240360020400d801d00c51040b00c00000300540c2c1d10764070020740e085d80704801c0c1e00581c864071800e0200000080c5040c1619000d800c00c0c20003041540b2024003d0343c160103082140c081d0715240c120105680080e07600044e0485a0a540c4040a662143d080c4010240c0c0d06404190840d001001008000c0c003849615600705400d140c00e105400190005c16064404a11035169aa4010640e009140c618070308407a0002d04100c442850180c2c0c540e43d07040346041891825041c400e200703040d4018001180c01064850358403030842038a80c6002100a4150f8000380 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 302182023 1250 302180773 302180779
    0x8030f1305010906020606060a11010c0e03070b07151109060f030103020901060503010b0a1419032301150c060b101701080303101412060702150915070c03200c 70
    0x309002800d540103071110b0054940d59030241a0650320781041c000f0a40c007820300001049050a201c200740d1000303104d0200074003859a45d01002010b00c9040518151991f089124840810060480010000d00c200910f14540c40004104110b101001e1035080c01092062a04140001000242641c21070300841c160780c800ca40207070041e40c0700c45048899000901880c07841c00300030817911500c0c80c000e01c40141c3d140c410000403460b210003030014152031420100d000010a07100c900d9000d072800c00d080e1000c0384500307440320090f042d85000303000e110b42e03950190040c0611499150b02024801150001c1950b60000740c0b4a888401c84528001c00c00d28080d04480c0b0820010000800c0c00e00021045074003503214008000849400c10384410000e050304200c0c2603100c2c0f8410810003076403205016641c8620303929000341107140d500940f20b61400400400b260202d400c003040c9090344003c0c0b242e002da0049964600000344a0881c40d09840447c2c1a4246810600d030080d911161001e0004003040f20160035 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 302183273 1250 302182023 302182057
    0x180e0a1a0910050106080606070c03020a091d0d0c0b090102070c0e04020f010f09090b030f010501031a01270506040b040f1e021806070201120f02130e10091508030f 72
    0x800c01c40b0003121020301030390b800580d880d00030070030a203400c20241c1540c0d0b000707032a203261442c1c2d264000740e800c5000f0360100c0e02c41904da020100b820a806440207441010180c05000c1c0c00400341401000841c205000510b40d5021601080c0104c00950503030b2076582c1d20900c0c0e00c001b5078589554442c0341c9800c80c2c08a01c00c01c0c1e2904854015481200490340750102621005116401e044802c0042c000c81c00100b81c061107080c0c40131007402024000c90f4000c6002d010b0180360b8000e656200c44480740140c00c0305481c00a0940130800000310302c202d00801030020710300045c203915940f000601070415409019030003800c0030103021384000650f00030140310324001c2501d03030340764502d0780c40405a00811a03d21b0140d84041400a0039080080062809510514001ca00205680103c0c0c0840f034880340341d0303203055a0105011171200c0b03d1040700000f401f0800d01e40142c1e454001e03200300e204071081c05507032440b41c1c8440f0700c0c0206103e1700b2420030240c0039a4080d01e8a5541040700c0010b2500030800840c861113003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 302184523 1250 302183273 302183293
    0x10c0c08060c18180a0f020906070f05060702160b0d06030f1520040311120304032109080c0111011508100f1407030e03040f06020a0318180e0a1a09 65
    0x3c00a0303861007000c4c0488400040b9501d44000400070011001008040c43d02004111003545e00c81d401815010b101d14815200b80520f801e0040c0341c0b01008090409560040040d900720300c80140c5003200711815227201d00e40d14810200d411001d07200710384c40145a9100750340301c0d20400007140c4904d158070010f424100700307641242c54214022842e240c000a42ca610420041c40414036061074040d00b0f10740035040300c1080d400ea02140e499540a40e0003075540c0314036907240c00056940e004003c41c5920341460500540303428101000e0b00c4211502106050020385c06107003512440c00c0d04030030301c00c0c0c1821080e0241184c0c2d07101600e032280100c8100b130b078840c0c0c03406100c030b10001c400d44124403080c0c5002e0045011a0384910040c0e00509405817541c41c41d02c01400700180c06c00c084002c9801604413a8003030404105e11345005400e43c07454400340f003081803030b0b9641840940a0494014050710003e9800300700d400340d510801c0e080c90703443c60000c5d101d4060024402050070301c00160301c0c0918086403c03100c50000c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 302185773 1250 302184523 302184529
    0xe0c030106140411070803010f1a0310091805070f0609080d0219140a1101030e061501050706060e090a170406050702040f18142109010c0c08060c18 65
    0x815019104061040c03041c2d0a80034109503125000d903d00350003000d4074152031903c904007183c00c2603126014100c1e19603824402c0303e14414101614030480704402c3d0943c14040d0f000a92040300d401103002d01c81d03803002c0c807012011218100442c00c42d0132000356520036842d8500000205540e008907000700300300c540c000680c24400500e40280f801d82d68050500c0c0d003280d11070300c0000030108600703462861509907840c0d112442404400445c1c0e02c1409090240c20103040090151100ba00358045642c00c90f00410031040e819103591522035600340b8100369110b8080c6032840040509400012900400404012501d8000184845064004d10b003600d1241a507100f6680b00e4460360260400050701404503000504154200c100c141203640700c08601c05002584141400000200617200718078102c516072410201032003c80c2d0720150760350711803495444200307001040e44100364241e810008000040024002c004081001600300b05080d610381d401e00546c005916040745405c1019101d04214211080c5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 302187023 1250 302185773 302185781
    0x23010e06160e01021c0207090b0d021e030a0b040f0311070b0d0c050705010f06051e010206010e1512070f06080f060d030504090c121104030503030c03090118060e0c0301 74
    0x412011089040074064800480d02c8101d0500141d0651044154514058181e18083c1d4444009540100174046c5004542d8054038480d000702402600d00d01011750244c5c40b1511240801403849055401a11094010900d48101e401001d40008500e6040c07108100d0034a020840c1b040c043e50360b00030b40303540b030210403a181c45070f5224a002802d8104900c140200154201c103e00480900b415401d04015440342800c1d0791100d9443c4180340e036144000c2c40756260652001c1413854100340c01c4112801d610300080d40c0e90704107024943d0300c90204000110b4a6000302d00c1458511009072031510340301c5514402658400c20b03401102d403251120394010a003030b48a503c500f8495060080300303560f00c2e2203040600c018850b2103101030b13041200400c000b045030420b601409030441032641e80c01d40080f03219807504088801c2501e030705242040801041000c104000141c0350041a00303001a40d580e1200945540109440030304110f600c0b940b50700e00e90510503240d001c1c10001d10844140d85210070790504150803a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 302188273 1250 302187023 302187031
    0x10e0f1c0804050a06021222090204090e0d050f0738010e220305070c35030c03040302220c050901030b0901150f1205010306091704061706060723010e06 67
    0x1a201402302401500b004880001c0c086540b00b6800246500c1d19400c44c241ea01c41e81081ca038150b1218603003803a0003010440400c00080314030703040303062000240000c60385218901d40a800c01c06546245000340e10f0324070300b64a0038422280e4800801c0071410400f0f0214400344207421034905102d000a21b02003070511910b0039848104a100c542950340d03074055030306801100003a94481c001c4040441c800519a03810703964035611130071102d08221410407592a010b952104d030742c4e0300d4106001044141070000191000d40b40d04440007a9051950780f505442a0b0320b1041803110306080c45c0307a014016400c9001402143c10030f0343d06120490a200c18410300110070712400ca55100202c00200045109010345190241645007034010414440000019110280c1094a045590307641b100104202001070800c2481034134145800c0c145081c2000d0302c031852014000030125030410008240d6900d600c1141c00650380009010349c02e1012056007008400c0c840c020f54515031900345d4505054000003001841 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 302189523 1250 302188273 302188303
    0x12071b08030f070c060c0e0310110f1c020301031b0b0c0c130902040501170f19060209010c0506040c09060b09060d090515180c01030b010e0f1c0804050a0602 69
    0x603584401ca458640b0400040c451400c01011030200300c001645401851840c02040e9644484414a04205420482e211905030082450180c0e090984405902503401c5040380410b000c1c0c0381c802c0b0b082d5800f07604200d1100702c525603100000110401c00401051071588094aa6180f907254983d0320348100c038402c0340c0c80c100069200c603044010350714101408840f86802400301040c90380165001c181a10340c02e03046504911030a8448d804119020440c001a8041100c02840042405038006111005801025214640008111100d41d0080c05119040c542c06011a40d281c41c160070011044a868040c40f04600e003041e4001418904410541c1c81e0304000403e00740c07030725038450703a803000500900d8803c881c03501401c11403400240414850030300c103d01d1200481c9044047d040114100384000182505061814402200990340301020314440380085e10b5141810302d07580c3c0010348200c1a44142402080751224410420000c400508210751043d00d4041c41107450300003d0340c54911102036049 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 302190773 1250 302189523 302189527
    0x12031b080f060a051201060306050f1b0906070b0906060f030303090309060304020307090e0604031b0b2d09030909090105130f0f020301110301050f22020c1212071b08 73
    0x14459108050030b03009600100048003103581c40b40132035038002d802c1d21240d45a0355110420810306c0400e0041c44e500c80805401c10f62039250400503211490328181c00300032180804214944076458000c1242d00c0980c03c00101011403800180541d43c1e44011524203000b1840c84000c15501c0c03d001041d640150380410241d0f0401c9446028844980c00081c42680d15114966000428407030f00d202d0b4048060001c0007424003840c1c1030501030304e8000340c07500e1452100440451000421114034103a500901c2001410364003014a603960403034104a1600c90700d22030060070510130381d41000002881c0c119419a201d10039680c03206a41400c80304100c1e5920740c0d00b04140702040003e88604200d40803188200c124486201181c0c01180c2101d4080e02e100060142c0000117000c0c40c40c2c0401e880101503c00c40e40300303a4010385851020104122422030350810ba4010880300340149051001d2aa559581d030089a2074142512682107201c800382c031400046050152030410103100706030344110309034000444c1d038 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 302192023 1250 302190773 302190781
    0x30f060207151b020610090e150a0c08010b0c120d0b1018080102090d122606210a02090714070b070306080615010e06040e09061b070c030b060102030c070312031b08 72
    0x187c0501a40900c0711514007441c802085910081304146000b00d0040c0030003c0c004c0c1a44902911040c010307001112114800e100d82c0034400f0300054080f242c040f940c040c00c0c0d100e003000110700018101420134541d0024845601869083e800120b030800160000c0d81c0070110780c0d44110146c01c0344a90401301c0c0c0c001c812094a6008244982c2da0080d14202a00d0100b1703c400498442d0b1040c4c10600c03034501d030104000024000c0d103107404c541c088244881d8000c56840c1c0654418480e03640c200300c081c024000c40d00c44000075a80b9011350130426141c1274607004195101e00514104507050800c452520200f0710300400030454043c009a032511551081c080464200113030300041d907010301c9010085500c040104004203c1540060a090085d4100c1e00280384130304101d0b10180c61103c4a41040156400a12440c000320f000e1411200440349c00004c2100141c03030b03940040f03045205010380480303107200da04e000000b000503880f450300034103003223a41c1045000f04115811000d02c00503224140000d0b8400003007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 302193273 1250 302192023 302192039
    0x1226190f090c12020111030a030624210605060406020609010509010b010503010b030a0b0619030614060405091003050a15050c0403030503041101030f1b0e0f0604030f060207151b020610 81
    0x8225005040488000d810b03101b040e031440d84006c034100002078461900300f0003584d00901212603420a504000341d599251803005000102d410a5856a200301040813000e241865102034060140034140c25584e50303c0340700280da10340741501e8504066281ca0009500918184140f03410090305035909442d503442c2c44030500703c0c2d410242045808542d11703d02002d40780d446000070f02012031400502c0843c41081c1e20080e00321030059101c880702441c02d40d1041c0280d500c280c00c42d020340700111900c0e1116120001140b468506c1604001c0c004c1c41858146014024144900d01c11440010340900c0b0b180e035031140c000d84a004178840140800d40500c007040004000d984013414880c01803400150700310100300f00b8000d840407461242000104500c1119001d54840e00c40380c0004015a000c15081040da008111684030784d1201410404d0586d002d4010000c030b50f0101d88840e40c11040305807030010b984030103034001d000948111205003c09000c01c401c050004c58074070310411048034240b54851410402c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 302194523 1250 302193273 302193299
    0x1523120a120525060f0605010816090803070602130b0703080601081e0f1b030126121c0f09030804060c0c0b10060801050109031226190f090c 62
    0x400c20301c0b00500c4800b083c00c1c0f00c1e14440d811400d5680da03c4040c40901c0c1410340480705448080103107541070020500469030132505c2c641d0440d0058800d01c00c0c0703c0b00c0502c103da03a02e449400c040e0003404000b54210a202490b0094241006956280300309250b550398a0f04c83d900c03c00c00024040340d0421f000035031660003020499484010b100c0c109901c00000e498005403004102c0d160100c212885090040b064509000210340e00c41c0d1080940c6154101000000e0352588030045012089141c6004411800140500d40a00003ca04016100d001d541000703410310000c40c0c8241e202501e0010300b509680c00d580100184c66070942c40c0c01816848581313130400034042c54a0590300b031081c0384d040700300050819182c0501c0f42400340300301c4400c142009401041e000707047c3d20841c10007041d90010b1011400e81d003500d08054a1604020b20045082c0e4a0303480000142075410030643d4510040004079a100380d0f0000c07440b955030790200503200603001c4500498400120203408800c9500c2e0030f2100909002d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 302195773 1250 302194523 302194553
    0xa0605040f0306020f070203100905010510122909010603020316030b0a0e1f0209030c0108070206161e0e030d1b11040b09010f0e09010c050d020304061523120a 70
    0x60545006c1107600031900e01894150403c80b41075035001941d0a1060a01c82c00c0c4c0c2006100b03c40b1981d56241c034800b2510206507610240c00c40300c0c24886036400d03540e0140001c000041241c86400035103403e0340301e03074000e15103440164008d000e9035803031031004030003400c090050b40c3d808200c1c3c102070f496003c8001c0c0182070b01a000c1001d8410138850982d8a0003914030002c0b9052202005661181407505260404407401201c60602101d04240302c0b85a4000c500281c0c06002c20a0120703000c94008011683c5220300703040e580440e000c0c100f260f40303115030050f20095104019011108900121901110350750350141d000c843e88202d2070400c40c00620360518881403550010f00100c4d21462000c0010800c032001c0c0e01c07402014041e41e0081003500c030301c40021035110300c808000300404480040094150b205002c00600c0c2294000001030401c00180c0c00700301d101c5013102070351002c00d860f89500c0e1410704134501d07a02d21402c0d1030056100285000f03c102018030a0480280041c1c121507660490420b00c09030f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 302197023 1250 302195773 302195797
    0x20607020115091805510717010b040618030c230418140102070c0504111306050901021905210c01020c0a060b01020303070c03080a02070b0f060a0605040f030602 71
    0x3501c070012650400541c0c1440303e01005042c185004c956207403900000c2d45855541b42c500254001e000714034086010f0070903c1b11440fa10880303940d1200c084500c0d01d4030b43d08242504810100200f2514094805082074415507150390f6031941e03030340740214191000c034032004281d288045007c0c04070591140107000c1c20301071012312110103905000001c0540d4040102c0383c6881c01d00482c141c0512004c0c2100080480407040214906500c030384036100b05071071902840d8010f070b0300c590204290f156400100c600d100219000f103c0306640740c04008200d40c0c00640c04500500c1521480011800785403c20b00b5110750082c001c1c01c20a000b48003c042c0c50039105c2c50140c0c603246c280280045a5420300080401c51010409040040039a1414000715000b001c00981154014405c21491903000a441840030303402d070405002c15070310000d9103000f070300c182a8000c0c20896850107214013502c445103a00c0c0100c1c0e0854850740c545455200880d25405070b40f08d001c000505101007040424460b5006085c039480c95 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 302198273 1250 302197023 302197061
    0x216060302130b0705010f05101d06060d0911030c0a0f140609060d061d09060f061c061407020105040b010e060d0b070f0e03030a02070b1b0607050a02060702011509 72
    0x100070f000ca071900101c1c0e044e2016512402c010089000c5441003950240b90a900c0111030340c2084d04107051041224036400c15240120701107041c075070b60403050341c00c84000c039030041c8600e015030f01d8403115026105000381d001e132190f10607281232441e107500f408054030107528101c0c6000d840c00300c403c0e01c4c0b040902c4115410000800c140c120580b2180b0090503c0000c2d0140411380340d00d4500c030360b4500c0c0da80b5401d19108146800900440c03200210350140c002000807440c49454652400141caa544040c10415520203e00041003c100940d0084a00c10003210042c008070b5844940c141d080e07840865004002a259a0041c010007108120442c4c01071000303000d203c1c1c0c107d031503134402aa500c0c0585004000c11094030b800c0542950002904c100325105901031428040120703c060f6458099000d100e01f8120042800c800e034500c1c10480100303000d5400d08803081800e1000019110f0ba000f00042001801100c00164800c0d0050140e100050220b603460903a582c90701c2029002805000046608540d80b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 302199523 1250 302198273 302198279
    0x405013c0e090a03080709060c060207030e040509010c030f0905031b0c040207060e1902060901140c1902031608070b03040318080f0c030c030607140d0501090902010906021606030213 80
    0xc0941c0751842140349000a005010040c107014110400c002c019800b0890410340c240a207980c44000c01d0000c590101c0c016896124620f015560071410311703089a005440c00f801c00c905c00f00150041c04207007805407001c00441052440140c180c80c000d01c8043c6c143e0b0b00400050004c584410b8980c08280c01d4441654081980800000c05aa009801c2590752540f81c42010050000c00d002c036105d50b203402c050585441c01f0690201d20035006101186062140c503a2688800c0311910781180d04150480040d1070700e000f4030426050207001d21103026402881001200d0310f111b145000242c060301c0400e03000788a49817820170082c6a66100404c124104041d0384181c7e8488400c480c40c0c10082e110480103403102c0c40343c0d00001440c02110320328452280e4400300511a06440104840d41c100b022403501c600b481907100e0080b08a0710800a80805142c0f501000203070303407442903002110984c070036600d040c6034540c0d0710012680d62101680034048406949020080c6034003c0d4000c2c441c0c0c00251002800042d9 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 302200773 1250 302199523 302199539
    0x8010218010e0111100f0b180a0c080f040b070c08071110020a0803060d0c03020306012702031e0403120e06040c06020607050a0521010308090405013c 66
    0x1200195031401205240c11200c10340e000b00d10200c0000c0203180c50b8000c02901c0070820381c2c645d82c200300c0583c038035520b90a038000d205042d08103400f050400381610500514010f10264110012201c0c000304525080c1243d20302c40c032400300705004034020354102002d0f841e207840e01c58283c0d8000d011070082c0f120f02c244003030028000714090030b08a401542d060141030400c8041c0b08800c111002000304540002c00a180040d034500b05a980040055850300c003200c2d060f1504600103680c0360030180d41440790000004018181c1003505800a0311201400300e0b0b240c0558001c1e0a9010541742000100b8600400c040d503401407034001070303019000b0310740191a00d6149062008507049000c0c9482c654001c4020002031004202e810f42c003c0545100400c1e013440d060314010101c0c01103154080c104440010103540080360440008008882c6860104282d65a80f030042c05640c070003803400740150b0510000082500f030b6811520202a52001d5051824580d5407503079800180403043c00e4070403070103081c020070038403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 302202023 1250 302200773 302200777
    0x207120305062b050d1103121009061e050a03020906011d04020a030903080c03070c08034204060e2e0b0c060a111e160501061e030218060a080102 64
    0x202c00031911800c0c0f541810424140820790001100388001c69850b00c0d00349000008450494034011210350742d688035603040c004840940d62219484a04202d40415640030314014620001203410b00412501d99440c01d0158069140c8406544000d0480015030154002c80c80c4041c404501c44002c00c0340740100001070105e030404a00540001e039038407248001c051300030f644140c03c0400118640c1c290303d00064000c064109200009040400120102e440d11f10005180d0a2004001b1a0b4038a400c242d00c545190340c800030f0110100600103290302981d01e05140c0b10b02001d43d240c00591000a5903691169010590000910f10315a080050b5078084400403c420a02406902001540d41c034072a088152421902521408403a4505159558001000411901c0c1d0500d4a40c1c0c952541c1500780a04919015a51760803284041603001102001410750008007950345443c90460007030300c0d01e61034074089542404000e41059020304596901c4029000c0c0c558020030052141811540380d08c003290a80e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 302203273 1250 302202023 302202079
    0xf031312050309010b011e0e0117090c0907031e0b03030403020604082410050d080409091401060605250f1718150a030b010207120507030b0109020712030506 69
    0x258022041c098002e500780554401c910782480d21100c68400e858000240307504011f81c2c40d0621004c841c15031100d034010101c59490800c0417849110900d0700c0040144c442592103003040c4103c107040c000840c21400b03446aa1060b81941544082c05518010007034020643ca40c0c0040c2e0602c0305000000050741c49a0040c4090224400940200c1208403208d80c0f03403040d0200e8826400010004101c940401d50818500704d0f10100c0d10b5202854450600000a10072900f00000715801c0110b00000e0001c4103004254504018008100c203035515041103070b050046007614031284a00c0004030f01007080340d0307500c45401f5001d4184503a01015035603c0e9005e10008481045401e4030100d59070445000c580240d018990307080d01c50307224080c0030304a4041144250300414041c0740e5208143c1605034801c05c041000b42c55016285240a101420900e50740c0b4910310003180c10314080070001c120304505000382d856060f070295505006800715070054014010041c07007030b50000c42d517082168540d8100ea405180d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 302204523 1250 302203273 302203277
    0x2190c02060d0c0e091b250606080606090603010e1509030c0105090f0123070305041b0b1312020603070503041b031101080f0f0a090303020403300809030f031312 71
    0x4904d0018092084800000300081103c030f2116150942d081c2c0d07014102d0704140d038519140c909055542001d0b4842000301c0300c001d49044d00d070081c0450b525800003a00c3d8002e440031030f50790b0003541d59070b0101400d03980c18036141000c07500400070070300507503540b0070105801c02d621000760b90900c0c440c41196421210300700c840f10442e034000c5c0e0184149140a1240000f01141d5140035800300940512481c21102d026251104141d07803030001a060140040d048130628801580d60760815540308010100c40d0001c0d803981000006100340016060500d0a070308150340e9014110504561340d8440a8845800007001a01d079003615141607a034600c0708105140265100b054240a101c544600051120301c0040001480e0050343d020310010704a10120741c3d900c0001c0d0394010079040401d150440107805160b0000b401c1c00000391016859624280d02a1401540d1400c0000841e00c2c03243e08843c3c5400030340307401c11150800c0000300b040003420030040d5170086410400c018102000d558201071690885c1d04400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 302205773 1250 302204523 302204537
    0xb130e0a0b0303180d3002060403020c0607030203070f03080604060f030c26010606090e1e190209040204030b09061617040c08160602010e0d0504050409051f09030f0302190c02060d0c 80
    0x280d5601001c3c06c60280382e410f02c001c0580707103010b83d006507441c9001d042c1d040c4030f0f11022850804240c42007040b2962150b11413440d0343e14042510f000781c0355a80c00e80e00c0078070403401c001c1c002c90009100809003080b01d400a82819a052070080c114030b006882c0d032034030700c100100d01046554840c02400b403203004000ca9035545030380d1450007001072540755000d030502e682e00c1c10000c030545203800c912003415000060790035928001c07509007809900a12601028541242c00442d0001c22b0110041860744194014400c0d5131055568004020885035404242e01c00300384481500401e5071000c2e40d25540c443c0c8140400d103561510341a0715460800074000c190095261a00d041c03281a60a0003445620342d101001080b9a40c02400f000e08280218080c03030f4083c03503603420a041489820040c2445a0803144c201000101080791044090311071a8020740208091009401c0c28078828400c654076110a94010440020b221804483d00c066840040c2d034814414403401190784428400d181030710302a5201e0710 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 302207023 1250 302205773 302205833
    0x30a0621170301080d0807050c160815010302030303040f0204020d090506150f030a0f170a1101060b0306130e010b030d020309090f04051c02070b130e0a0b0303180d 72
    0x144000c0812451850700c024001048240000108050101c03040c0c105142507a0300c0c608100d401d401140c1101445215a8054107640b100281500e01921a10000d986000824a0350451024000e200094065200300006804114000d139500142d620040000d49000415590041503d80d00c10080d202500910103001401340c0712008464451000e035103008241b040d100000e80c40c0c00500d0b01c003400308201701d45081d08000c1a0519554606020b210484d00d405c1007202c0102031034801400316140d5842c107003001c103030b48805030150b034800d0000403d007140300c0a654905001a002d540c2c4034403080c0d0740750607400c555603406000c80d0500c030f010b5174002c42c0c40e40880003c003e42c007071000d000e404034a4100000d1001040300400c809031409024a58500d140c0f103000030403403805485622481c07a0303090218008054144440d4900100c88800b9208031140d140e03040e0b0001203420044102d0341c550f004000d00010103814420300117900c00002c000c09002c0001c0c0e00e0312480c0d04e00940201080c0e100044080d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 302208273 1250 302207023 302207033
    0x209010f0608100e010902090409020d050a15060806041103190605150a0b0904020c0708030a03020d0506041b080a09060203010b030907150203180a1211090603030a14030a0621 77
    0x1039070b003d0340340041288440d2508202e000d0014041c01104001768000441c42040d44558001711461540501021004800b0f81030039601d03580150800c80d0040ca01c00840d085150141c051070040d1601c00002e0040c5889d1552074142070000c00c4d0010703030103000f419002901000486140910b080c0140e50100d91840c013454a684000740e000e42d442e1284110810a100e21480c000070307030707403110019074005036140300700c0e18002d28103500d6900c0070049200c002903041c0c9540e4141c000e00b901145004c401d005540b036903000c02003514036260000e110305501043c030100a521a00c41650868060180017654915648580d02030364005d03000700701920030000c14410f0000040280d400280140c14041d101201920340c000c0d100d1140c9101c03100107002da19160405559400242000bd0040d0740354103801d0000d13440e000c101c0f42079a03480c2500c00c407000c4c030000300315040c04011aa4140340036951b030301e1007040401d0300125a07000038040700d00407070b6602004034441030611200321609124010102c1014468601 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 302209523 1250 302208273 302208287
    0x180b030706020d05030c091206130302010b09131203060812090a1a1c060506030a091218091e02041d0a090c05040903020c1309030801051801050105160209010f06 71
    0x10031811544041042282c2e2a40311307003070300d410180c00d158540d925160a80020700d20030803524080074034000c0c0028842000b88209101c04154801d4000f840740581c400c0c02c00131175000465420245c0301ea03086003280041c8040380b203842d58002c5130a00180c400c0e00d03000280d19143c10b82035010080800001c80c1c000518100700d80304020a0f80780040c04e03e01c03050045150319401034503031041d201d01060302c0100700d440304da4000c43c018201c0544215241d14280103118003404000380107907903c0009122414802e0311400900030307140410304c001140c440c40e0400201c0100060902950b66262030400504080f40d203000074401840d1213103031400b0780c1c1815032404200e1800600322007201c40c90510040009400911a001210012100091034500c142401da041407050903030b8581c0304501002d15085103025600402c41d10307003c1d40da4450141e80352000e00c003580926402e40c4003411424001000b996228200500da44c09401c1c101c0c558404565010848007035080e0030100040148810a100b403e0388403072 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 302210773 1250 302209523 302209529
    0x2e03050901050c0f0a0c02040504030306140906060a110a0c06110f0d0e1c06110d180203030301031e050609060a0c0f1d01210b03011424010306180b0307 67
    0x2c101d18148402003030014458050382c854010f0340440c514070b40c4c500896180c5800c58000e8020f10080c58580783c0140180707101e003d08180504c83c0e812a101a040c21404103110700c0c03001c0c0c140d602c0d0a404041c00c1c0d0741c021501c450001c09101d0841030a0004507681e064200400daa502e8400c824803990030602c0c10001f10050540e40c55002c0041031600c0d55020203c00c1241d407082d5072190340d124104544410400540034058405400c00040c1c01c49564507030020840c3d0401c1000401100107420b02e10303500c0400f5541d010b54141d1040c4010304c00300b0b080c2c0045901800081c035040450740c1850f81c407141880c0381101c0000482e0441c50820000d1512405094611201850051500e00725064080c1c481c1901c0107501c07071501c1b04070460801c0ea074003a214100e5406c0726007403054548440c00c103500c00079041082031240654202014a00006a400da40c00d0094180a90b103100185c1c1603091014072003d05070406042544801c00090740300b00314082001c4158580d00c002c280d181c41360b07007070501d440081e074 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 302212023 1250 302210773 302210791
    0xc01020d020d02151503010c0e01110102160212150f0901051005030a1203020d06091a0405011d06010c02060307020609060709150c060207080c060109180c0b092e0305 73
    0x400c882850a90100f5210844c040041030490140c0780d040c1c0000c54a520074903a150150b291050005405801100511901c1d10903a151030101950a6543d4203034055001e5500da00444501500010310309403d000522030683c908a41c43c00001c0000c0c11002c9005075800703404100c4c808140003242c142130042e194080542e42c00c0d040721500c0c0001081d50b4102d0b81c036025140110690010002c144a60100c6d02e014244110500c295926404480028400c036016509100003444c0c160089040c1801068101d4208000b0382c001000700022240342580010b1a240c10041c1c410341c0c1d880183e5407280594000c2e100c3e54003c00039440c143d0391075450500080c0001051000b01c030410410903a08000307100c000040c0b0320b00050010300314a80400a8000c40340001c020500105441c138042c1d10001d0194101c60802c030061040c0700098140500c441182080a0130100026a0a0100b40d40503801007659000240400d4500400b06403041400340060001041409010000c0d42040d94980070301c0b90452196 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 302213273 1250 302212023 302212033
    0x51014010f1a16170c0f070e161d09131406090c040902060d0204090c02120405102006010312110601140d08070b010b0912010c09030b0604021b0c01020d02 68
    0x2400c189002c078040d00c03540a203041c074825100d07010001c284491500c0b50140b820082d850320f446030a03041d1a4048031841101c50b1286000001e00300c261003800e603001d0b03681e03484500150000d40500300c0b4100c900c0c0c02810b0201401c1211b0f07858903140c422585210703000001c1d2010000c03026181500c2006000c10b05c180c05540310609100100802042800c46c1b054100e600150000061020035550300448a403e4109071020400161444051b04140c0c2c038514540e007941d010300070080500b560760007180a2a0b8220000008040d205805500d030500030030210300050094010f81180d1500d04642600121400151181e01c001c019411007000404004900060285981071440f50040c60301e14554841c070503110140e00a0500c5132202c11148002e4001054903003c0d070310341d040041180d0204000c0b500618069580d8844500706201c0c1500004055507071030b503100c2c510784804814150182420394071682c20010360203108a494006520590b000c00681078441000d40060700f00101954098199000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 302214523 1250 302213273 302213309
    0x1020d0614011e0e0d0605090c06040608010311040e0a030c060b12030f07060207052a04140f06030c040f0b0a1728060c05030a06140d0609051014010f 66
    0x58242c1c182c00603209558002a20843c2c0100c5011a5040c0c6981c0c001c132000840d04148402c0c2d812203480340641c14119080e4013010000e00029100303034030840000544200050000a130b1075000e110745000700074004250071300e40321400f5090902010040300802c02a00f185020040c140c09a00c00221044a80b8200c0341c04a03152580c40cbd1080c903040101001c800507086080002c40c2c0d054407402a04041120050038610b4071600c0708008042d812038007220700c50407080551030030380100b0100302c484900e5605c041e19001c1010a0308076026012070b40c0350140d541e40e00c07031940312846122803145007000e010031030b0700b050710070f100c1c02c075a040e040103203c040000340a50b2001d900140d00c040c0c41d503103500c00548a81d10b0003050705c4da000c25801c0041601e41850080106030707a000c3c0182d400740912800810042e950345a50610113034806140740e801c00c107190000c2000c90b01d43e6001001c1c0038001d4050301c50b04018031009100b11020300ba84989d1401302800140320070030070003003540042c00e407607000c2800f2045 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 302215773 1250 302214523 302214527
    0x82a0c0d0602070501180c03060609180605070e030d02010b01030b12030909131a01261b010203040f0e0118090302031c1b03050610030603080306040e07120501020d061401 75
    0x80c0310080070303240a0b0006820b03410003100350b024118401d007042c440700c0a400c4034a000360050341d0f1440203441c0301d41001c40c0400c2902407403103400da00300018510f0765041551540d0b01e9008e494010031110501c491100d04000507101071100ca10f443d1626400012041c8038035001404071082c0b04007007805800410300031a052103001044500c1414202c0350039110342e6440c0210400c0008e4400010499030180c0d0381700020f2801580081e0584d201541030300740c040c00c9a204003d01e201114403280d6150700101e180c4421459070403481c24800e174180b0560b4074050b100d0318150361099003a03024804010490700100440312003142d03884408010781c02d05015005098034000d5682c0240025047c45104a0070500c1403d40c1c154000103140101d20044822419541005030040c40c003241e80d50b00500d100c800e9200000e02c81d1190006882d4000109825a2100c4c02480020000c0c408404ea0b60701c03c038400480c41e030810f40c041c486114815000035a8803004051024196485503112100c0c0f07e1501a030401140c0e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 302217023 1250 302215773 302215789
    0xc2a030706051914040c061e050c0c121510080d03020f120a0b09010503030a140a090e010b0702030d0e0d060917130e09060103200d082a0c 61
    0x79080507000c51192a022106030150031043c45883c481c0d850115a074144038656140c0f2403040380214440740c1215542d940903200880181140c89840d807405c0c808001c1c080c007940280c0014842013007100d401c46030703010105403881400b94000600d54010b8415a2000d07207000c50761503024200c0308025080c81d00d400c5400355501c088000c0300041c96000b203a8030503004603120603203980342c8544c1c41d075100a081884408008201d03840045014000307160010880742800022143c844090350740700151012031850030309254202c0039010382004405180015192081380b8298081c2818a0340140e580000c0c2c4100b61401c1c09640c25042806184184a0314642e07030181801c5640b504021b020490501a02d0100d1101d003214058600000000c00d0744400c2e40950b5030203805440c000e01060710b00340c07601d09007036554617001d03c0b0003005800d0044c08100b12071041003803121b0391040600b2001102205945070610354020a52140382c4040000c0800129039090001e051801c42100240030103800407004a0307886 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 302218273 1250 302217023 302217037
    0x607050606032803031806020a11010501061d011b080316080603240601030615020f010e070f1206060302030601030305070b060f06030a0905030f0304050309130203010f1512050c2a03 80
    0x4199600d0f80705641c01c0405000c031b80340307c2c0c0c80702c81155226201c25000e040d0a040803200030311580f8000c00401c110740200024605070003044800f842603e6010700454600e41e1116982251402d440311230000102000301850042c8128414400d10a0f102d0754000c2040342c00a00e00b5120340e0040385030b2040c85180c84420442940b1410b0807020a13a104401600500206da001500b80411307004102c50f42c9a0204486943c00403c00080c0480c500d41c86245583e00d1b164000c000c0d01c0119032904000c0c0d03000d0859540c01c01c5106040200c0e85903030340d8000a0410100f42e00560216030006020800c01041c0c10125030300071812507007003101c1c640740c6010030070304c3c000104000c1c0400c0d40c0e24034280500c801001a070701041c1007801003a51300e00d030514100343c403500300c11941c2d4010000c010b0386040c00c502038000c0e00d0580780300a0b4022129454a05c00f1111219a004401d041c0030452501e101c0380413080c0501c61081805000305d0380c0d9000c2d84036510740c040001305c07111442c80c01c22228612440c80040112840 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 302219523 1250 302218273 302218277
    0x607080114120c0a080606030c0d210c060603060903200c061803060c040e1605090402130b0a0305041b08150604150f0f05010806010e0111010b0607050606032803 71
    0x2202c1103094080c40c14042c00780540c0d0004210400007401d40340003420520406d000c6d0300b43d50800f071200081c4004210086001014400710080e903d41106100d9441656401c451908011f408982e0300c4020480f18190415600c550300e505c03690040c5904000400000e44900c00c0a03007a1910b201106074a491482803002d2007084001014022054201d800c0c82c402d01008050354100d051101d101040766001384107181d1000028000980c412007118515070001003a034543c06d2400115000b004025808410181d42c0101d03546000300384220100e016004c42030f81c07514001241d080c0341c00d11100c888501880803c400030015800c2c00004004528048450a107008a4002e62104400100640302c96062480940411140016242e030711140b03d800b1a41b044070629901d5441c3e800450303040c8000c0b950306021402803005c0340b100f5480380040c901002d6400f0000560030305d01030001035059004d41020303183c0e07503c0030041c8652440c06200c01001c9240b1f140e400780c2060040107240041c1500f5000c0641 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 302220773 1250 302219523 302219539
    0xa09240e0a0812070b130506011a04090c0302070c081b01030e0102090301051e07140708130b0d091e0b180a080d09110a03021f0e0604060c02030607080114 68
    0x403544540d02140050103000007516040050508807842c1d0380c110074015209a4a1040840c901e204140c054207103003a00603001c0d29450b0308208540c0c10120001250700044c1c0401c00c000a8812a41e100d00c60007400159005070fa105a80d09180c400d049650700200b0036034110480e10181e031403107a5480110f464007802d020a862841840d102d00a00450403110b0f00340d420b00c4c0400c04102c076019902c2c005a1810803295845440302a0f080365016038140350210460f07804c0040c4c5002c1422100035040400110080c02591502c0e0010328409030804450319404903141c0b21103c00f042616030031102852900c000e000c1540c005070b128002000c10180c00c20603080b8000310100340c115800d01c40810030540220303841c1e17030321100711055900510700200e00341c1da104145a034031542e500c2d002e40514201c0e034009003002c541c0504082d0000c2030141e13501c0902c0a0110140108280e91281c00141000f03081c69194541e101c1124010305050481c014070640401c20b4490051141c4208002c54a00242041d281d0749 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 302222023 1250 302220773 302220797
    0x20c0909030a030e0f030a090302090a060f051201020d090804060306080c09011215050103031d04020a0c0809190909030e0a21230703060c020f0307060504081606020a0924 75
    0x9003002c013240c05e0010640400070700407007490340150400d801c4900c00d54202c4015610103840100300d40040c0600718076084089010440d52801e40f1a40c40001d111000051402200540f080c04440a100701202c4451011504004640e01846140000c0c8080400762021009810000302e0204c014040c0880b0f002c1c0829a0105000c00c1034003410348001800750410055850741070207000d141241032903100355403852562400c5070519009595155510b9101c02c0d820070112742e0f40f150b0f541c1090160703582112a00040235940d20515812800604003170780009152182410010425840d54040a02900d079181c01044004020160481c6c05a141c60100c0d1a07840c0d2854400c90f4800400c1711044040703441110f1804242c4042541000c86e0700c20201004603c03401c2c00c003a42c40300d641d03040c0864140c0040c40b0200200346290015540141310f03100741c1b4500b408100c40383c13f80e007905003416a0300c1d560100c0d04044050f00104082c019080317641803181c40419000c60b08007414045030440080000c411180 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 302223273 1250 302222023 302222051
    0xc0f1c030203120906060a0f03030e0f040f0f0506030106090504120f1404150f140417071a030405010b0105040f060e0307050a14030c150708031e1501020c0909030a03 73
    0x541c002030755081d40345010342000d03a1240c5e03880300d080c2c400520030843c3d2a4006810a40c5541020440707615444d00c2443c2d52140041000d2964035141490b0420703122000d14204000754414103600351815080001d190405505143c00c5541d160482d44080349000107000c081425810740c0a030140c2149488110001ea04408445000020640c1380d0303003041c00b0a011410341c0c4e0310411510342c1c1007a070769021410751801c10211b49480002000e41d0050004000c14850000a8010040d201c0c0c0c07040b041f240b40311307074410340203026600c006203000181d20040140001c006007801030b034040103000d180807800e05080803c500c3c2c821603640b180d401404596005803501303807014840c8000520004108034481d9a40310f500030080c060f40c8a9181c0309008252480c1c80d50b281c20a402602c0c51603040c522130070481a655036581b41e5001070701f040784810360040301803012a549079910303101e03150110201800c4400f2500292402060a410b1441039000c1010450030503c0082560754904581c500450307411280154 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 302224523 1250 302223273 302223277
    0x5130308064c020d0503011a0408070905011707151d031f270b0601021f0606090b09282409050d0b01091a0603180c0f1c030203 56
    0x42c4020280c4580c1c2ca100c040b0055001c8030714145882035010b01c000750094412a1250301e80050900440c40520040c8400405610044c100e2186080361503d4a03440304002c0d172910050b68401c080c90307601c0d4070040c020b90303020030710b81d014540090004129107800e0184510380c440c05100c24100300440915103600440c8a580c201c120890b0107800da8030250205550780071001c2d01c0c4410050500d0800700001d4843d440c2d9041c884220700d91882004542940b5039490240c080080d0038141184070380110b0000c1c42d80c150300440240e0050708000601c0e41d2030050048c041ea031195000c0310007942c040c061110691500407000340e6a010001a4002000000018280504054024030100c408414a980398884112240007607801103440e03001c0d20ba5512820840c0700034412100078282811040100005141c6030485010700b90b50300d9200350800c3c0a00089004c0703800440d02c143e05020b0340755003011100014000000c3d030100580d0904100b07600b01001c00e64240c140030301380580003907001805046c03510900c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 302225773 1250 302224523 302224579
    0xb13121a131202011a2707020708100e07151e050c01090b1f0f06110705060a03050402090a0203060307030f080702030a0f120305040b0115030905031306030513030806 73
    0x2070808401c040c00700001d0082c40911801741c5c0858003214400311500d0880c003640200007240890880210a00b860903040700380140280b0194440c9600100342403406101034400448114000130320081a0454a844c0c081213920000441c550005640184d643c00044600d12551200c1c640620804001c0c08584038455a81102c455519102140042110b41610380340030f5007080c1904100100e070b50081282c401c107544a00c207070200f400c210030040c2e503010340354020200c02c0f00b00035681c003079603a400801e020341e00c8440c9410010b03644408001c1146000804560070000212046003035141c841d02003551444079010181c200740c00305030000200320000d41150702203075000c0e0644280c1c06040c034040000e4600c45c1d00840311f280e15600d04451092080c030515116a070400c29100792a441c00500901041440302e90303902f0592a10350500c0400d1081004001d1920855103ca06141c80c0c180300404440000c0c10208022088441400200e5032004415421150807502c1d4400d50703408503450007204a00c10 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 302227023 1250 302225773 302225783
    0x1c02030304141f020c010807180314010515010905010e040216050105010602061f030605091608071404020c0d081009092001050a1d04020f03010b13121a13 68
    0x401107054030720368940d841003280507101c5020781c034048101c843d42a00151040b01c0164048404d030035885d13101e1f42400d50403004030f003080811804c4840b01c050080a80da0803da464200c0142c500001c0802440303110b6200400440702c0c14403454a0700020304841c03891103811304003d0a500380c0c0c440f0340c0ea80e5044540392905042140340607405460b082c1d000e00400d1040c807026020f0400003404068002c0015401c82a080800d920701d24110ba0740d2000400c8090701d0384420b441103288001c40c010011580101038070782d40c00240f901038509481024110315140d40715000d140180030044180400003522941c00c0322505000c01e81c0da036241c0002c404060075a212900d0181000403140510503070807018095078800700c01441448440400650380d40c855a0940310005c4c200080075400c0c4005080b00598094004001518002c00365040b01d513983c00c2078004002982c0000380c140750315007481d00100000c00d440c2880001009041c0c6031541d000c0c0f00c111049400350041740001c1c141104950320700c00c80591003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 302228273 1250 302227023 302227027
    0x509070b07050c120613080319020706060e060102030703200a150204030b0105040e1009061b0e031e070e0403031508010b010306210303020d020412050a0303060e0f061c020303 77
    0x142c01c0c0255690001c0303403241d000c0c000e030754229030450001141451158074540d182c296011401e60300d4880f158030040c000c4120204503500015041110300040c40b80901456011030010305210a11100c4c2102400320360640d4820494040000d400c443c1e10001e04c0e004d10092a085d50041240c1414202200e4009040160310400d1402125103a8013803c00d03280200f07140d81c0c4982c0c80c3c0045c03004480000c1403814031903204805542c45407001c1d03000000b0f4244074620200e80210b2a40140e0b01541500401e032000c40c041402c07103540c506017000440c0c40040d42080b00c584403102c592090703488401e81c0c02041140850b007000101450b000e90440a80080248a207585195407000c5c0e290080074040c071000d0000303040c450b0005d40c100100001004840d48010320017030042c2c0c15502034001750b1241c1b81d100281038091100003005140c0c622068401da0003030700500f400205600e002011107a00b5001600216132001c180000c41c00784940040c2d100d001502d000b24440e1003800900242583c800c4000d41c18400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 302229523 1250 302228273 302228287
    0x9010b03070e0a0b0d020a17090a0312090807170c03030106030b0f0d08220e04060b03061f050108190e010c02010b0109052404030606060e130b130509070b 68
    0x6180114424400782c2c0e181c00c4a0010031007000380c3c8600038803409466800911908003420070075030050a030a0700c0c40c00d01005a00d039403809004003900c04c5602c101550030410358601403540000c44505480f904400400c283c0f5445e0f0b03079490450055500142841c3c0041c000f110310b03003280908554000c01160101d980f250796a6078018050940b0b601c81c01c2c001c0d0a8600351041030300b06130400365110ba5110303642d582025801009032100301f0b003d0080c2c4080e203884820000d5621f81884c0c51170b0095000f00404101c4505000c141441c18002900e51501d09000c030303002c0a06500c2a41c122000d41c0d500346004c0100d03889000d01d0244403542207880701409494400825886503055010f49094041500203010344850725005480c03280c00341c490282c00c1603140c01c0c0c80b480401c0040c41d0b90603020f000800581840e4480d2a01c008456190f0400404107010303090000c900d281840001208052074002440340008080120b5034510080342140802030302c8401055140c4021b00801024045210f1015180c904e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 302230773 1250 302229523 302229539
    0x7111005060f10021203070c08040306060807060504080a0206090f120a050c0307060806060d1b0f091a07020909030d0c05031006050f070807020d0c03291603020d0b0901 74
    0x10703079803103100700101068515582801800003a400480d034014115540782c0083d034034540d83c13006000c042080400340310240020001030150015600901b40050006c0c24800c2c8507141c00c01e10f0f081041400006d01c820454100001100075000e036061b035402d03441fa240c40000c9180718030b00404403076002d0140d00300c402c00040b0000c0c000c2c4049004604440302d5183d02000d06840d20034900800d40014001800606030342803c03401000005013480d0009020490084c00c012403d0503c03c02000045009050319a0a584041d400024100c486101c0e61320b0740342c480d040c8449100d206030007401030340c850380006c8450105000340c0301450028602031103042c3c0c5a18009002d507004aa0724800d03071064171400706003588100309842591600c641c4051500c0d100d41ca07214090f4000c040100c1c1d210b00034501c080c000800740712910340150721078900c208014842c000350303e01c0c0c0000f040c031065804101d4030410400b41c124030b4140c8245401403c0050f6100b010400440140001c0b11301c25401c002c8030703000051145 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 302232023 1250 302230773 302230781
    0x813030807082a0c0d080f030108070e01051507020103150b03010906060810030b0601140c01151502010509030913061d0f01060201060b270d05071a130e071110 70
    0x1540c0c42c042400d0201d44020215031800e180701c403c01140c1c40640d0300d41960600210190005024800d0141042519280c000070b5510907001140640c00130b09040100d17800e210082800b41604962007060700c03000b890196124002c4441c041d0400d51100c14100c1e581005d158034101030806000300036070f2580c450700500050040b6114510005035460000362107500c911400a096a81c0040c088a4a49808004541c050300b00d44082e0381d203a02c10001d01c0c03045a0300740f0822180c1c01411401003117140c5050680210301805a400c0c60969040000300110300c503012085607080503085030741c906000d2a45104600414058000303241a1880a0200c1e00d138010718042c0d035204980d00881030f40c1607170300d481c400c84c01da40b0248183d1a1a1006004840b100b00710700f0f01004000c0d0b1107803e044500401940040c8030610400030a0751160002c00007030104c400000d940400d5001d0b0848414900700c2d908420080d2105a4810200c03a1039455020684083c810079129141e04100300803520801c2c90080203000030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 302233273 1250 302232023 302232037
    0x3070f180b06041415070f0b01061701090203130b040f0b011a03060609010302091c150e0606040e031608030624070b0405010b0303070506041103061003081303080708 73
    0x2900301403040c42001446801602001a0094421802c0500e04079005401402000c5030942c488014003e02a030081580050080c0c1030260013a0080803501d4140041d0807a0181c000741c00700440403038040c0c60014403403145411075104500060f500c0e6541d000364400309104010007403550000e881400244246000c1d0001170780e0040b00200116603076246c0a500110390504010360002080c4006003951030b1030740c080e03c203500060501502d001d002c000003d04035410003420101c4ac10044000105220544014100d0300b8605c40c01001380c0b04c2001c80c41550b0f448000d01c4035200e151201c0420200b88410300580b50700c40c030019213507004d1802500e000c090340c2d081141c4160088824080800c150001880c0c03050311400c100c42d0244c6009455203814105150003002540d696482c2e0998122680301040101074040c069006480581001c1c50007443e00c2850210551081c1c0c002c0051043c0c0716070781c0743c03001c1c21658050305242c0d4031184614110300b9594194000b501410000c1500c10900503084014003030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 302234523 1250 302233273 302233289
    0x40b061306170d0905130b150403060e0f1908070f300c020a050f03150c07060e070e0f0a0b0d0303060918110f0d021c0201090e0c0703031a03070f 64
    0xf4001d015041107542d508607100b92a8025400311942075030a109901c9086001805420a400f00824041000d00e0f07034443d41c402c40340e15a41c0c10445070200340c14000145074541d01c00181541111401101d080c0c10081c1c107014040081c000b80c0d0200300100c401e6100c00403580403064038590100d500e80b034940d5111560940c0c043c100c894585848440c0b103a003104a20039401001c080c1c46034100000e1210b50350555011540600c101c043c0301c10a81c40d4031118510070607689503502d80c1c4e200f061905000361410f05034030402c03170b0780b150205001b4003000d144110b5009208098107012035455001342c1e000b4005801519422620310820300f000d15506811400540b101c07540e0500c907000340c2c440c4a185001c2d503c0c001501c203560308407000300e442c903240740e03d100305417401000e8140c0070340f5580010b0351340c41031048851000f48201c1c09a40031540c0080803940100801115441c5902d0056607a180074450500000e04050799080e91184203d204038240d032142002608071814103868040d0720302055a60f0041840c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 302235773 1250 302234523 302234533
    0x105070801090c1b111f031a0a060c030507170306040e0607081b0d0515120a050a15060b0a0c0c143604050606090a02030906040b06130617 61
    0x781c2000c1e50f00990301d0b403180c2907980840c0c0a00003561500c4803025800e080711a0007140790900555912007403e079460100c030324090302c4815102c1c1806011a424550381c01c403640c06074425482c00742c1e02e6115403030440341c0c03e040116100b1194542140d242c468548020920031146182000641101010350f124000555040000f42c01c1040704035541d110455442000911000000d400030b840c94407104100c0312401510350600402c00200c034151003044504444144009040c0c2c0700904c0d0030341040010b900b00402509284209031221074545c0b40c0210301800d010950f5045070210a802c1e44000010120070344038980f42c2c03412500c01840c252201e0819074903d914036001041c2030300b02640381c3c4c5011500030000100540700301000b1411082c80c0700c007001a420803980000f201250082d015101c3c621540103482580f800c00308000c0340080143c440c0c400c840c07051003086516036000542d070341c0140e00f00307e44580d690784450002e254012242106905141000f400186c01c607040034100d000c040303488064031 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 302237023 1250 302235773 302235779
    0x190602010c14071e020111010e03070203120a0504090207020d060603060e01050a150501110709051602060f0c0403350c060c2d09030d05090102010f05040c180f0e0105070801 76
    0xb1000b0f0080c44005030071086018440d84003120480c294600c0588103041c940c04030306008003036908440e46440c1c25080e6070400142c03541103150510408030b0341c4640d1041103080c000e0140340146140a140200c0782c20b1035001602c1800c0d551407030b9603e00c0060344441e00b0f01402c0d80741d143c007a016020b0351042804540c28000807c26011340c501812040784007096046001070304c3d05004603208000303070800161500034060042420940c5003c0e1510419880307408100c1c880030008000d14008004008468a594207401e0000f0343c07200c00c0851b800c07243c01c8580c01ca003001082400c0c5461060460110040702d4076805585648c000301e4014051500084094820550b00c4c400300c0c2900b440b40e030f9070000322004c0e456411000580c0000c6000f081c84000c0c4c80b43c0c1d0405035588080303443c20f000c4601e860040307600442c08030075641e0709003e0a00106000102030000d0b081540d1071205c440c5144c018a40d0325428032880612200303103980540031407030141e4070078441e0800c0c450b04540244001e4a8840001d00c00350004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 302238273 1250 302237023 302237057
    0x8011b12061401050d1b020706120e0d030902011b140c0301020304050606040518071d0603010915020c1009120206010e070906030b180405150a060509010302040209190602010c 77
    0x61411a80c00e02e401c00c00341100c8400444043e8000306250a03259501c00500f0343c803c2200b101c14801c2c01842d0002c1082609040000e080741e0070740721103807498a05002200c000013001040044081c8140d0a001c1a1003200344011381d409403660412003043d0318422040c90a000d400554110009841c1342602c00c40180c2c4414103081c0d01c011039019203158400008201c85040560090303602001146007407000161013100f5608000880e4046415550300d9121143c02d0b40410404541050080300200654289a69480098200c2010801c100ea030b002ca65055021420300031614200d4401c0380800c040c141605d010101c10300c14840c1c0e5401449100000300e9403400508065004080075110300d40f01c00e203481c8040b00038001441650f41c000003091214185030460642c02d80c042c6200d04050400083c0094941d000302c400140202c0d071880c104001007000f072b05d4102081d81903a40540f00035950302c1802e030108003080c40c00e84006211400c603c100080c0c4942c1036000c440704481a03910b803002c0040a00138 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 302239523 1250 302238273 302238281
    0x12060b0a08062701140d05030a02060a0b09150d0c05061605010c050403081c090b0c03060f011b031b051917030f0601030209040b0a0602240103030206010e0406020408011b12 76
    0x5005203c0028000522943e1143c00c811210168001d103610b5a000c0b060b03a0345070540d002010140050fa102500344100084580a00d0080349400d443d0300103580351a08a80030400440c18034075014a041100d9041402402001c10b0043d00020704401c0e9550984050a0a0407d1094090f41c1c5940b0300307024103910a2080d000c440840b6080f0b16020304002100000220280926049502e02a42c0700c0d102d40029464091040c82040100401e0f6201d140c00402d0010002c0200b1686d0304202c041380c1034542c00c001c15080300e402c03d42c0600c0d002c0550041100304565000d5042c030023800e5031003071141401d500004214004940c41c03103880f403d1810002121014501d000581e4408030361407409002402d80d5102e0b5010b80045000100f01040000140c00440c880301030b2030b040b103001038019001041c060034240c00701c0c280c68183c005e203042c15503242d518001d440300018015262100780620220307003482030a4040d94040c14400300200002c25420020081201c208141c0001045060304001200143c0340b01e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 302240773 1250 302239523 302239579
    0x1e010605061902070305190b0a0903020d051b060103080304050d090b090105030c070f061a0607050726010203090d0e100903020405070309060e0c04050610020c0112060b0a0806 77
    0x12482c144001401d01c000b410008400b100d0031031044440c0080800c90821540081031201d030741c0c00769051900d0070300145240004105240d21070514800400082d0700082050b10443d0510300b141d1501000580c000c82c00c40e850121324030318415400003005002c1c001d0000d5001d10b210b54121002c4490113002138502e840345116148116100b4085040e095010b01d00460b80b02d080d10401e585480c585598045040303c10718019100c0d541d40740800c00d03108001c5402c20a4404044840314106003240e0b948941d180d10318001d182c42c1881442c144068011040100f09201120074000e40d00ea246c500344c46550b895480036074100203a50b404000d0201d08001444190006440e038a9401140c210303000e01c405080041c250004243e5100d400d503001c100d00f807080d03211000164001d03005668800d0100401d6a82c080d1186100b00d24071100107190a400045084040c00c0a082c15034084411340c6c1c6890003010f80c0e034030002c000031000440340086584008014412003048417503944c11086031449428441400c8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 302242023 1250 302240773 302240779
    0x50a030f0605180109030f0e04090b0103230a0303020c070f060f03052206050103021e10030c02030d0504030e121606180906030b10050303070c050d06090209091e010605 74
    0x300d004404507072940c002941c403060003441021000f070207580d00c40c02c5501503503054002449010a55842c0e540c04a444154030b0402c603014000740342544c8a00210120601c4001e2000b0f0090380e5500300a41000401882c00b01c1c00010350782c0702c61403824040c000e5806420049860300a0384030200307080e40c10b100c2c201c2c1528003035910380a0380c0f00044d2056004007005850480038903859400c03420100000280d014881d4465240441c036541b440c8148001c0c00301e0304180f0341800a24a0040d0385039103904205180385002d600d0301017008a8802c5050b1308601c83c00560f0381d400c90510741000705058108900d03843e07001c820fa400c0510806040300464560fa0300c00703904a0000e0f6140c0040109901c114108248116102e042440c0c2540d00e00500d000c50701e10354000c840c0241d10300c0400c00040a4500204018041079014502d814082e03569100e4003196802110710440c0c04540700c000340700351030b440000025805416014117080600c0d0481e82d940d00301c00000c1c042c0201080041d41240c060040700704442c2d006e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 302243273 1250 302242023 302242043
    0x1050108010e0c03090a082d04241412040506070c02010207090b010905030703140d031401050405070c0c06110c0a030b04080c0f01020301180b01030c08070509030106080f1501050a03 80
    0x8424190303103500251842e02c0321b1140143d6034000c01c54160003407900c0304000100d1810008003000d98103401148405044805c0804c0c40100482008140c01c82800b80b05590f00c82100f038283d280603500b0544540700d0303c08a0501050b0081d0410300c203d90b19010391f00603806c440c02582c2d140e0701250416600b0318001c1c011307042480104402a05d50300700050310744050400c1c80e45c19840b000840d10382141176106071401c4110060750040000244a403400c08295031600b409042c4201080d6071180c50184a258003981e618000540150706c1005441c0400354800701c00000c0540e1100014200521901000320900454100420302d10f0304840a90480b82d2102c40c042d41030b59182c9803048250450000c002450240303500003038800200307100a502038808100c0d03d1183d912030441031022607041017a200d06051800452010303c44d003082d0010b50000c01490035035981c00504000c6030152107103610480007441031180015601c00042610880c0c441c074540341091507079841040220707410b540d01c409000c3d101c0d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 302244523 1250 302243273 302243281
    0x230f0f040b040f0f0c0314010f03030503060a17060108100e0a06020c0c090405070608132f10020303060f0a030b07030c02160e06090703060b0f070203010b042301050108010e 76
    0x540c108004445000340b00003096407000001000303644040c41c4220001c1d544002e550007203a01841070414241d0080d00c081455810411444880b0700036000117030501402200240260b0f64402e07040000c1c0050399183c4100303019102e401641d40301d081c06164010300079440720b0f46407041184907100c405031082000300b803000165218240254004021504580215454200181c0311510340b103014602c80d000411940d0301c0c10304000c1003802d001e00603c40b021044030390940801c03c51818280f1001d41d080403040001c0303c0001c3d044295000402d51900461183c20511480d900400a10300c10f041c251201944c0ca1269401c00007090200d00008100101c244045405103100790b0011060103441c1c0102c61f880710300340a0125160003160302c23608800d5014802c100b00381c00d0040003a03801030a14141800440e0610710244050b004216011224074400b0a0640c1503542c25000a8184603010384100180e010f05041040d03214a00d85201001a1020000003035552081600c28101c3c0c2001d42c4103507654403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 302245773 1250 302244523 302244529
    0x15020a0504141306171c1706030a20150c0a1707020307140f03060106080114010311040f03050f0d09030f060f050703020d0608010501080c01030c050c07230f0f 70
    0x1412800303150060300403c900c81e01c80416100354005052403420001c034040030300c5102850007000d4a4500030480a042e004ca6000782c12504480880c5c6696004818980e510000300f031600d503004c80080c00900d4078030006d807003d0703035030702c0e024060160300762289154805111940c80c2c151103804641c0400f03611013103510000c242d030400d142c104c8036454240c0307510b03045240d0002407401025070801d0300700101207100010540380091011400c10001d03005418503602d4240302030000c407014807510700c2c0340d600407000080ea40c0c4690310800803c80d400851756216620340360304400211250100315403034820340c8000c0c030200c4070002d01035000e08040e41d40c3c28000750440e80c4030021411007800480e822a01e0340c02d00d9120100c3e60288610607000340d03170b00584500c0100445000d4513a0307984404800e900d40801030014803c04100c61160000a08021030341c88150042101c680c402da980105090081c400e011441031050004400044595046c44401c40282400c000059070343e114043ea0014501100d401542 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 302247023 1250 302245773 302245799
    0x903150c040608190207060515010309110103020c0a020301050f07020d090f060f0306050405040501090c050a050604030b060d020907090602070b0c250911030402090f0106020d1101090c0b0715020a0504 88
    0x2192180d02c40c4d03012505914210503a00720700b5040b0340b81c54a0b1410410407404003000c03008169008d180a01c5100b01c29118031403004035410b0800d0425070005920200800200301070070503031354060000c1206161218542d124500c2c00c0e907841c0c0040c013868101034000d51003040300500ba00c800780d910840792440c02c84107031804860010f4883c1410f84968000032596240e200d0f04e80b040f4000e0f400800c2183e5103280c8414441d0303180e00010700c0f482a004003031107103423140c4081d642a2a40020300300056102c150004030b221040710b0b002907116030382c41d082080942d8058820f6080fa171140d02110b0304c0303076100c00040340340d0700502c5909040350740044851012803c0c094030ba01031024051010101d1540c99040c000c065070106844081d06213400000d000071424a03d99841e07121011541568040d410814000d448500c81e007a40c008014000500d0b0784229400c1d0300c5405920350000441e6140307940c1e800e0302030840d00141825240401401e446000510160080301d00c1c20215a403800d2610b42007851615030b01c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 302248273 1250 302247023 302247031
    0x90c01090e0403170f151c080304080702030604150525120e01060f050f060a0203071728180e07210203010f0302100311091201200903150c040608 64
    0x40c43e41190703001c000c0180040d400b41108540c940002d107410f500d090090841700401c51b000e50300c603050b5021076180e01d280200440f0380c014205542c032b4035039081007600d0b07010700c0d0740203503160041c0c02c02d02081101d1078092941c110700245040c4101d81d200b1450304902002c40070960400c0d010302c901001d1061065001e0345400e22030040000e000c100240b1445e0848200c1d40000391380c95044a424080ca140801c20788811403001c9a04603d49480c0c13441c002d4890184030002008280780907040e00403200002c041d15402180c29038084180f003901102d42220b0b00207554403c0100c2c5c1c154440c9400e4041c1c00104900f61034160300c50311540d4075030001c02c45108007016425142c2c085003840b100e60381c15803070004600138400060713010f0100781180100303c0048041c0c0e2911041c5440c0003084100d900804040d62441002142c030f011155250394101405800ca10540c080c08080d40259003101d510702030041d28003590150122103840802c00030140c0c00d80402c1c0e5600e4054a800d000c100a41849140a5684 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 302249523 1250 302248273 302248277
    0x50f060309011e23010f090b030304091b0e030a031d0418050309101806050702040603060203100806070504080615031501091a010f0f030509161d090c01090e0403 71
    0x1a403c40080d180300840740b5940140100d901c4a0340b200c00059060444800403c00d800004419450708a420740103029900c240281c20f629110544100e80e0207006450060100e84000c0c4008150078501d920807004002c1c442c804200b20760314188041c2000101e070102c03a07526450354881c2c00c2e5102e01d00c02904414001099100380c079503500a01c2ca00d503001000b084203109000442d11240b07202c0802002030b03011b400c0d01c000c0081d503400ea114407468600c100d03011242c203810150b031ba407502c9001140c0030304402d805c00740c13220340000240240d0303240300f40300107080341c1c010800d0703030501c4d102c1200454062085100303845030396004030302245192202540800e802003004040700c426030154401c092011100364081c1032003d98a43c040c4600801d541c0c03002400d0750b42441c0064410b01d01c40e1000d465998065099800c05da51480002e40302001086801822440a240c080c111030703482c0020034295101503008500756a120340810310275940011500740500341611107500c200e00b400c55510200c10000c0050381 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 302250773 1250 302249523 302249531
    0xb070312111626120610030506030a080f070b010b070512090d1104020702030609060a0606030506100c060f0e0a11060403080403021306091119020d080a0c03020702120d140301050f06030901 83
    0x1c500720062004021004082c0250f5107117150038020090000822038015050500748003c10903540d901080120846a10000e125154052010b80303800c00d01800d50001c0104884000105851402001034a0150b01c107800712900402c0c1a1095505030089054040d040001348400e240040c0da49982c0035511003010704014100a01900041e00d088020340e01c0d841d10781c01c10b8080c42030004280c0125000f8003040c0c00c0c10700c0035040550124000c43c0f101d120704010810054a007108001c140e4004a01c91000c040c0140280c01c140c21500c1c0d101d00109004407041101c400e6102030300d0030006c054030100c80d0048955030a15246800384180c0b4035401c1d0b08914055511034001c44da264681c40b03600106485006a01d840f031f8400c2900110740700c50301546000350360220b040a412141d2102e0b907103902440859011400150050055001c1c1c011884000e40c03090107003040c0e8401010001d030b80540d0382c8444d80c8607900b490700501003406a2100b80100da400c8410810794000c1390410701d00840d04141d203040002 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 302252023 1250 302250773 302250833
    0xa111002010e032502040c0504030201120612020909010b030105070504052106011a0c1906050109140c16020a0915061e08101205060a0f15120c0b0703121116 69
    0x1800c851f04000f01e0300220780003040603c155684907500c3c124490708034108004485c200000700e000100309200091140c08208001801c00c0c0c0e0a411003c80301c1001380090116081001c1d001c2d03c0ca4200d801424004c4501903c030b8000185010400d00a556051003c0c11599007403d00c104070780c0400f004600700e0030b4010002e00b000740c01e081040030503280c03250f03a1013800090607140072420703214180d002326900ea040040021100c0c6291181603003140e032031002c4a9030391580f65220030313032148483c00107507002501d04000900340e5aa6045003440040769071401c402c3c0d5485140550b425540800040b400640600d42c1c071070a180104469034020708407002031003d1039a984400d04030744000c42c008a803981c01400520032300c0348440c05213916600c40810b0a004130b200203451007124501130b20900751604820800340051015400d15440600610349035207584000e54100074200c21600e402102282d4600814034484400b040199400462615030901e80300c8119121840c412280503070703010500f0501c10940d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 302253273 1250 302252023 302252029
    0x7050703080c060109060509040209060d0c0504060915150207060311190201020705120a050d0f0212130c060905091503070f060c020f0f180a0207050a111002010e032502 74
    0x1621000070000003d00107581400a448240c1d01c1c0c651000380a103d203c000c3c040142e0b561013000e039010390300341c0d410b2102990a0a000124514952050780c0003494038801090100b0b158100038a400b00742d850404100d41d40b600c1020310104800c520b000184c005900500c1041d1003500b05560000c840040241016520210324000410f0000c0d0079004d41e50014142003000000c0c40005109074080c1c08075400c00b0350151014006100703070040350f50341540d00c0c08100c0141019605545400900c0803c1d48101d00d440769038140c0042401c8401c0c0c40311900c00500044107031003058080150f8001a001402d95140c0b0041c0d0005507441618540d41030144480100d80107203c40156001001550340e031030001c9a003030042c00f00d01c0c00406a1507005894119641f1a40d13180d03c448010300c03e840d01d00340c9841e030765002c01c1c0c1c034024003403020018a5801102191420301c55546c00d541410581200d0002040800d00e00503401c0f00c40c1803046000d160003e12100000d841400d116103000c00880c443c41044000a40c00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 302254523 1250 302253273 302253277
    0x40201050a120f3806040b0c0a060c030510150c030c23061e130b0415020408031c0c020a020f03120c030315060c0a060f0b1905040b10090b0705070308 66
    0xb0b04540c02c001c04c0d0103a001d68501644000c0c680588030035051100b4a0130b404502e4521030360041c0c0c021400006440c403d504010082e20b2081034000030200441d80c603e10b4003c01034481669812504038110307801080c000003140140f06c200295441d44444201160307402e5030741200c0c15400756070031051070041d0000d200040240050030040b440280c8140d00d000d40301010f21249056505082402c520200540d96540040751960f864000400940039601c43c50081c40180b5045030203c0b000d03002040000d1040800005810703005881d0708407100316070103c00840f044a00007031510005030301042c02c12016042c51031440c40d100700301a0941e5941e1920303040980c8035912041c403100350313079000104200c1481c804010f403038021842203480914000420500c00e9503241002c2000d0700081d6210302c0c14101c00090303409400d10080c060031000b06022a15080280c1c10030901c00c10380524202905c01050b4680711009240c021895282d10240034107142c002038080e00942802c907182d02c2004400310200d0700ca440 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 302255773 1250 302254523 302254541
    0xa14090a020130020d0605060714190f060504060b10050c070608010503150622090209010f120f0f020604170c01080705090609011e02100b0306040201050a120f 70
    0x100500044080c1c0c40014420707120000106803800301404102e21081807201c0a00795075040300c0015840d203201182c07001c02480f944e48100d82c0204000740d2002001000240c0d18240440744003911030006183c090300d40b130610583c0c0020020b695500807900050156407015030024000d0703400181d669180c03800301d01d01e100e1604040340407660200b61680c448138100081c401074030300b0b460f1001095141c040400d0380c0d0041011070b00f088003003035000180715840300803180d80380741010400064101c91605068008001d1024241c0c01400c10744000300f0001c45074004a1b0856200c11002000301100da00c806506541040080700c1c001c1d41c81840001503a5924054806001820424111034500860844c40e03c4810360149040c440d0050402c404650404280d0740c8124081da001c666a80c415001228041d030a020780c104512183c0403400c0941c0e80c00a00c004019500300070810002090004041d03990034102e9009001800030042181082d00c991a8800c4882d01c1140c00314104042d6580d82017a03c015407 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 302257023 1250 302255773 302255791
    0x30b06031f05031b060a03090507120618050c06070201090504020d06210b0a0c020c0307060302030702210901180e0f070f0513050f0310050a0603020a061e03050a14 72
    0x41258a00c0d0180c0c07040000384001c500602c05008180c542d6080322000300c0c0305510403200411281074090280c4c0020281030f80c800c4c255240e050b1261500c9503001a4503100f0b85480e407500b031201042c0c2444000300001141c0003070040060001c182c08100050748004012810062070400c005050703100e900280a07400301d558400308440f0f051295804810300b2000300128280314120072a400304590302d2401d070300841e880c0004582075502c00000d03458548800c40d50341d0103114100c03000031502d9141e800f55000341641d50a803a0010a20940341140c0344038054803e0380e0032070070400c0140e103602075050b9109840c503641c10508540e40c0c0e000300042c90349003280e544a4440c64041000040c55000180030421003850910310706000c0d00c0d2100681c1c00f40c40f4010700c1c1c0100155042400540d0f410408a0301203544807000380558544075030450064641c07480304a000e5102e5a4010686a000714010141c4200007004a592265100022070140c0000342c03e5140e142c1d61038014061226041000c107114810039 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 302258273 1250 302257023 302257051
    0x50a0602030c0d09140d05030106050403110f06070b090610062016030c031214090d0311101a01050a0807031a0411030613050717180a150e0606060702040903030b0603 73
    0x1805c1100e05110082a11600f040400c0005010007a040401da8003500d4000d108a101701408001007600c0c1490a060b055002d98040303000303810842c11100151141d0024825528242c80c2c0a4441c140d5507080e00414001c070b080c114402e141c0100e40e48441e10a954218115600180ba4030418580101950000c0d1807030021340c1c4050052010806401c513070109549080030b0315501c00715001c1d14900034200713042d00c203013080309141c024584101c50030001030306c00c4810359151001d02200407000b01a01a41003006000b21140d0481c20341c022030076100b40c2e05280e1a441300c03130790350008114001c0c1201900b601c5080525088404a9102c1d40700d00000154011405952400c000040040f034844044245407203e04210804c0035441d4004c00c400510f00c14207131104081e40707420260f10103008ea00315140e40c0900c82d00c2c081c01c1c00c0c41294507020401320110003042085515040c41162215801c0394240d030413031010494900103041540c00340c000c0c540030b07290010300328020800048055005460059007aa01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 302259523 1250 302258273 302258303
    0xb22050a030f080c04060c020118140a090b060306090c0708070309060201051609050d0201030e0a050124050d03050307050c0f0601060e06070b010e09030705010f05040b07020a050a0602030c0d09 85
    0x4240c2c078140411690408481d10302d00000034680c00e00c954001c0b8003c01507412a0041164065092403a0307455000502c80202030303d03102400610018030304150701c500522003002403c0d00203489008208200980840e146507108002d02c034401101920b0506000c0c1d0802a0700040f403400400340910f107100f69580d8980d2440c0500c003c3c00d4031000b90840010301e0740c0d40c407404025034219110108458050398550b01d54500303400140c1c0144100088070b40d560080445410412106520120410080202c00d48054070a100c01d40340c0c80d0944e020b0765030041646604d94001c240500b000e55440b840c5031600b54030b814000d26406041c00c4800110041e0340e88010010b20070300d03402c075200844151050b1030107410044252940b03d540c0300188103510b240d2886601042440c0404e10407a0406178200d00244504140c200b124401810215810f4404600040110712080e03c0070a10405c4560002c004100e880d0a5488070300c002e50014107400c2880508003c1c8031801780d2140241c0354158090540b0880f0011 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 302260773 1250 302259523 302259527
    0x90b030703050402210601090b21011b09030804051c12020d0801050402120c0703140c210309061503030c010c1e030c0c110d0204020f030406270b22050a03 68
    0x3070480062a4214201251111704100008070681100c01c81c0c403008c102c04201102240150340c800c0802d03005104603243d8001c100302d05402c281c50303e6002c0c0005d100c007500c40142c21a20b40d089400001d003400c0b0200000c01c210f1400c8155400b01256024002100408540d580e1050251403032800016070000700c050000ca94200880500400707058500703524044413010011203032040101b110000300b1011559800341072041810030510b11124020646d107a507400700656807440c148a840c5072201b00300e14580070b588030000599009242c0403006010a4660f844548805060031070b0803030b0140300c180b08c0c541c1d17407400c240a4515141c006494640d02d100c0c44204152406100500074800d040c01c4c44410349009900c81c2d18402c42c02d40003100344a40c088a500000c0004214480c00f80d8024008035031100d040ba00b400c01903000b240303c2c90781000350181d184180003c45404c1a141b002c0707402e004000700701003640b0800555128031124200f140a600c100321026580514120648081d40440e1110341015 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 302262023 1250 302260773 302260789
    0xf0e011b030c0f08130c080601170a0305030406020315060a0905090604060e0612031306030c110c0109210606030803061912020111010209100210110f090907090b030703050402 77
    0x60390614080c00040880c0401404207200080203804115228002070300085860b05030340f462950000602034013950300c03840e00350369080c00c0c0507610340040c11408000c40c02d10001044c084003035040d00c40d142103507110744510000350401451100701c03401d43c1c1c1003102035550340401000024266282c5110803801d0405100d1099001007007180902d151003c2801241c42e039100d40d0364000411076203010b002e5201403081d0300303501038500302c402c105400c0c0401291403501904420b200a000d50f0705c128045d100700c1010303651144000030007400b00e00046000d02200c00411240300010314490750901480a0076914082103c1a941c810385440700044113000b4079152900e0b0100042140a600d10021420108040e218819441c002410310544228400b52801c0c207406546801600500481e50700307030316003c06915030b204e8030f50b11010f0520b00001c200034600b01038180c603007103403a0740d20503828001c4600c03c2c030189070740203000c500910a050308005010702d0410300440c071030301c90340d50301007a80d05080c41844221 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 302263273 1250 302262023 302262071
    0x20c0f03030114011b021c0807030e0f010512012606130221030406030213030b0711010c11031e040b0a110705090f150f0a0803030405070509070c030c060f0e01 70
    0x2040c42c20741c0305510b511000d40f80c886950107c980d1821a01c0441d40401000e0400c00c009124080214008050542018860400c2c400c141e400010040c14100115010302c1200b0311a490080c5800060241500c0444500000e8606078481d12071009400c12052400b04111410034071005444941c0045040003240c060722410640b1030501031800012406807a402640600320415078041001c0041c00c101c40a0700005540140c056821400c00c21710040c644405140c404d1075a60801c0082d42d0340c00d00c60020001880d0494019600781002d00101c3c16440010700c0011100030003c0c00049803200c8140c0c000d204800e6280c9401000c3d403c42c56042e41010016400a8840e0107000201f0507a0b20842440680c002140b0304441e060885060003c1e40259005225642005040b200400c41030390020041d4050b81c080c1e801c80340c0b0380b5074540c1000740000f004c88221002451304a00500001d0042c850240d9041c03242d5404292401c034295004119008602c200040e0380d10b904204207402030640c03101c120 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 302264523 1250 302263273 302263277
    0x6072313090e2109130c02100c0504060903170409020c06070e010f0f050c072c0a0501030224120a0b091e06331b030702180901020c0f0303011401 64
    0xf90b02d4485039451181a034010030400940000703640e2400c0d9035003441070a100c160050100024084944002e41d41e180035201e0001c0c2c0391512800504180c0100192800c844040d59a0010745045540c0d40b04075004004154030003aa040c031020848604500141070b5102050000708400e150843c002042000c11004060600160044040500d5030203800424600401c9c01c14650f07800c094401d0300d00e41103440c2c0c440c800d0403135148800c00c0c0c0f0a00e100410a0b0400d5001043c4d240d58840d0124101201c0d802c1c40000d40c03002174228000001c100341c5402c080b044441070041408e2400345103400035140c0301142c8040442d036803903102c01e0b114582107422541110030031800c101780310050401e5203448100940081c0c072a1150b045440a010001d520464240e8010b0b0911076103401602c045413035075041050307212154a0319444240d411100001600c00d4581c000b4805080012200c2c01c0070301c1440040c103209065502004400c51044040007103080507680b5000640c0c0d00d40c98015102c03d06e001014040741 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 302265773 1250 302264523 302264533
    0x50f0d0c02161d0c0a0c0c08010515040218360a050901021303030315090612020301050117100f0e2a100c020f0103090215040503060a09020306072313090e 68
    0x406040a040d0461380309074140000c55440080c110244c513001885440140300e190390b10f101050404043d00024003640c2075602600c50040c00070b0401080e4041c0c0c01d001c0154105103120703030005280420006c154450410041b00a081000c0c000c070000c150f000055800482840d130910108940a2054640c8685203030001c44c2414404aa15480714820307110140803d91104e09111003010255030f004001c001480041003c9030351001d4650300580c0c060380c2039110f0f52030b29000013001d41041c02c280070b0500002c400b5010124985107200000d181082501240359a62070281100e131030100041840b18014980101d0041860703107034a43c070200c051031001d01600310035012a02c02d6412400314016039078101c801203101032440c40101c0081c903030084040d40c400e9004c00610503201a410042c002d075070065050f2901740d50342caa82c0c50141c81040400942550000d0000b0b81040d01c110b00c0e2590400c20b15100b03004a02400c0a8481590801c00304a507510119207010440c6034850b2082c00c0b800200300000d40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 302267023 1250 302265773 302265809
    0x90103030f0f1101020d060510020304050303250f0302010e160501050a0302340b010501081003020d14100c09050906150309010608010c050306090f09070501050f0d0c0216 75
    0x1014075000e001400c00780400304420780c07034150080c08901100042d41000315110350306078012002519491242e14003510060059110700c0f44003108131010b071540a401189010303424550140c2c0d8505480c4981c3c1010f1040c00f40074000341043e01d20300d541c0b90280c2d001040000b0034a2742c09040c07070b1030008a81c500b5404202c0c100a941d07005002c1e124121901e007001a00c0d10909003072580d071203541c450200310345180d2107038900322202d20044151086000b01074101d0282e072100c005484010b01074902d81c042040c1244100014500300810150340c0c1d00c600015007030684c401010500d08003103501181019a10f41c40e0700c02c500c03540410500001c2404a60482181c00c2c854089003410500c4800c0140d22803000000030340d00b4070250480001440d654000f0080000000002442608140d900078814400000171440154a254243e4000ca40040c0603189543c523100040da119031100320105003824091010885a403054420a000d103d501d070041e007a00305940015034036440f040e41040890380440c207960 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 302268273 1250 302267023 302267027
    0x309020a060c0b1e27070b0a11030a2016180c020106031a18070e0106030614330f0d0e060c090f1216170a0308150d0209070203031509010303 62
    0x1150807203011181c61950302d0900f8001c60440c541010705d01c8091103203040000c0c010b60f48100034041c48540740d43d141881814203906544a214003180c5400103152104046800000070460041c0110100b0803104000c1c940000c0401500c0c2ca6406000542e0020710214821041c9019022a0003c544001c11031642150344a0702e2200d4020b248108100608000440750701c0403070001c2410103044011038100a0359001c65801d40c4000740120800242000000502c2c9071010011509681c3d004110740c403410084208244078071803008d9040c60b200441c10401c0982c283e8040100440341d010103185a40e440c00ea01c000050754252903151009030700070001c12030f5011080042d540b140350b04a5090f81c150b0782a00c00101521121360352010380303004619071003141d4203040080380c04507a54150100750140700200b42540352050700030040e012402c0040000c030005001d5064140f0281c000709410410304003a004121426001c403020809640000f0901807002d211002040400b00c003141c03900015070545da80 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 302269523 1250 302268273 302268331
    0x50106030c0c1a041403070803060a051008070f022d010e0304030b01150e3313030813030c1503060906050a06030c0212030a15170d08070309020a060c0b 67
    0x43d61001d040c2210105040041c0800c03030a008603280c4084a448112606210803154000d8034400d200340b05622001456050030100c04500c4007403520340302c1c81170f55801d0302524148071030300c1040210701890400800707210f60a8083c5401c500112140b1a80b81003140c102c5084850117207070031001e81e00c140804c00c00607011213152419207448220311120408114016900d00b07580c2c0007466400000788410700b01901c56110380c160840003400400c02c50882001051800e407066400300138061a45130024004034170307804000c1001041c0c08072000a66581ca44620019448a410000c1415150b42503031041d50b40c503000304000340000b8141000414600b400140c200e10440c4650300600d501e4000d24180f0900031712200300c0203071305002401c1d0380c0c0c030701000020002c04900a00c0d0708842d500d400085115141288948059038a0800424142400b1541942d1401e802403000040503102d102e22130040c0c5602c1d1030382e4000c1c00903484030300200b001032030700801d030300402014170350501e4003400115010303c1e410070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 302270773 1250 302269523 302269553
    0x61f080f0a03051305060d09050d090605030a0b01091703040608150a030303050603010f05040809010212091c0c120506060103060909020102060703020d06030f0c0e070206010f050603100810050106030c0c 89
    0x512644c0c40c03418800c040e07000c00c0c1d25440264040c8010801517088180b43c0c0090203102d1245050f1440803c04603000d0b51507155500a005c0020818800a08042c1d010350211000b42414101600340b0355036404c0c050100c0c0c0c0000d141d4060b50b04081820004039402034601604907111220400d1408040c901081e5181c1740c900c000f404041d01d807004181c8644080d80000a44182607606100d140380905014031300760f0095a00c680140716003003038050a004d50105a8481803c01041880030104103800b2400c03580c000a0180d4142908040c00524215602413a02c1420f00c15801b41100c1d28180e0300160440b01035611168080d0304041d64500140c0c1d000c919143d100c056420016114502203110000610036500000d000d07003c0d0f400d08a0038002c0715402e25085443c00142440c03159141c010480e1602000e110303403c100d14420a0a1086d40b40800103554000e0040d040c650105a42d00980d03413506050320b075000c000c0c95541c5d00600030b4507414000c58030b10403100d090031004c03c8160364598007415040e007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 302272023 1250 302270773 302270777
    0x20c0d080703031104120303060302030d0513150e0d03020c18010e041b05060403060b0a0906122405070e0a081f0f060905010b0a18032111061f080f0a03 67
    0x104c401d81001d459401501c000c0d0810715070909070b180d43c600d00a0020302a82c08240e10901c81d074003403520b00d10320410441d42203000f85180240c8642c40e14100c50072130280d080810080c4022804042003d449040300d074070246005c1d50050400c0504941807001240300700140181c09a0414014001c00301d0500f803864100342d129500c14013182c03411028030145901da4121640c09500028000700b4020b00b80c101080c03604040b5540e4900690b0742c014202101d015100310942c0400165035840861001c681c0c43c00c404180341c04d41002803440c03080e0801100d500300c0c1d03071401007811250311002904041d1440405840b0810080603034181415101e07058042607485041c0e100e40b138851015100000c2d410240007840030300003e00c1039584801c00001e80c1d1304102d182a00140420040c0313580501c21503042c40c200c070f23080f0380d03140c803000d07450251091180001e95842c401e0003001149000d4044042040c944107031040038102490f0010600020442d502ea54800c04145c1d2207100300c0f40f00350501017040d65000381e040c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 302273273 1250 302272023 302272031
    0x10051005090a0e07031d19020d3210050708240301020c010204051c030503060105071103060c030621070e041a010902090112090c06080604110c030a020c0d08070303 72
    0x3100002c1080c4220b40080d400c1d000d0f84400d1000103a01500803c8032149112004012091241c01040d61003120030000d0f21515006a1000c0241c200030140f05401070041c1050840d01e540592030046840c140c56403c40313a0381011440c0c0281000c280200c0c160140b42600c280814140100c009003078680c00b60280300248816501080c9c0d0702c182c5846c1002202d000703002507468040504c4514001c0d009441031030300039200030800f055125110314001720001d901d84c0b20301d030641e15440011191a00980e4045440507044450001180d03010040310b84a8115104110340e80d01c4c1a00600001c0240802111204e06c004050300100c598042554010703a0110520707107030140e44509041c8450845401ca00480d20094000410311425640040014103801e07250512100038096038141211500720f0090103100b50a1014400f803446465280e1300550b0040011802c0403103201d5408284e030007400d80d0901544001001e115203901032010b00440d440884680d11240309a8079214414441c0c06801020990b803 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 302274523 1250 302273273 302273287
    0x3080703090215161a040b10030302060106031104030816032303040209070309080c060405060c0c0d0309030504080d26060a0905040c030c060807120b0102101e14040b10051005 77
    0x81094040d04a60442180c1340301001901d2080c048005c103a03000d50f540d1492500168110708111040340489a160780100300a03032801000302c00901d8010701001000c0020880080404d0b2003001170045011303031002c80e1a0550051802a081e82c0079076001214150111181802500760001540d60040d01542c1c15040d607694120220f006201080c0700a02c91a000b0401e58182c8000040d001d129610a0b000c0b61003507110300400f00058000d040c10400795920840d4000c0200d8801e40055000364402c0c2070907802d158a800728141082d94500d4900005230f03001a2014034030b40c40c6040700c070114000300c001181c0d0382003080100c1c44500d80e502451701190380341d101003010440005500d800650f0810301d0b50380419207502004000c004161082d40006445041480070f54942d841769445104050b001000122030350f5550001034000c0311801a64405408248500070780207008581c10005c07800310754501031905290098041401600d40903080c0b200800502c919184c61403c1c2880820b2410016101ea074 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 302275773 1250 302274523 302274547
    0x5061804090602131403011a040917040b4b13060306061d0915030109060212070f080c0f090607051f18170307050d0203010f0303080703090215 63
    0x50768207001025a807000418000ca20101600041590f0b240702c80d807500725032a2001c141c01d0320281003503450302010a4513040b81e0b6183c158000d4510301c4c0300d0240404a040309501041e003d8019038411502040002000d171416007520b590b114190a1584c0e4681c50707416070010700400c0c450f80925195400060322141340241501c13400380c07200c84a070310078010445a02c0b50700050113011988581c50100e240b841e400b000c00c1c00c0b54400c00300e5640b8060308074041e5940c0c0e003c0e1200e000707032418030700ca8140d56189070340700c041a424001490340d000c40c09821805802c11404c0188840503541e126400c10003480240454001ca41045503a0302d1a43c02149840e49107003c0001c010748200c4800802500c90b110316003035801c800c064030648491420b803040129000c3d0020301110041c40754002842d00d452540c1b80b80c401520b4202450700300507a440c0040c10001c034000000308aa00c01e81201c40c042012460800030945e1200306958050303e03900c2c0600150705554040342c2d40c0c080000d4288007040f80414440340140c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 302277023 1250 302275773 302275781
    0x306020901050f0703050a031103090a020f190f081204060912080c0102072003030918070c0f0f0b07030228020f010606110613050a0b060f3705061804 66
    0x1020220503ea039514585c540903000b40d003c2c60030070340070908100c0310b81400c410f198150707886103101401030302070942c55908000300c0e04a8180d243c1d51081d505407035943c6040b604002039001e406003c007ca02003074100041da610340407100140030440201004140b0800350b000f0551400c989403a280b05140000390b00e0820154000c95802c400d017580b0108078274003440022105807141c2800c014860961404c3c100c00c0c583c4a22890f042030b41c104200b515211494402d0703008032540042e482c5044108041d01f40e5036903414258280c401c0c0d50006c0d6001000741804446980e440d0000b4482c00d0851a0510082c00301c0171516507106404044bc1240d03049164060007408251000032404c0020081e0f13940f1010003400003050345011401e02e00c2000d00159002c0e038500c2825202d070b034110006003070f11189c0d640d442c6a040401030149400407002c4001c00385a07110581841a0b4290401c1d4110158204010319000c804850100040048001400b0000c2e608c0b00750450361004414442504d183e000304000c507000d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 302278273 1250 302277023 302277037
    0x2010909050c041d2a12060a031b03060b010f1e0309050f0706030b0609010c0b0a0b060f09010f030504021f09080a030f080c09060421050a120e120304030602090105 72
    0x15561404c00000c801c102c40c2064070440c1d6850b14035182100084a60965180d60203081100000030030500c081c615404400c07030743c0f0070401000c081c1c0440d100e5a0365030075100c0c0000e904821030f0f02d100085c0304110240c0190202200c2c00c0c0f8255036080c0140800901c0c0281003a241018905011070500901e40309802861000e5004400c46842c04608032505a840301c50f0b104132000a40780400b044800d180c864200c501441c81695408031002442c0c0342c42c1049100074200c0000c2c0c59071000101000e0710703500098240c1c107520740c00c02e6440700c1a00c00094107148100030f1003030405181008000c016500c0c644152001007102c6100103442c211813800b40d41d0b6907501c0d001006544203015584081603030128540990541555582040ba11000d00032240e900a0103803071540450f00b44004d22100581408a001e0002c500100c0306010100341c0b9801e04104009009981e054511010a0702d13040d0014000701014406403404200345e94180981c640307030b00841c00002c000540020306a0341982c4500191010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 302279523 1250 302278273 302278289
    0x60c031510080106020c0d0b0606220905150d1709040b180105041b090506070204021207030b03010e0a050a080d0b090109090303110703120906060b1b070e0402010909050c04 76
    0x48003080780000b51080c1c0c001d2040b50700502c5920006059030400c8000245200c0c0e00040b2600b0a4441034100115500910403664440521081c441140500b0b487c030b410041110301800145810300c1c0f0010f5507204c140c0d10209000342090500500080c44840e501c440714154001c0c003540343e00348140060050b003c8000520340c04661200d502c90540d002000250417140202e03010010031b812a182a228000117102d05000b19010700301c104400c0c101500180031030762004000510702000220070b424201401e407502ea0010303a4480c0d10440d5814244182d00c0c042c1c94403001000c04041569540366201d03009000140152008604040c205499400c00102c00d42c00038104400c0d90f07100e50990707004000c6944240c000a080c5600180402ca2400c22507800d9501540c071035004002c0201e403c400303070140a0042320400d545010001d0346d40b40101c054404118a00d500f14980c01c1402c00d003a1411065401c2600d03440014424000180c1e0055650400c07144494030104d2070b82d844142004850090740c1c02060 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 302280773 1250 302279523 302279539
    0x18060f0b1306080f150c0c070315090201090b09031b060c0a08121303080f0712050c04030c080c09060d141606110d09060e120f030403030f11060c0315 66
    0x1041c1d01840c0c001d203054401c60400c03200b1111030307507041c90341d100340e41e901142840d403010000c10000c07900d40000307082e10301c1040d007103a0b1a607580e6075654600d0801c280c0c1d8070303001070380d1071030303084119a4006003070002450584540e50602000d4400a40c5034000c0808202c07100c0c0c0070030201103c60300c0c2c40c0c06581101001c0c1083c2d0b03040d004a4203224010b40e00001000945210b11400141810305141c04507400c03507015138440030309550704000d4103020440035007140705000b00400007912003400b138040d0f68490b441142c102d5807201e1461030883c040f4003298000283c075400282c3c010590341c94210300c2c99400748084500d03a00c1d98119013801149134507100c602da0110b0041d070034400e440c0d20741108200211001a03484101e460481c94915031540ca00c1030003400004c00e4400e0420075030340b0400c035088016000800041d6101180e111a614100d0007441103a00c03600007080420038540c04c1100882240014140401d0080254440c0c50311260001c00b07480e042480800410b0002d1510540c2558000c0043c00d41c030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 302282023 1250 302280773 302280799
    0x14040b060f0405011e0801060c0f0c060908010e0f06060402090a0803070b150102010507080a0209040605091e090f07030f0c030f0f0209011e09090302031207030e0d0318060f0b 77
    0x10300d42e40180505400f10300d002048600400b0a00c101e2025000a0b6450b2401a400d00c001250703086c401c40d0b070030350700100315000940100703482402c0b2030020150340c2c55841c2c82e41e05e071240079829074103042e060900541043e02058560040812403a900220440c1c0041c4d8864003440010001c0e041500107201a100102e146420481d80c02c401e1805081c0d021a1456031030b21440049007660800c4401c0700006000d00301161603007900d5000f40085410090021030200d85503400318401803012201c804c05909240288982a90481080d580290141014081e90900c103411583da0f4a664440100203c80c00c4c015401844513016041014552101d5110489009810180d910301c14002c02a44122418800003801c191a01c0503054408405042400068607005030f103001048040301c00d60660000700011210b4951200c2080e115541e40d0300c0000e50354911400c034902e4808080004410705142c40110203140f0a003a28214015510840c0030030030703070010213400e000740c810080d4140d00160796000c5c203 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 302283273 1250 302282023 302282047
    0x606282d0b090102013e16080702041d06041b0f060309020906010e0d06020306130504050708060c04120809030a12050c061323010905060103060914070f14040b06 71
    0x42802d00303401d0740244141c1c5c5450f17001c54403000c42c01000c03c2051818001440700d16400300940d00c18422a10041400e2103200c0008001ca4241010f08541c0100001030103000c500e13161051070213042c0200081004090307208000c40e5208000350000d0004444140480000da000800041c0a841c12411405600303644078800f901610401904a01c00e00d400301c00035a032944a41d00d4602c2c0c000008082c100c0c40341050312508000e600c080c280540202200c414400906044d0044d280910310030b10003014528a800b04c20390038070700c020700b03802a120410017041226280030f015560009800400b8240e5500100e00040e20f000380c442001061010400040f009054020b0042c011107a844001d4900d503580308040c8202540c3e60090040006802480c40c00d20100485284885500e0900000440d40b0031074032540d00d0702d07030242c2c02283c6039616034a04100b0030940141291801112030f009001c480e042c81441c080e6044540075001044d180140c6488003961140c0140f5005c51300907110030b589103181908 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 302284523 1250 302283273 302283277
    0xb0c0702150a230a031d370206030f070e131506050309030403060944030601020604120522090e030403170703030e0d020606282d0b 58
    0xa8030046030a01c41142c1c0d0710030242c51000101d407800843c3d00c0c50f15142640540c02024040481070301805840010a2411030030415064060f586031080c1c0e400c0445164203045042e07108174204151002c02c07204d10016107500c02600e811000b6081841001d554480d000c0780c030070036441c07642988400102032a1400c54419801254010190133016240c192940c0007520a484180c40c40c1800d1ba00c1040108080f403a16848918840c0c441d13241040100c09020342554040c81d14406e44541200c0c030049805443c580d106005255420014080d085180850000c1d45500d03000b40040c00342d800000d08011028416003c440b080e20304150f900400040150104000915600032007100911700700750b210180c3c1c4000305035000c80e0343c0041c8125007001044c0610025420403a0114140760f00c0d4190399a00308000d10500040452541c0108002e01e40b0341c007008081c0d03009411407d4503180c5003502c01071404410f140101900c4402d20a811420845150341c4807400b8800025405000300c8600400c03031510040c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 302285773 1250 302284523 302284537
    0xe07050306042702010e15040302060d060b040308091f0806040e030c030f0405040e060f3c07120b0a030609080c011503050c030115120c2114030306030304030b0c070215 74
    0xc0d4540c135045040c1d040c401042846800800d1040082c0070800051404038014100c0c00203300022820030f03506c0e2846005078020380c00803501a100440c0c4a01039041810700200381d5a816210820441007480010b4a03150740a888d29015545810740324150020410484000d20341140c201ea03074034100b010b0824540d40042c0185803141e424401020140c0500050490041c1520b001042040d12a880070b5001e00500c4807207407030303140700201e5400c1681c2d9200158044401c0700080520003172614a000410001c038580c0508050361034013560083d20b844a03144007003503d502042c00181030800f810407e41074051528505055030030609103a02c8041d8088002c1c04603071144080b5015084a002014242c0d444240d80036010010303004100050742c1d5989680c08083d019010303c04805448650945d0301c1c0c0e40b8041c1c1100c90021484441d001c025540310110441c032041070280d802c40c2090000280c50b441144400713880c425050340071800e4010300d1002c980310036034004d10031400c0d00c0f0b8040c454051900100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 302287023 1250 302285773 302285777
    0x3011b05120105060f0f0a0c020901031515060e010e060706021603200c1c060c020303010807060c0b06151b0703060f1503230f21040e0705030604270201 67
    0x110000401d8200407065508070a081e1001718107160380c0051009803600000030754420420108540e00142c0c4400c84014041c6000310916002003400d211120140c0301e111650030403540b4150710070440301e5442186940448024a040e151080082001505a0003014009846103200140c2d0b00b005110341110418614402c1e00c408000d003401c0691826440740300314400906402041030380943d4a00400da00c14070101c0218104465441d81c1c5401c001c0355040d0f09440c001da803000005000520301000450000c0140340b40809a9256650b181c413650f40e005041c06000340c6160130b40c142111024001e807290400074403081d1500c204034400703c40d551050740c881524200d01d84402002080702601603000c4504a8401c01c4a641e450340c0d644a02c1c10501258081b80c0800d854006211201c1c24030070803102039034a500074210f40301e01c071901c003426040c2029401813110003084100020410507020340d0f80103d1505180e80c80c1d50301c84011401811202080201031308680f1024070382a19440700c003102c494000e03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 302288273 1250 302287023 302287057
    0x309030615010315030f0209040201090308031f15020a0b0a0b060a0918050609070806030f070f0e06010309350403050102030f06030f10020c0c03070608041b050108070e03011b05 78
    0x24044c80c0102c0e07019400302810a02c40c0e044042e0250406c0080507400c14410316000c00c8041c1c0d0ce49504019030000d41d841903404015601c0c1010300200f02c881100500100b655a0080c9800507401a6484d540030a00401481307070700300050081d1550340e000340742115019001a40e5002c04000041c440c001d180110494281c5800305a0040107040c42828894040900781400c20348400b4426141c00e00020182581842106500103480c081400710100900c904a0741d40311483c1065214440c41d0310092015040500d049010070100381081c03051407040100c12018418100091400c11090050740c030b20764400700c0001400000c000301540214031940300c8081200ca2519000100364031800a041d618516030301c1002055846040c82c1d005000c0e54114904443c58401c1180101c2c0c20b0040650061012605803800c10040c0206d0110404c098210921200030385410031001038031126010303202400300403404042c545103490275485140b4480b6014111310f81e0290b00380c0000e00941c84881400c944d8600 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 302289523 1250 302288273 302288291
    0x60c0f0f01050402010c02060d0b1e040605101b0816030f021c05092107030f021005030f13020d05011103070f08010503060105060702032b1b111203090306150103 71
    0x81031103030301d016130350581d6000c2c29a9815020007515401c030687d01f2074295038030308604a0582e02c201901040381590095020b16a00e124100001c44146038003245c0203400202c09118020340c411000d0841c4810f02c5040501c81800b81080b8610340510040c02e45e044c003c9000f001c003419005000401d100c4441e80c2165045220051601804a10701d00070b28045241800386128528000004418060560000302802c103442480781c0c0c50205150b10554079020740d50540e1041d4106003864101c0300e00c10382811461410406600c2c080d81000030036107088840b205d410f82045540b91049008101c0c0c00c10002c2c0820040748504000d154400e8071101d01140d1900d81d401e030820b01810385641214002000303070411368680024081281d004000c1260705029807410003c0316aa0700d41d0b441c1c8100704450700034490200401003d451013051032850080d07000c200305080c000586105411401c0d01d0305640000d488071910005520b580a1429140c3d414084d900801c50a513502041a0880304801d0340c0074843c2c400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 302290773 1250 302289523 302289553
    0x3030402040b0f0a06140d020403060603020411070803241201052a030c03040215070501050a0b0a08031803010608011404020306100503030703210203070809070f1214010902060c0f 79
    0xf03450741d4190084030601041104500848400c40300c1c01c3c580d482c840c50003180082580490340260012a1450b655280078401e5082c5842000040b01c891b200a82c80e16945407240849030000404495100c0e0b07454014041411844105150707a0030045e0010380c1d0401c1c0380c48528060002212000c4e6024208982d001c201400f100b010090003003020185461a182d000001d006c5500c0144140d07004507182001d0b40c550815030004000c100d0181c400013901e4144415a13100b5102c0c140c11080c805d045000d41400304200205c1242c1440c10107012000c00c120725400482c4c090090359201c103d0b15460328151a00c0715000c0610a44901d1084094039400d680d2030708071002e40f02d0903010b580d40560003803003002e0000340282c0c03108181c440b2145882018140314482a026a4812035040700010110424085041002c00002001c1c10a04000303000040c100383e001401d00000d4a801741a102c400400000d0040c001e40c0420b03882d50300984910f036075070111250599039040800141200703201e183c5950800322 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 302292023 1250 302290773 302290789
    0x506190201111b0c1c060902030f030a090905090c060301060807121817040609060809030403050316140a1518020301020f03040c0f0b120406021b0708010c02071d0403120c0203030402040b 82
    0x2c0c0b06010800118201c0d4440000800224104981504c034203412b20410704000c10142130786000e240d60341c8003094107044a03041a11400381c880c184950040700a014540e903624103036415104580b0705049196600c000481c0d1a80300080000b00303503880c0142280a0880c2c59403594280d078050360100503031b080810030400c164410361088800040d0404400d020040c4a1540301d40c0044c01907084a041c5512900c85a0865200100c10b42c84c0250001da10000c0016200345501800e00071005408007959680791400d10784400d00b108804070351b84942d2040060342c40f0705001541c0e0b8002d4000c644a4101d001c0001903584151019104140c0700c00c00058020912440b450580c1c5001c0665403c00d981045401c1b6914000b50045400ba40c00f0720030b24036114440010580d45400d00300003400c00074540032420f800c40d91211521411504081d000384200401d05806500f045035140b05a141c036a1181001c4403450018040e040e445802c01302403181540e07000000d0b5010300c1c005c803000c0054821020805c05a9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 302293273 1250 302292023 302292049
    0x60a051206040609170307021e0f0d050a120515011b030203070609020607052e0605220b060711030606061213050705280e010506190201111b0c 63
    0x5940700c040094001000c0b80c028035041441451794041515100340d2010305a0021201c2c040148e100c1d050302c0b4024246070218a2002418402500600a007611241c1d04d0b403a610501da020310100084006406215084081042c138010030b0401031401d1041c285c80525107480032450000da910a41c10078003d450032200d06400d680754000398601401a40d0350300c0548503c040c20b991000040c0002404144140042d01e46c540307a08a400070000c0c80055149070031301c3ca000300300c0320841c03802c0c00030701080e02c84400809490b03805940b4107034020f40c03944116015115086156812560102d28a0100701d00d0f1815061072840c220242c403201c2d50740d20180402d9000710360b002c4d107682001e0030101e10056001080d41240e140110140d41c82c3c20349500c00f0540c81b02140032048204000f1944a09403040c000e42c55102820840d1504440303549071400294840c05941849503072810241c103405d1959000b5030100e6850100b0801d0395854a1000c41310182c500c40307100c00f103a16130091041c0c685141ca4420401419 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 302294523 1250 302293273 302293309
    0x10629090a06030b0409080c0303040b0f0709030f06060308040b030412021f02071406131a0106020d1419110c01030b1f020102040801090c050a0602070509010317090a0b03060a05 78
    0x1281c0b40c090700310003034815001c00c15041a940c00c0714002041455004208005802c0700441d03403420241380c80306020a0081810600c2a045014000820392141d680002c8036040b074905d01d1402ca40b4204100240481c1d4002420020300143c002403038400305c8003075031285004801041c800c100d500c0c01a42c8170048400c0c0300d44925030502921404441c00e40c041d01d00c0c140181a040038103032003400310610705030b01a6166002c000903034800c1d2040010390303003445004100c0014a100107524041c001303551520641c1c6180280300003a180c400d000c010b100140d881905a9800303001c01c0000f001d9003c1c25022401d03c203050305000c5c00f49524015406070040030180100688007001042c1d410040c031a9a440c00d81c80c040465400700400110b84009014100070980240418110b41e850a000c100e0040b0042d0721020540d00401e404001c7d6540e1203d01c0d0341102e4004510301003c1c1d802c03a00c8462284202200c803a40221420070210f400c03040034000d10720440341560300c00302050701c400030000d10400e13403500305003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 302295773 1250 302294523 302294539
    0x20a0b01050d14121b0102070209040209130f0305030a0c050c061503010608010f020d200a030c0c0209100602010e0a050703080a0207270b0402030603031806090301062909 75
    0x807407801c0c00400c140c40640100c02c40c00742040070070301d1a420302200c00254481d214000c034580d111504c10100e008035580081008616218041d404106800301c024000f0b44140000d50004400c1c4101e007244061981d48071014592400d174604e0701800700e0b00151041c071a1249400b01000340039005070101d503114040380008010541d2201003048100c0c5180c07586503010354840c1d000060690090044005c1c20050a4026898004040d0b5800031140206c1902400300c000c0c121094004e1301d564202d40320405607141c0401d0b00c4140000aa452402d50040250801040d808000c5e4401202d40d5090030340d0400c1e402442a444040d42e00c581c0e40100032000380158000503001c10010340e4040091a48110701c1c01542d0541c0d503108414141140e010410340013a01548080300c684039221320400c61600400c807030443c210306000c004660f03a405401051b09104001e0b40c00040c0300d5603040d0030740d030305600014002d006241d1035200d6610410300c84100034114804840f020345202c59400b041d1039038180041c000700 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 302297023 1250 302295773 302295779
    0x70309061205070c240e0309040c0305040201090b030a0605090414060109050601200708030c210a08010b03040201031e0c0e090103030f1b051506100801050f060705122107020a0b01 79
    0x102200c0c00000d0145e5840000307001e40380181e40350052100c02043d00c2d014546460030741c014402980c6081080c00c08051515041000603070700206414140c41d80240311945070790360b440000004008a8004540c400f03560400c0104000528400800426003001034030701e0790340c1e554100c4080c0c0314155a55030106400000710b0140030020103201e00800040c070101e4003541d50790003d00341503601200348642d158210001058401c0b82d1460300202c540050001d15160240040000f081c4d58018055412490000404602560b220390440c80c00200740d01e800f0b080054031400510020140c00d01d0b00c802140034040d0b80396a61400140d40c0b8102d03a01501c9000340e8141c0914110b40f0143c4a00c58407121103060205500440c03000c10600c400034064174180751380307410074008121103602c2a4810004105a007001400145c48076a104001800306480b010349408091030458141150300107070058030705010901840210a18024100c02c40780d010703a5000ca6141c03c4c80c1281c40e000c407410094044200e9034010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 302298273 1250 302297023 302297033
    0x31b030f0e0307050901060801050a061b03032a050405031002090d1209030512040306060e130b060a031407050f01020303040515040f02041b11010b0a030809011103070309061205070c 80
    0x7081c103032401015100700648890000743c0c0203c0a8101c000040d20b200014403044c10108151005400c5a0802078440c011081c62510540d0345880300404054403410320b15501341c900d440d54100000008148a00c0300350300080281f203504240705441c07192051138000031969003a842165004400076100300c00c80c1c495511a0200081c0c40e0011004000120030300001044080c031140750591078030410710f039440b459810301c0c42c2541d4050304102d500a4410781407080c10080100340000543d0302003041d02c03141d50340000040000b0036a130700182078890070041019404c100862101c080e11002c5601c84024041e0800481e9240011100201242d1180e410008220f400701d5016620510848180d41da404040d804038041c1d440c5c144800c251341c0d00f003401a80c02c4a0304245080c4107601c400d0300030411803c00c1b40009141061038800900407000014001601e1303489928051100c2d000c0d241207035920a0382c1e10300201108818403404001070408050b88a81810760f002e46800348d6019074072454141116110 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 302299523 1250 302298273 302298287
    0xe030c06030907030503070516060801141012110d0c0804081e040b12040210050c031b070b0a020304090f06050619020a0b0a090201080a0510060f03091509031b030f 72
    0x502d50144204000000000d10070001007500521910182490f510100100c4480c5c00c9281c0019080c030402c000180f0801010540e0705420420444040000c03078000d8800fa141e0000080c2c0c190001030800f0140b00c032501660004058030701402d1810130800010540c21110b04409680042c40c0c1c8074100712807845ea10044912940c1c5a04202001d86000d60b140103014240d40034145d1030030005c1224003080294174164407014448038440c20301c54a408100368441c2d0300ca01c24071035100d8464912618618012004201e07500c0030f050321101440d80c55107080c8004e944c9800034425010902d00b0805072006034805806058216000505041d060500b07902030031000804011000045105200002021404204500d0301032142c0c01400607501401d80001800000020668014907085c070041c8030001d0f2070481041e044a0403480c0c01402000021001c802400c07010002801c0202810341413801492540d018882c0d0368466140e00010792250581c4201c4442e407041c003d030119100043c200c1c501c07801b541c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 302300773 1250 302299523 302299531
    0x1104031b0905041406150f04150b0f1c060506040b0a05090a0e060103380d1703060a0503010b011d0604090203090106080c030625120e0c100e030c0603 66
    0x21800100c81c0c07500c400500712041240c06540014091358100c100071001e00c8201d8104c0c0b002001d08428015800105807020004600d10340510382e50102c0452480c00c0740d0400018042d812100780d070301c2c1620b25185010760070911035100c0d429200e280d868540381d014852441100c03409000b880c141440c0241d0010f05800a0603900c007841002c11103801c803a035a4005010203407034406001081400d10200040c2201d6400c01a0100b40008240c0d580714a4030954a1040c219083c1c02c0710560070004001003105490900001421116030349100c0303c0500500c00a1413060009403441c406207a40c071420582611401c42c8403502007440d000c070b2900d0b10058450400c0d100640548050314040d66403080501301d81c4100c1e03140c0066559680d0502c030000c024022222201c104400404031400d02d60f0321171180c80d07803443c4d40285e00310400240710900390142012800700a41841c040100050445009840c1d51605518520840d0a00d07500b071003640c021685100341c034502400601c0c447d00c129007400320a0340301070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 302302023 1250 302300773 302300813
    0xb1302100f0e01080411040c03060f0b0711130204170d080f0105210c100314250e0102190605070e01020304062003090d0807060f020418090c1a040602060901110403 72
    0x124400187c0c03114002d80c5082e4040d5540002c01918124080d2410402600002c0741d00740e0410010010842ca03400d6050204030898502d540c20580181e0b1600070b100e01e501c07411001d03240c00c043d64140c905c00320740c10700064165140c146c003968031100720b29103000c000d0150561122907001011175280b518500501e004850408a541084551001609141502000c00c0001c0c1d2a070400c0024500030320b44a40d004008508088625160110000e8142618903140340801ca52100000d06987c8208070554562284c4886014240403d09011003d044100d81a4002c100318494265041d4400412907003200e04e60340d2081100b02252895800c500a25005801d1901c828001204103544240000210328400c449480e40d4814a01e4140f0a5481201c2e040c0030141c41400f0401c0802060000300420a403100ca0010707800116190a0f41441d001c1c0e00b2665102c40200c90480c0300b0400c20004000381c175156000c030b82981d40c0340201503007039131420503048565030014041000040c80016074029150a94 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 302303273 1250 302302023 302302043
    0x301150f1413081006080d0807032301030614150f2101021e090d0b0703020c160501120603170724020403030908031306110304030b1302100f0e010804 66
    0x84503080e4510742009030501962030016100304480d000410000300c0e24101c0000612417145884c0b510b071b8903250740080c680148080c2c00c001442c82886644481c4498441200400513807005036803150703a5543c2400100c0300c0c0d51030244001ca441d00007255852040488410003021521240d05104004400b9040c80e90010450b8546880460002101082c039510300d000040c0c48100242c007005046c10700d40049003480e003040140c1600c0391941c10045001c00e80006111034140c13281c4504a00a1240803509032143c0110089a0066045036003850100c45090303881140a00c00701100340708480300d510006002008449130105107418101c045c0c001a8040c001000b08050309202d0940314603000030010178000d81c00201441010f80081b125400b400c246000ac1d800c007800309420202982c2d080c06074005100801405214bc01810000c440107594031404240d09403c0009a85403280a100c1080f4483c800105540551912a00c0f81000000d526030b540101b0f03088074401034400200150096840d2a45 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 302304523 1250 302303273 302303297
    0xb06130207170c0706090b0d020a1125051507060908091003230115030509010b06040308130b03060109180b180f01061d13020c060c040f08030301150f 66
    0x180402481108140402d05548102805000382083c0303664201006000e480002400425014415104c000301c48000045e03035000c40500c03d41d0340580d00325250a00d0300c41c1c078000e020a00032180c6862195404800b4554045840d40308000050070140018840b445084c41402d002c82d220740c022040c1180162441860305046002080301d154a0314054000302c1e44404000c0600c04241101e0194440c06c04003d404a505144101c081004044400410941c40780080350a0b0842076010840624005000d203a48a940c0d00d005a0580c20000802d5411404964006040b10503601103038414941607440c444064101010a0078044817441110b003c80d603600d030340020603120f01070058909894003a10f00d0451030f0640d2040c040d0601604180104418820144c070009135048510080b0f400c22212030508040405003040240129483c552040c81800d041c4160049900024000d80311a000d0540045071546000d5507284020710131000c2c40304020175041c1e8914443d100709400400245459007071801 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 302305773 1250 302304523 302304533
    0xe0d0302031923040b070e0d1104051008070f0e100305120d06051306032009011415030708010512060601050306040e0c030106030305090418051009080c0a0602070b09010203040b06130207 82
    0xf040700c040390003036840414018416046641030307001440c01c503003959412409988030b02d00115010052401152110b000c41e07500307141c004101014207000000c4507421655400c1d80c0c401e40b201d911401c0011300c0f0030008280c101d00c070001c002c42070360780040c02010300380c1000440342c015501c80442c40d03072015a1614042440e40d2a19000303c4442e05105020503c2c1d411030402401e42c2200c40c13000d201c0c40c501d500c00c007440794503804003080c11616406035500101c410300d00412884d00c0c2403003850600c50000010010811340208115060f0380094481100020081c4520303655120103407640780c00f007042403000490501d82500311f5141c054040007556210910351740802e0958240790011001305601003041600348c00d013407040e07a481310300310044004d03c0302541e01d075a40c41d8810803002550b201c0c0c45018040500000104407400e80301002c081318a52002400c04000039008494211480810407011400011050007a43e00039504201e2120307690716150108400c4d141d00c094171b054440d809001c6d21000c50 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 302307023 1250 302305773 302305841
    0x9050f060f0f130b0a2d1407021c110d080f1803010e0106090e0c130c0509030732060d0e10020d0b13021c02031005060a030e0d03020319 60
    0x51385030180c0d00e40d002001c01038000c011913513100120102c418010043c480895080e0002d841803030600113400c2c4150784040180d4451504040d401000d040512046c0102401c85d80d502903000342181145000c010041122070f084540e0050070f464420b01c00303216030310001030085c0003980c0101040320f4082c01d1003011900f5902a0517031141c46135550f2808200c0780c001030140f824041c81d00b20140103510050300c00514441040c554040940c2d549a84480280d03001d44200c1e208240024101d076026030b56844101d0b044031030242c1b0840c10f02c0d180703003801100c01d0340c0380d2569802200c000c00241c2481f00701142c5030010b08102c07020b44624400e00c1648003001b13a117480102211070130564003061412080c014091408425041c40302c510344100321801d0315080540300c00225402038000580d480d03e40c103185c01c0c050400340d080158400400030310b1819040d0594040c1c60030201c000d09868003001c40c641d041d403c90108644824000c3d8030a10850303400f000d82c1d8004802e80d14000030b10403180300510755230b110a03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 302308273 1250 302307023 302307029
    0xa0206181006030b1501050415050f0d1d0d05070b01170115080a051e03030712020f03070c060b0a060207050607060608060106020c01020f061308092403060109050f060f0f13 76
    0x20311010043c0710300d0501701c0960015288003801d142d8585450b144c448008050700f0301c01d5070200040807401c0c8140b8603003d0300312201c1842503603082c045800c00c400b80c4a40000000350000d09441400172004401d0b00a40a81d0304a680100d03480007103a10b03204003d084100240c2e0b02c00401e55982c0001c4051618008029016110f40c2d03004200c080d01519009240c00b0905c011042a80d00c05103c1d01031720b201c00401c99030b1008a5140140807204071100080103409510031242c9980300220801000c4c031750000e01d40400700c0c01881c091101603680c00c14802c144415006060050304840e40600c0341381032007001065650700c252000540c055444d585d0504001d0280c006000680000408048644c0d040042915030458500076002c10b007802d510000c17081c1081c0d800100610700110300e0b018569600c0103203030043c1032040c041d4201e001610924404942c0110b51a0740400c00411012689040c10508000304050190030b00703240894008074010150070441c1805405001002802c0d5a101000038000007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 302309523 1250 302308273 302308283
    0x4081801020304360e06062110061805010e0a0c0203070507140411130603020c0f0115050103050906071d040212042d0201020a0605041407060201060f090902010e1003200d0e030a020618100603 84
    0x2094105210500b40c000302f064100c0e15581083d00511102c00500006504603003018400a608681000180d0a500440c84080e0150151040004420410500c0c2c2c0312115011502001000170011854072603010b00015642c90b49540f40c01032003030901035802840074060031012140c401030070451090030f6840204204140942c1c40e1010409560540a8950010032010160240e0f01c3c102c0c0c001446040c610b11008000440804c1d182070b0307900c40e41e040f00c001c02c818119603c3c0c17901d41824055500500031011603011190340803036286c002c1440c01c00b46000ca074141d01a0414242c0d68403040060440903000f82c0d010710907080f14480c084e4082100d0300c005c0c07050ba0008107606280007020905407040c0d85c0107010207401c1240c000b0050703a11040b481000c51085820080000074071008800800070101983c3c071440320f010382210300d00c140342c001e01104200050107002c50f071141450070b52240612280c800140c1d0208011603076100c0c1c00c0e9195880d01c0803020485d4108408007004c0300540c0e05079402901c8e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 302310773 1250 302309523 302309531
    0x311070617090a031e0903061a150406020727020307080f1302010f0f0207050301020d0605041506091214060f07030b010804081801020304360e06062110 67
    0xd5640ca80081d030301d500c078822030064075800f12141c5019000e042600782500c0604600d40c80358030705500a103070300c0020310f4010004001403004940d810450113511300310648502440c41c850716038228020100c8003542c103158007400905242c20440b14240002840820f4000f60705040c50507080503d1019500c200001d56520602c0d00300000958445030005c4c001592601d040c103188000f42c1d80090404031025aa1b2400141c9a50460001c81c10114a42c0007103034954000600300303070b81d11002e0304030750306aa00848041240281c10070800c00329a81c18030a0344c01040148204202d9038410b10381d414030070780c05a4000380030302a1300034001d402c0c030a0494100120804440601081561502c201e1490800a0900645500b0681c0b81c4020900a4000084450300040140c20450f4030920954008110f28034a0001710182a01800120b03120400c288419001045000e0b000d56003a000e4414011048800740256440e81c0701405442c5a12400d0724603100007010080e94003840420181c00c088003900e00000d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 302312023 1250 302310773 302310797
    0x30d090b0c0307022d060103050304150905030a0f0807080f032d06091807090905060601081308090103092f04140a0c020a0c06030e190807020d03110706 67
    0x182030030006444007180c00303024010802c405400103030007072100b0442908100c03003162000860750189014500e482042c040c51000004100380040a00107542849020300ca141610180448145a10b48583c6a06074000316850001c01c0d01c8070314666030749002d200030901c0c0210030380f21078070142e01c03140b0081c5100600104104100388036145e095519943c1c0d0441c07000a4131914142c1c07511150180190703100303115036000702d901d92840880184d02041c040c000c8c1d1311119a50320714003000381a0b58405071860300495000400a41c46000c020f88507210032040b02117140510380b03d8102942142d04143e06169485101d5004540c118525038545500030f102881210038400070000c004080c1001300b1701031410248807809004100003d103034070040484000400c1400d030182249851091360303003e000301ea600b61020030203a80c183c125091182081045440c40801443c64007005094840f001d07224800510001006250500a4a021600a14104220301000c503083c5c0d00b81f4800c0e0b801400469120072182c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 302313273 1250 302312023 302312033
    0x512121605010c05070b040b09031e12010801060501120903020115090b0117070e0d0602090904032006040804030312110f070314040503070b0705011b030b03060a0603081602030708030d09 82
    0x183c00081d46480c21174284101da6488200c1120040d1004240306601400102d04820070001c0e120391143d1041c0c1412101203041203084140c2c029a10901076007002c000100300c44905018500c02c8420603502c0951414840481000504044c407084085548803038080c4410125040000007505000c500064540e040100140080034030302c15250f108150042007045242d0081500d20801c3c0741030340c05e840080340300d180c4403000b403203400140ca600480d51010f0006040d40011016511641d0a0940c4a1314015141440d80ca96084030000c0214204000038000a485042505048401d0b0070011400103c0b0010600c03190304400040b0400e14408a4005c0c00d15600103064a040d914503680245000e040c0320110351228a18061340c0b203000400540310b010013400750b0100380c4172604140c02020240f05081c008001d8201c00401074820b114032808140401c040d032054000b100c3e0300c21501843c0c14000031680144031620041a80e16000e0721200003441c0006200410040c038519400003035002062a00c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 302314523 1250 302313273 302313281
    0xc06050411030114010605090607020301060306141e040803040f031b0303020a1808030405091b0c030702040f0203070f030b030f0609030d0c050a09420219020a051212160501 76
    0x424404c03c100c900c0104103494000e02240c208000644181c0d80c0d5850701c0c000b0901420b0b090b84002c02031450415080c1341c20002c1d007001c50080f50b042400000080440300c0e00c030554141a00c01410350b000130030209000900045c0d40d05451442818018540340800c0c1544130819031820301640400c4d0006012000c07103500410f180460030440c84410703c3c076414038607410f96a0050b80603007400f03880b803900440c1000e22420304070320442007200155581e8000380c50540b6102e1300500360403406a401c00000c6812000d460098074450015640c80000303904080004502801c410700c00a1b070180284c000c603015800c01803040f24800c040481c000c556035010072444104031280711500e001005006d008500305980c4c802036080880e0100b20b4201122618401c4018580c2d4040d802400014010f0705036800c950b1084401051509a80d0240c0b0f200500c41c41e204440c034006008001c1d444040000140014540036064a06802d038410446c0c0096041a5407035100764880501040d1a440e2415000200f02003405 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 302315773 1250 302314523 302314541
    0xa0e060a060e0f0405030c030f07110a03030503040605150d0305040509130c030605060406050a0e060102010f180305030a02160b1906060f0503150622090605150a0c060504110301 78
    0x9042103080e20b450752055840ba00685140503a101c2c0d000400c0900c14100155032920b0f003900c095994540070b2204100c0240e100070070071a409603224040406501d0303da80d6100032260552640d5140d0b40e25696410b006100c01000007210314040348030121551110300904900ca482511619134036401e007410000700d02c000030105400c1002e402c404600041c0190100d408403548200049000c1e103451000401400c401d4100d02d0300445103040014001106035200c6d4002c1400b070b0003c000440b6029440310940c1d100c103980303007a19500e01c416880000e1041000b541d1203c2807000043c20044006c4664020001b26841591004480003c1c40b80414900040d070000100c5804100042403a1080140207035504034103120501c640800003405409581040710500040100083d5581211584810b10303030380480c24170381e1110034094000c501d842d261b204643c203560004202d07140c5d040087c1c04203101075100d0700c04401006035a188000015803030340103840c026403107800c0300c0c0c101142d11f1052500f180d000003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 302317023 1250 302315773 302315791
    0x8030304030c0210110d0f17040c0b1804060305160e09150702151f080109050c0402070201110d0314060306061807140f0406020c01020d120203130b0a0e06 68
    0x20910000a0300311106480041c2d042d9008028402c1c55581540e9a084045480c60103010380810072240c103501540d4001c2031030786130716400c0001c2c90f2080751410110045034001e00c2c0301c1c1d010328248004002c640c0542524108070514144003030f00100072a003990540d5008035002da0240c4040c01d030107000c412218000c2d10182c54003840c00e240860420b0307a41d0240ca060031804401035000300d041d0b144280719003250780d107010260340d1740d5060030811a80e609840c1544003c5841000340042100c9406000310242913070440c00402d03c212441e0108402544003407000c905201038034040186c291001d0004814603070440c0c400255030041c83c0c40b44800000c0013403295111360080c030100100c543c1c8001980e07a0ba240290581411aa034241055620200d1a08028190f00c070205c0d00441800c00b500090090751036a50079184109240b500680c1d035583c000b600304001c950b0000b02c081080410b40e024580c420964240c900b5900030503221583d034040d042d03c02414284d01c48280c100303150f0041200c2c6800414203 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 302318273 1250 302317023 302317027
    0x10b09070e090c0909040b06040621112b02030c12482403161e0210060b0901020c01051327060b04120323030a0905070803 54
    0xc200c00030410500c0d40702551045010001040c00074003800c0c01d944588002070516140713030401d418600c1c4103da080b502d69100300e00b000780104043c0714441d0550721111741420850203581040d912500303400e0b155018250424100400241c600e9510241c0e00c503000821049103c0e520043d005041c00c00d1840b0a5944c02103c09080030000300303900050a24034141c402c00351510451440c1e011885611070703c1c02440c009a403813000c1e00600c0c03000d41d00500500004072400000049110110461803840440f03080c0781c1c410030710000f0b509450341582c07522600c6003490500ea04a01c100703000b400c15161440b0220040e030001380071900091051180e24050496044040c1c2407400e480d00013076458440c41519410003101041d201d14851541000d07002400c000c0614220200310b03a140c1c0040700140552041400d0b04100340000e030300c03075118111001e94181060141307541a503918183c03402055220354906540014a4800722090202d0103140524100c41c004a01c4220307504041d4506026500100216002 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 302319523 1250 302318273 302318281
    0xf0b060609150a0c0b010b040603060e06061207140f0406020c01110d0302070c050901080a02100302030108071418070306170f0703022404091b08040510020d0209030307080705010b09 80
    0xb81c50384070700b14100c1030301c400e0341c0c501c403a22040710354100b0740e00014050300b000c800101c1c00303000710405041540e01e25501000059695a000124900705540b865080a0708000c2080071881c1091840c0d401044c609141c0d008084041100046034864100104e030400c000c02e0522803e68103116921032003e00746006800404482c02a03034030741079209168000e05900191920030030160046e00c900400000304044040d42e511031340261584030301c44040340300340020550808400e001344266410b9400c000300811085050614658048c010f48641d2a031280c01c41c01c032200285010082503220b01d40d036070b0300820310030b140c05d0519900c0c840082070501590007484d0003095a5400060700340840e6011252401810020240603003131400807061140041f000080125000c030003908a03220140c40346000744040e05414034101d5488009442c010000d802521a40c85c01884d42c0d00a0901c0c22800f0000514210100bc0000d196074046070701141e0f081400700798441030201c20312421100b0407050b80c1c4e810f41454 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 302320773 1250 302319523 302319529
    0xa060f0e04022805120d02010c1403010e04020607021c0c0602070305061f0f0303050a090902032205070f030506060a0806100b0f0403060c110706021b0126040f0b060609 74
    0xa202e10094440034010401c0410725004954010003400040c1c8404c1700b00800462182e1540000000040590f00784000d4103181c40c85000120701005102c02e1b120709603400c100d044507030ba81010f0400c0e41d0112044c0f010202583d122402d81c00303121410058a0040017503454054100141035002c00155003065504201103030010855035403010454400503503001500e0201e41ea0028603400101160b1500b602c084101504017004110303603c1251100d03940d1a5494800805920003200c2c0035038045071084229030035103000c04012086502c500b0a44115640340c151206a15000e907100b80c1d035962056042c4011401c20070b0900c0c000d040100040c002618109a5139202ca42c018890303a40802d1000854595040e2080150340280d640250284846004041c0003040022034003640c0c409800b50060008402c3d00005a0040c02000006000e4101802d0350056500c4013003c000c510140d00101d60b4101015000824030f8412481109600074940d4a800c0044000e00c0040025000310000c0180502940d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 302322023 1250 302320773 302320789
    0xc140a0e0c040909050703050f0f01061e0905060409080a170901020903071203140a03020c01180c050f0d0c0603020307110105040819050904050c0a0e0303040b220e0a060f0e0402 78
    0x1a412880100313840d0500d10300249000600e03880500313140290041c6182c00c01c0c0200b003c00340c0c000c40d00000c4c0525903c40c54698152116900c04c1c0c3c1076044166410080b03202c180c1c004a0788080000e00001d50324225403549207940d03201801d443e000401480e242e8107a41b81040c1c03680d4202203454000c50500c04008003290396140303980a51800b0a0b1444000020184a1801e070b28600f94041600c5466608081010b0040d4100040b000419401d00d90f1802d410702400001d40c40c1d03580c04c03a4204d03170350910b414244561011002c071951742000d504808440481d0804140b0001085250340042c0d83c1c0c901a00d0090803982c90352135404069040c0001e01c00850b21144c2501c201880500c5d07a0170102d110a0010789840c8108060150424106005c200042c1d0240d00540021190781e241d0002101c100b00405807a84194065212407800c107105800400b4013520000301070080180001c03460640310030035034461300000c030390645d11a80c8400c4140304007514821014002c001080f004501030070594000b031015 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 302323273 1250 302322023 302322029
    0x50103080a03050c0d0c0e09070804030806040b130905070608010e070801300b100b0a1215050a0e0103020f060306010c020d05070b130f050d020a0b0a03090c140a0e0c04 74
    0x3540f910003258903141900c007214070320f60f04032508010509014001038030403002981e445200b0607030003000900c29030040005c144150f516981d0800c6907a510f40c2000018a004500341e40c102c0c0ea106454080d41450b0300c03d0301604ce0281d001000d00519000004041280c1604103440d5420b4050901072810341101400381540d100c60441c1403104401590b038040c82050b035040070288801c6826400600180e510f1290041807070b101c05074030464a6420140d0346100f845e400500003413031130103d480300c040141c0c803403076013841020741401810380d50398001000030019411105100c00034070010011450245c600a21055007a5410307402c3d45001740000e01410300c1d9200203402240351359100010001d06005420292181030741281d1101e85518518080704014024006404480c80c0301150310701d1b011456403512903008040c1400641443e1300c00301147c00c1281c41206042d2141380031000110038980340ca01034083c11030103a48280980040000c90b000e1580044426100c05090064220401c0221403d07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 302324523 1250 302323273 302323277
    0x2103020705030d090f1e0201110c210102040e0906070e0d030c0f060f111803060103020a030312020c120702030c15190e0904060c08070503090d030e0c030d120f050103080a 75
    0xc031038100341000f0520b0201c01000035095500040c03a40c08a02c19000f4030500030790311a2701c465483e01d4074a81e207004050106074803d42a00712040000010132007210240d40840000d41499036550740010741301004e6501103a51382220080195250344800304003103045003160140f64400c03123524060325074042c04030301500c80e1030030043c26400c1c0020758020103a0500ea4480c1048031803007004d030f1040c0715080310058484446484900a02a240001d03c0c2d40c180c0780c000309201900f9103035950554081401c40000d460700c2d41c0a100850000209004074030741c41200420341c2e0390781d01c240d204150402c2d2040345418440c40b42d600c140080006e80398213407240f9200307030080c85044000c2c0d281c2c25110340e0092140035a00001c4501004100190341d006000404915203418034152295241074803540411691072002d544214a42c1c00c42c80c0c4280c110031002c154202c1500c241115010100f8108048150302401056005008002d002c2030381c800c2502c1c60035000420444c9505583d140a142d100b44d0403c0c400f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 302325773 1250 302324523 302324531
    0xa0c0f0f02150c04171209040b030a0c0308030604060b18060a03060b070c0801050702070e070c031b0302150603030412060f140f0604061208190504080a2103020705030d 74
    0x180c0203000b04007002c40d0010980c41c400242ca003480b140990b030341c098000c840c2c501002e209104c4000d40c2c0001c0e00e000b55400349050604222242080c00010710032040847e41c036104001080300400d1540b84640d0140d402034206a0740d030b103450030038081070320100c0d07000040000c400c000780041c000004800c005d401104895069407141c0040f821400303000c1070b810912100c48006454410440c010403503a040364101c4000780b020360783c0d5600c140e03107840341481801e23907103008040041d1210340700707841d031584192003414540f40d401d4803100000c1300c010301e010b03007200540c0c09060f88041034040940035135401903044005518050509440100409050078001d045540fa5280501d131440300780c1110346c06420023860564146070050041c0715444013a11201d01492501e9001700702018000c154182003904260502d2070700c01d140e0f44a0059081080b440700c00c104040c0000704000105001d0080d005000340d04204942c00c0c0c000329910480607228118090610411400d00061400303c10745500c00ca070044001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 302327023 1250 302325773 302325797
    0x10305060f0d260d020309150717091002070602090a050316030209180f0a2001080c0703090b0f0706060b0301470307020d09081b0d0b0a140a0c0f 64
    0xf16055203400b200381c00c3c248000c241c1c40840e00c8103034055846541003d0449170f4070301c9130200391075038401d0a4131410000740303403454038400c2c40c0c011104080d000105a0b04a401c00c3c06400a071a0890b0894102220080e40010f004400e514150100178054482180034200303407400964002d040c07142ca403100034010580c1c0800580c42154555002a0004014040d1040d082e84841e03440c0e11441428021240d06020318112840d040040901e90800c080c180c480510700d848111440d4059002803500300c040110f1005e010a050a000340030704075051003441e1a58569018bc540842600c0c03c41d08005400081403004001c10503803500707043d54241d43c0c0e031000c80741c0045241000001d5080d0306e018221035000c10780104d002e0351440006502c900079507402d80e10751000b0443d088030720040f03503c903065499105a4441d1242a411080c0300e5100720010529002c3c0070461707542e0885240115003103e91280d440c001700c50a840c0c01c25840d035000038904c10401042e10320000142460b0450104038041201c5a5580 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 302328273 1250 302327023 302327063
    0x3010b01021c0c0606030b04170f09010e04020c070b0306150f0307050c0a0524010b0304020a03030e0112090804030b09030f030109051806162003070609060605090106020606010305060f0d 82
    0x6841d0381d91300140d040c404561241400c94103c40c090b54200c401c40e00c04c0c0b030300440080d504000c0ea403441580c400d0503460503420000450380040340c0e18296900540c00c004600b44030f001000010000c000700342c034075030312468a0410002e18020b28112401510410051080e640e10908100c039808030160400c4c1e82c031303081c0960200703203400c840040081ca030380303c1c20381c415801035040301450352054140b100d80300145e0307202e8403400080d010a49009400c908a5101400000e000300144001c00a061511041c00380c6010505016100e8684041c0d07640400040c040c014081c04501705640800c03031400841c60701072a200c8181c2c4511051003040d480b01c0da40c201084841443c5010b0b01d41c0c2400078001c5a040c0d00b401c0300100c485099244401e80412003203500c240240894841070201c040541010b1414000c00303485d800c01400382d85500b0bc0c0c6081d628a80840d13aa590b0158a601922880d8000d024518000001400b10798014000520800300c446090121b40c2da03041c05036044550000312010982006504 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 302329523 1250 302328273 302328287
    0x5030a050c07020a08060f0a0c0c06113001050108010509040b040503090d05010e0615060a0e030708030408030c0d0305040b13060f050108010917040305071e1802030105010e03010b01021c 82
    0x4004d51000103040002080040050300500840c403003070400c0042d403501040601100e0440c440c030f50210b1308494500012403111f610200d41c8101004109281036400000b0f882103070340d03086146007030180d045215113002c1100c8042034090300081c01d2841c810350420000640e200c00c001d100500000200000a04000b814000d03640c03000f002070040160300c4c10900e07216000c0c0408000b4203c1c2d41c4035110001360800b02810081d8040d41c0003030310051074503c40300c000300d0709002c014481941600c40c200c0c0002d18000c4c1040200000c10442c0c0195888184c0807a03001d003440081c03030f1042c0070075080c5010701010a10f1280f00940103070340000700b054101c0c01ca151040c043c06084031106021031801c800040d8152064020607180c500ca60400c001c40e41050740313400100c1c012070202a2880e40304800c1400124a00078800900c0e800901594001559960000c10718030191030b44449110380100042200d941c00c98480c01c0321060803030090000790a0030000039520038240c0b150058030224041d01004803801140 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 302330773 1250 302329523 302329537
    0x417010207021804060c02010506010e1201110703030501080607051905030a0b0d05030a1106090c0d051c031e0216080d0e03070f02150307080105010e0a1e03120f05030a050c 76
    0xf2105900d44005200c0494100c800c0f02c058540340d08102d46c1004a6106100b290b100780816102d51001c503c0390000e02a520b100d240c0c608400703669500515900071214405810030301d21a07a0041000e42c10001c2c000e05000c80a0440018010309000380a13003100c0d0b011298640503450f03e8426201e0b5070702164000a05101401c0755004034041c0364440038014080014040f10500c2e80302d00380e2066640c070702c1c00d41c0c0f11400c0702d0902868010484030801071038890480300318280910100c0303c0ca50161405240d039141c4a022400120b641d5845841c03005114190340074403003000303c00850134000e07164030340c00c0800e4a50f080100880000159481c21003810b074001e444e0b10005808894846059180c0280d003038000303c0050341310b1030003407000c0c2c92020801400c0f00d02c205241c4d640c110f09a4a0300d80151400882401d20f03590040d45e408010421715108071071402c5001e5552802030300c49207113052074158540005044010045400b812403075081d0003108480d0820005400010255207006450742c090003510 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 302332023 1250 302330773 302330779
    0xe040507030b100e010905030703080d09050a12050a0305060f1e0114040b03010e060d0507090f020f16121119050a0501150e0906060d020405040302150711061b041701020702 76
    0x40d104212242d1000c120fa07000f40c0203072920200d00d1f480d40c0405a4564081c4402805120f00300540128440c01d80c114112141c03041d07040b68a0718201307545801c0006510040070300010800724103400304079418021a6000070302911115001e1f91520080380c200c108011043c104244030907101c0b206070b4880c0044500445030082c0440c0c43c2ca4403481c1d011290f901c280314108c92018108042502c82c42c040d409008140e80c4000144022032070710502030060001c4d103c0c0c41d40520782c244402800684604004c0600c4055a40082c01517039031307460101192143c15070500100b03e00e068a0703028004002410403d206004181a00c40349801e103040781c40d080b840e1b4001841542405003080d29420464203043c00ea4142c5a8403403015070f80c0c2c0c06090340c1c61030210b41c0603503c442c003c00e282025081c170b40e1000ba00306000e48103030740c1072064099000c420a1015912100040d51010040498603002d00060f5005241442080001035042e11021100d020300d01070042113403c0740c011a011540e0941c110f4211030380c0a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 302333273 1250 302332023 302332039
    0x9070603140c070c350d0507140709051602010e010c020615120a050102090109081f0911090103050f010c05090d02220e031e090306071107050a0306230103030e040507030b 75
    0xc540300724900200f004480741400c0c1d035505d40c944090408690800c80403680c0e92481d007090b919484040c103182203451180d81d540200100800c40c0d1642d400391610440d07010449200e609103800c0002d007110741851064015034034280028002c0f40e80031403544c0e0802106050482c03201120400100c0b4031b1440000e10700144603903e114400c02806401a044220098841c042d00381c0e6181a081c0d2951600c04100e60f0900c40351411050229055205161090007190481c1064446401080441d10280c2044da015405845072080c614000d000ba0b550443c0d0910f403450600c641040030490f884401c1e18001d10900004007080300301e403046e4411414920f40e154051005001a10000d134581e4004115280011041c56075101000b00c01c9080b9188100003800504c4540d072a240211656001403428081c28007490600040702d588011b20a409140204000284400003101c0c0000c0403c41d00300c802c11001c031100040001c80e401000700520128182c1d00820140d54190084004142d000d119540c042c1e21 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 302334523 1250 302333273 302333309
    0x31c0e07170d02010b03030408060c0a140a0306230f06090f0a140f0105192d090e01050a08060112030c0c060e0312090607060908090307060809070603140c070c 70
    0x40060b0b45800458550001c00200c4240c2061540b00e12071030080d14419400030011906d070b9101500180420b1003185031001c1e2880503e82505000c1e07210100c110000390310356900b44118041c0c1c1d0211002802500d041c140320001d214045407040c5403900140d441600042051100d544600e40c0351608800010080c4000d0780d103580403903014801065005004180a50140071107500035800c49802d9104d040a09180c231143d03240071103c1d5400349070300389545580c1c032440201070070030316414054815030394440b4104c490510301e5210078044142d010502c1590040c4003007000e00004128141902c1481d00c00350340541c3c0034101910070104aa01c020460013200705c2c0060b0666020344448030500c0101c003901d01024005841d11281c5c02107144683d0320201c1080720100181c82a40081070040c0301c6d008413824501d480700003a0802d14641c0c0083d02080b400001c1214441c400d0003c54040d04550a08003c1c00c004440d0580c90114000e12915000c07a00003005000e102810584038024085200c1c101100d00b1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 302335773 1250 302334523 302334569
    0x40609051602060610050d05070c05010c0e0f04060506160311120d0c0c11010f02010609140106090603090b070c082a0708062a221403031c0e07 63
    0x3400d880740d40018010803001c90100d182c18155044110002e03a03a540c18002d10b40101801048080c0500c801d0202e84149180001d5003806034819084458861290303440000007031100346003680c02c001c0e00c12403400805100b156120803d82d80300b02c40151f4810308052052a013551103400c050000400c91103003100b9885414020700040c00f1502e120307501804910607415090340e065100d00001000c0c03044c0803101c60740341c1d48075008400c007690076403001003412541c0780c86800031201c1d030380450b000c08141341d0014000c02d034001072030600502c1545001c00051a50f902d40c0584000d000d88000c041040e18803410040c0203094003965951403050326071400b0342400e0441840b490b200c1d0f18980c01c041c0036901000076100300210300b5074440d00035a190701c4807511b500d80781c444400501c1c641250b404682840b101c443c0f07002c011818102ca41240c0081610036041189150801380900000740c481c1c5d0041080c80140798400c04450034800309504c001c10641000200c1c42d09001c0d0300e800104503820310015000c0150 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 302337023 1250 302335773 302335801
    0x60b19081f1506032403050a0201080705180103090f0605161211181801030506010f091e0f0f0c0507060f05071403070c0212150f01050a050d0204060905 67
    0x4041c9406549008007500d03241d005480799450324082c042010310782000914000e03000074040140d8080020702d03442c2a1040d049038215240c00c151499400784450b0411540c110304001d8014030f05040c10f608084011408102e0b443c20300755a54101074490301040208000002ca00d241d00b903100b0701c01c0c041490460042085050000c0e14040064041d1078080034030b401d0b610030722144c04821509207280c440710000340109551780200081c1c2040d111451800d0714211115200c2c041c602c03660117410b1079498840d40c00c1048030301d070700300b00207013032504000c020944d2000411088a060351040440c082d40030344140b000802c80c0b960b85568180c1003121420007039501c41c0007810002d1003110208202900a03103000203d4104850039070116200e0b95251001030420005940c0c011058581040d4202c0c959001c52070078500e1000c4102558405a0310001503242e030508282e1081882c40e030b03840c0b298034000019552409520900c1c3c00381041c49402406d644403070b00103102904268209010307500b01082c10002c070f4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 302338129 1106 302337023 302337043
    0x2070c08010507120c021515030a150e07090917031003080403151b021c092d0e1003020402030606120a0c030b0a0f03060b1908 56
    0x100c0424041ea500c20388580e92413010400d041d059040507106015041815034105101c28aa1401e032413404035800306500d21942040300d21392004c00d0500303000a001600c0c0900b0116902c080380e200750042000d851180c022030700420758566810007112044400100010841c07851110002c044501554101d03070321100500c400c0390760fa5246011036006034000c407074803010100c4029050020744589020305200d4590240e850200c10f000079140c0315a983d07030b00c206a07102c154070001103205680e6600a0702c1800300102c00d403151a100300f05841e9541420b242c00204030400890303005001c0c0c00c0c1a00409004c08031725030803401c590030403020750070050800e50452024059180c01c007902c115150b01940040f44001406403901100805403612981510f001c2c071440541000600c0c40380525a0440c1d07004140011912041800159542c2281c80903040b540c840140c0429284404200d0002c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 302158273 302338129 := by
  have h0 := BRFrame.cov_init 302158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 302158273 ≤ n) (h2 : n < 302338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
