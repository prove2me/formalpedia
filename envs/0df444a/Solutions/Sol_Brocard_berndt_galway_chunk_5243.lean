-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5243
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:13:19.248735+00:00
-- url     : https://prove2.me/submissions/3dafb8c5-b34d-42f2-9f6e-a9a6609fc989

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 942805755 ≤ n < 942985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 942807005 1250 942805755 942805763
    0x3061d101d071b021f031b0302090f01020c01020307030503060d020901060e01020606011e1d03010c180f120b0414101a0616120e100503150405060f060f070807 70
    0x8007034101914050031942c03125800400c58020125000d000d612800ca44000d0b00450086503881100d2801c0c0440080110146030828071200d13581c0c4214175035054014001d510030484240c07905140000041e6a5580c099803440e0245e04107028900101c1e001e070300607581c032041c0a0001105460345a0004030705202c243c0100780881c0e00803100001c40c0d40d040103223980c40402802c21244260224100000071292208008100b08569502000004d592140789025060140007800300c403040a201401c0914000c0b1002844c0c40001e20000b100c10f801000c5904841410741000101c2c01540c9032034442100080042d144201c4080d034120398418200450f03100c43d0300302440041e201070302004031208052a110414411601804581d0303244180d9a0011602503020441054140c070040080d07942030301c44610300e0740c420414014440b41030340020096105941d462005c1e12020034603020401104ca05843c81500030700304140340c0072141400710060104800d585103580c14055141d480303171526800744004071 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 942808255 1250 942807005 942807059
    0x60510050a0813110d02030a0b0c030708150105040923100504150810150f060c060b03010e0a02060313020d0f060501060c031d01111509070603061d10 66
    0x10500c0d0b9031119405400c00481120b0044203041e544034400100410498207210b1480790034440210360342000361500c1140e00004207510740c58150110f4405400031a840c8011607000e40020b148843c088107500805c110507180e150400c2e00301107012000700049035a120914001c070500542944801e4805d07441201d0005070240070074280410302007651030742d016464040c00340c20700920070400302007030b440d00703005201e1400503250000c0b1807942c032407000315844140020788610b00032920640c804400110280124410b00400c40c03408241f50890300302034107900454200c604c0b40001071402500660b048030305110070b40c503020354540014420140030081101c01c1c000340610b01c020401c550203a140103040394100107140003486c0d140a411000700b0003044444520075032602e0000d80c003039039095201039502c00455130204076004c500720030000161444044c0d4410380c680026450301c20300603e0161200e030105842c42386500c4800d00c0441d5000380512000100c902e102007a542c20668618219010f608104 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 942809505 1250 942808255 942808267
    0x140a0504021513090b0d0f050604031b1e03050904180519020607110a1205011d070803040b03090a06020a02161410121401080f0c0406260106051005 65
    0x400c00d45016000010521003d10089009050b0a20800c00701c1d07a0300c0d0008101707140c1080000d01001004900103151007000c130781600a0010002d81c3e6031199101741c45080c040154240b071841d45401d040d0005008900051a280e1142500c59084010b1072003403c00b27504154038040000c007607507010820070210b08070102c3c00005000e810007e1032040c07600419100c0000e0700035004513444d48110f01c0702909482120740032440316140c809120300200061041d960342c5080b24a0801d000c3c010320003028040445500d0302c42d14405002c02d0100c02c41e03131000d004501c2c15140c089074203466040140340c65014001c0610000203c0e1a1b400105001c1041d13502900d614408079070416940401d81e08452400a0304591480294071050603034800d0b810300c0e05040c5003e184548c000c60143c00419450228211039400000740c000c00060258100d8605005841594203040b041c0000c403411407003812002a21444000700300b142c41c03200c003d00c5503004030000c00d80988070380108010700344c160241000501c0011321 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 942810755 1250 942809505 942809509
    0xd02030d0f081b042105030d02190201050903090d020d17190206130602070f0c0e090705150910090308030106090906080c13110d09050105160203270103140a050402 72
    0x60700d0b440200c883c0100c0503104401a4010b4900480c002c0002c18418040701020744900030164440c245c0c2e001040303e80c1c03070000e0060013000c5e4000002e1030380c100090344030410031540180143c51007030f41c1400041d41800c6005003040406001d8041c20b90b0404c45404030100820070100e0708a05d4241c0c03c030000c6503100031124860301480c244080702c2013103402c4001840550541d01c203905001035040180541c0340d2417182401e909400e9001c01c020034403400c141000a00c00401c89401d032280d0028410342d480345036182d06010304134036045550030034241300b00142e1941d0305e8601b80d142c1e211849480c040c0c0b18181c5075920526a40d100780c010b030000c41e05901040254070310501410014112070b07805480c818600101007030010024001d0110752585481035130144d4421103094a020380d420310313414840e00c065400d00c28002d04c0107480c070f0540c002c1650000c03070203540000216030300040380070740076030410302c442811003103200202140c2d40c10507499901450001d00c4521001d070140c0040340c4005010300701441 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 942812005 1250 942810755 942810767
    0x5120f0d0911190b04090203071b140609010b0d020d0314070f0203011d031218030f03010f06030e0607111501140f0109060221040e091e120313020d02030d0f 69
    0x44070074070051031143c00d22030316810300306540403900c1b540c0300980c980c0c9070250b085d139824000e01042d079402c3c0503002c148401d101d803810760014590500816551141c458411450a17185118031081e00000e084031484010b0403c1c01121903ca0b01926140340b005440301d02c1781e070711a80183da0990381d40d0481c800110030b41c9001c0c4981c006444080700a11526085400440d45900440c550001410100000115190070048916511281350410f0340c1d500c1040c0a20358416030020f002c1c0340b01c4006001c6002c0b0781c0c1c600900c21100e00c80034850081001d991a00000c4841c201d00e400c0c103003010700940400001c28044208114040c2021800b0300403844107aa040c07203d41e1140d40806410000d00f99810044150003103182c5a04a100490344074200c40040103018943c41154480080c43c2d24400800003410404100c0c00000d60714400000c02c1030892040881d03444148043c49021500c041022880d0f6103c290340b000c1c6224400792100c074070784d0090340000b401c201c640d903280c1340480c00203010940301d154810 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 942813255 1250 942812005 942812029
    0x1116050d0504030f03080406140109060801052d040f0615141e042705071e060e040f1805061f0f0312050403061b120905120f0d0911 58
    0x45000e9081610f55102c070100100482c0010342406111404103050000940119046410448031145156529076045009040a01c181c074402d5180c18003051101d0100300381004075071114040e907030001d14850401c600004000d0300c2155803000210200001480901448800030710a504000c034061a003540440601c4e00c50a0251094040b1078612070020001000464155416200000d81401c3e4461902c51441241d03000c1c0d9100c00804042010000c1c00507108084e2785070400200001003101507200907200180c01103201054400020390b070f1340d08003a842a104d80c03046110109010482c101d82d20b07561038400005640c550840c40400542c144061400d24680d80410202c9060301c2c0b0741381d60300d1003801d9a0f000080c90316020302c0414030341500c100180d4020f141c0003202046214151a2007461818070f180442c00481c0c0b03001e14604a002051158864154024014103981c0d503e0101042199011601c94042c10b04240080c200c00e00c0244514406d0911401c9001c0e000107158080019008030301d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 942814505 1250 942813255 942813257
    0x26010305010f0f1e0f020f2a0727020714062403070e040302030c0706030606020c0901080319033b030a09030b0402040b0d0f170c1f1116050d 62
    0x141d6044184091824049490076800100184185c07411072134002130b114266020459280c0441c0340007a80c2c840701810031260160440300403411400740b0070b1548581181c4681e000021040c66480040c505080c43c5060909100200500d00074050b035881103035841d413031501200c0e5481f5200304802c200c84a01c4d0070413030703285001c0b8040c014500240001e645e000640158948008614007090806008000760744070140d00b14292810707251a400014002d20b01072281c00014480d00d9012a50303400c01c0406c2d54160707540440a035144c40c40b090303428044c5c140030a2070201099503420750710484102910508501e094030020046001b40507600c8009072415286502c0300e0b42e0070030088440c0454101c0110012684d214200c1032255581d800001c00401221038002e8000d54a01c4c030304010070031741071100001c00388200c44038104c1900080404206000700012205a40d11815154510011030710300c42d206911300007400308444012540c102281e070803000c24400072400c4030302c0510030071030144500c101c80451 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 942815755 1250 942814505 942814511
    0xf011403071701060b03011d070c02090a090f15020409050a0c0806010804030309021509030d090f0b0d0221040c09020702010801052106160f08040b060126010305010f0f 74
    0x2080002a241c1401e0300c1240d006119854500c80c0380c031820340065004042c480d06a649940e907403139400031803210319000c0711044510007000604580c003810900c0807164005d0582240c59555580b00720051140c0d00050794401c20301103c8000040c43da0075500d1080e030000314003513160746c5817400303030400d9a8001e0000800b890034510281c41d050750295455138842c0c030900e4014010f0321242401e0f0f0081c00394803806900505c591380d566100013400c80041c12004030a80c200d80c500380417003400f2240c40300540100c807841114140308010149241d000380810350341c110340040c94240b0a060700b003500402c022281d04041c035923030200000c0c010600e848800505c000e460640c03618070b496000030301c3c103181402110307c00c600d2280c0000d040001c0005500342c4440319011038200b41480319019002e002200d0705c410010f408941c0018105228114942c0602d50107020391704103132295401914038070b0b245000079503041207090303807000b1000362024054001c5010300000a41e40d05428244c1c810784880c10030f0b24200030700b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 942817005 1250 942815755 942815789
    0x50412020111071205090613030305072a2c100503162103140a0806090c07050c06030c2107120c0e040e120424440109050f01 55
    0x5134411030441c0070000342ca004c95880c40d50301d000644a0280034225104250704100100415400c070009003900c42c064100900c84905404043c07a20383e6401c0c1c0c64801001c170082042000040710800d2484426541504034141c120f0745000d04510202183c111400ea22414407c00803030030306000c2c114480c3c0c00700c000c0e00a080d06080d02c51482c20a200240d00c00192010a000c007030503c07a40c0c1c80003592540803101d40e0341e949000e00041040d0340680700f9910034a00303080414041200d050803245402e5219015200070000c580c2003244a0b0402062501c0b0700d41c1c10002c0f240b0a1014148400900d03085510384001e5090007075009001101d80c0110102130351502c4112070300c858000705090381c2e0b60320455000c25005c12403c4902c0c1480030314080f4403212040802e0104d20070072034900240365a06601100c3e220024031401c1241c0740c040c118030075407001044040b40d403858140103c00c01c09401c45555403648445074030079101c501450907448401213503a42d5003071041c1c4048542105004221040307110013601 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 942818255 1250 942817005 942817013
    0x50718090b18150903030601030f06151d090702061f06170402030a0b07051e03040b01170111030112050d0207270e030409090b0c1201030209091005041202011107 71
    0x1040a40003948120702c2c8541c00303410036410014100030000500074900c0a06220442e90f66980040c2e03034140c0441d09003880c440d1410081d100b0001100c0b041944103103100c0034910241d90780c113243c0e8a400c517a014014000c0055032142712005004040301e40c01401107140c0301d80c9080800401e40030010041407016410450254080c00018024083c4c0c01421001d44407031002a1905070540d100078144041101008282078200e0081c2c418a03501e031101c0300704111510140304152004640041040e82203000600c5056061395041d41500ca12500005014000b54062500c07500240d0180b05001c0d2039400d03001c100541400340341c80c500c4c0305000030003655042005920401040c2e0440390700b070490310500300350311003d160000c0745003d2460081d6581c0f82d440d00c1e280c030060141808241ca00410850208003072034a2001142e11a007500b00000b8010303401c1d94200802c0c003101030b005c8a824420710506c08079026113442030038011071203009640284005680b01909642c0584041a4642000c0c85244041 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 942819505 1250 942818255 942818273
    0x181e0309232121090603070507061d070e040803070c031403090c1c0506060108090c370b0708090406030203100e0709090206160204060b0d240302061b0c04020705071809 74
    0x40601285d07425103e548444044403180030f5641d024058078249000341030b1142140074062080b0b035454060364a42521206644050002075034001e105000c10000100b02502ca4403400465501c81d18105010020410f8064840d81046e2807410b035a8021100210440c03800030300c1c880200380810410218683d40780c0b81ca40d183c150041c607890610a0315400603100c14024020320700740740c1c0020304034081c07510711558510742080724480c1140381c4103c15060f00400c3c042c060800d02115035000380759140a0b08c40d91b0306009500f01d03018640c2c00031780b9000f0100060358240001c1c0049031b40c50400140701c80e080a03465207829656445134100c14500070380302c0d0150711490111107610111b4503485502021072701c013290003030940354015440c0030000b0800c00103044603908035402122481449980408002c0641c40e1130080911000750300031003c010410560100090741d01c162121a801d6034964040200480e0603640201c42c1120680c009900900c20b00d10300c1c4620280d20380c0c0d040b20030085031050355990425 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 942820755 1250 942819505 942819517
    0x503070807031803170705030127060905161d0a0e040f06060b1b0601050f0d05010e01020a0507030212030f01030b1801181e0309232121 60
    0x10806480001a0301d80d0090b002a260250303d20f07800c9044501ca428000d04510f584e40060b20240712030404115440c0c401c0d016241070b40d80411030741038041403840d0505a41c0c2c84140d648200c103501c4400c002900d0f06240700f003921500780240c060b0320b4080750500082007415131440c85c4015980000e10841c00b600e5048500080e00c400540c640b14944803810501907088541000805c140d003001c1020400c0100710000e445d9046448455210f0340044c44d0200e602c030802401050f800c50b03500041c0e2030451401038283d58a050041000203180504a072a16003664004055900820800074022082550410481100c0c0c2c514900450030740c107180c0074070202a003062001512a419160110722806034141c1000d010300e0900000f0800800303030161a13a062101c070715007a200e061094401c640e2403011003031005207180e07040e61450800ca0400b030301c03016021070b5108200d0900f00a0f04021540e81c403244e0190080d07900a401070035082c41841e110741c0ca040282c01c59a2114152044156500d070500710075520 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 942822005 1250 942820755 942820757
    0x1060312030f060305160e15010e0d060b0a030b0610050c030f0c16230102030306180a0b0303070f2a0311010c060203042001021615020703020d050f07060f050307 71
    0x82041c4802d210002410303080c0c1024129028000c0354174042c0c0c0000644408071200418100c4407652010384400c0704c04080140c550104007280100325242c80c000324031160051144000081807100880800c00c100c40c2d542003241e1012121052101c40d1400c00400c2860307402c40c1c41e103503207080081c04069443e0300542802041c0b05401241445c0580f2041c002c10103940c407880e030102000d603960404d00c0102c900418070a00e030a1b40d08641c98009510200c100c034400c0300094042c090460840d0002203000800500301c01c0596568801d55000b03550500040c410640111002810250300d41019801b1014986401c04803500c0c820b1180035042000d04560110390304a100c00b0341103101c1000581d4040351482c0001d01082c80041000108500d601e01800b044c004a0740c50b0034007408280041e655800c0c20070440c1070614988008100321214810a40c4549005105807002c0719582d50200300070514422048400d070304900c10900d0074400400c850070041c040d600c2c1c40b10844084010262940c400545440 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 942823255 1250 942822005 942822011
    0x23100e070503120706060b191803050606120718021309200307021203090a0c0e10030b090708010c02032701090e060f1509010306050a03020307260d0807110106031203 73
    0x100910072181e011b000184503003a040b41d81e9007640000302d00c164151245420124006901601d521703030955003240c0660750703c280144555110700e0304104040e1a0501c220480c0d10480801251088084480907080d0740001005601c55a00c20320000d00c030f0740c141d0000a0307036038540248807040c3c00d6014010100c204e100c6020b682d03240c9420360300324280074805640d08244640082808112040002d0140c4818090030044803001d407545003121100d081a2801d2000d00060303c005e00215814080d0a80c103d4240411154a2940c40c00b4403402c0d140e030714207410003503000882d24030b42154490948140300310118100100c400a03038000680703a842c05000d40052405010700040c0551a46603207441500c40080060308042103145038505140d1003d05940d0010341420360001d0359003450108102921f900801502c000ca08042420440f0502495070030401403441481c0e80300a4424071041d6850f41482d80d6a42403881c0058003e0f19006240008a25a80c5400c80810219441a01242500032607143c04 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 942824505 1250 942823255 942823267
    0x50307050d0212010f08010c030e06180118030519110d1124100b090d030e0613081005011431020f0309060c160b0423100e07050312 58
    0x12100a000d5031244581410383c410000c50a6441d80401d0011901c00800034481d074a0b043c42c040b81580c8081403150200d030301a4022488284c18480000886440c003800001c011074110309078410f07039501c018280c0104900041c0c45a2080d0300340d82034013818029003002107204140bd6141036585003200030103410030811103105004280140140000c5940070101440c1801a000c15500e401c241a06c1c0d44100c40e030300e09000070781c01c150340b000c0d508003240041c00ca44016026840035140b1500c0700400603804a02003140840c0303000104041000b03840c514006000002502151108482c0180c20880094900046050307103980c92403803602d144000c0c0409288195002d00030f403100c2e820b46d0000c0500700d03400410403260300d007a032038080c0d40302d800820121032075a01c400c0c0328000d041c4910550450f084054034400e4000c070311110f504640003481502542c10781001001c40075400c10441d03205210304d42045a505417403513007038028805101c503844054400544cd010000307540308884100f03880d40c01404964 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 942825755 1250 942824505 942824527
    0x7060c1704111f021c09031a0915010303090306050121060c02030c0f060f18071a0d020a050a080c0c0a0204050402040905010903092c06041802040c0f140a05030705 72
    0xf000ca002d59000c600085120480d0f0180d101c6040481401c280380c200075151003494811881c15080b0b0350003100f4038100d00401113030101c0d2520014001c42c02c0c2c0c403414140c1074106052941c024001c2d8040da8034120a0f90071460540159481a40705a540300c3c1003491a204154040086281039640a9800035a801008100340d06500074103c21103064002d080007848891408034010f4071620f03a42181c20450755a00e84000c900c3c07115569400c250ba440440107208061907007401512999012103c507061001c1000c050041c3c2c0d008203410b0000900200d41c03011b00d03d402200e406e4003c10080001e90420b903d101c4034641e40c44912102a00c101e49400214080d07448940c066445160414000c0c0014010f070f05010340300c0c040030f1280f003d068181083c0a503290440002c020107812003511981e0b01c41d180c000800c40500031071b1418444201c0c1c0e10040d40c0041e47e07944550030800b0250344604620b40e001200280c06281203503d62003519034100a0b88580551060403240c1c131030640c3c14003546550040207 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 942827005 1250 942825755 942825769
    0x11030115020f10020d0510031205070c0f150f0c111c142a09060411130e0a0606030b0306042901080309040f02120c0c160b07060c170411 60
    0x4082c0303240d400703101d140c05030311a007640040420b14040b240038000c0b5190a0810840b51546100c06440141d00c81c42217035080d80b0400041c28106e0245401184d02600c1d950a419521150f1344030301102002d649940040507006000d015030280d03e414512030000080d04c07111011800e14498078401d0842074022007074008000303d4000610f40206a6500240312240e1850340e4411441c080c4546002a410f880300c40e000d0f01824404400e0042c1a4030804e886400c00d01026290074840c07007000900521551029038040b07480d1600504055200e000c00f801c1c44842d400894006410200416090500030350031900e0024605400690200038a003030012400b40101c2094110a03e20250b041a07100004042c9000001361805110840d010000b80b02c001450740120321640840c6440d0382011800201004100000f4110783c4203000c003034426564114001c1c061a503040c0c2c001130008000841c450b0144041c51003004000581818145251000d82014001031000100002e01901c544105041c0ca81c81e100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 942828255 1250 942827005 942827023
    0x5010e1b03011401030b070216080309010801080304060909020d0b1305060103201209030906070f110603090c0d020f0a0816410405090a0201080f19090f140d020d02011103011502 78
    0x508a0120f584ae1506141c4a501c0940d400e4000baa00c100003150b00c180200c04c071421a18641c4802008918021164000c0e40100c1700340b82c007580d60780000d0a00c40d20f82851201a01030040c0000030b4901d01840098116510501001e0340d54250180c104450241c1e21b045920040304d0a054906030f641e000320507441c40c0700390300304141c00080108140d01040703418041c42110a00c03e10820301a12080800d00070680421101c81c01caa900501d40c0c03803594240464a0201140050602034070543d10001040070304041c2d9009480d25845030600c001a00f0481103030401030188075402c04d132140350002071190110030f4000a48855001d20110f60340c200400f0514004800000d00103004900d00240c1440d1507640b26402070b8007090901001031200200d17481c1c80c500c211480301c000702c0b48000001b00768004202c0c2c000c3c02c4500050030140034000ca42c119000b5442d031005000103160994035810020b00300131440036040d055a06014407450000305600a0341d05440300071141c004901c420b4002245819506 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 942829505 1250 942828255 942828283
    0x80609070525022407140307080409051b161e03021c170c0a02061806130c090f020702010f05040510110a060c02070603140402061602030a05010e1b03011401030b0702 73
    0x36009400041900d58040d045081c000c5241d650b200410142e01c60301c034424050014200227041005100410a950102d40c1103641d02846156141300c2066107107003940050803810444180c1c5030f008041109494008040540c2d00c160200303218001d80d400395945119080e01c40c0d0001d4580901d00105128050b00228055103418010040c00c011492a030581d20030101a0018003442001900381701c0110884a10040f00c2c3d00100815590420040750360707000340e0000c4035407041040d03000800b24600c0c0030381280c4c1c0c0303030b20800180d480c3c4062001410048142070040c0500c24140000c01241da00c0804141c13a000090526110794643d603940541040c40610008180702e2615a41c229029400035264041d507007291410822020340059880d076040d41258000d51140e001c124141080001c180c03003981461000c2d00301d4091103201c0c0d0b0340301d0a54182160b0440e940c0e220850403001100c10481c460a0480b00350020030011a940c1800500381c3e00500025201c0c040342da006c034400307910800a0100700214 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 942830755 1250 942829505 942829549
    0x2070f0f060207021503100b1602030a0606050117040803150409060f060612090503250c09050f10031a100915080105010e09030a0309080f040608060907052502 70
    0x80d910349030000707420070f800c00d0f4003030101da041c0629000c9800c3c040300c0c003500440803002592850001040d449512803410754441c004646019001601d0420078405100e219900c04a502800d000004260081d00207441c00300403080b10a100100309041e040740d81218690746903610212076403010070094040601e009020034600303d428103441c207842d88000144d44003955880400c40b44a04040d050310701402000d04240c0080008080d0a03d40100d10764003080b001201d00903000d402e4403180c042e5115507006c844e44075107c0c0d04002c7d0101c821510309e5408030b0400d1800d00a9403d41d06c0b418041d0b2018004203c0c20441980858070241d5419034880060415240030720061030303120b002d480710042505ca401078540c280000800d40c1c1d0040e10900d8401c03900f1500850500c0b0040710308501a01a166056402e100708104d08c03000340500b1130040c8003030002d41d1a843c3c01c508043e010300826001c000c001c0c0081106c1482001c078450450300d194542500461701401b0b00340d61500024158095240490100e004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 942832005 1250 942830755 942830783
    0x30f0308040c2106050f160c0f05060907090b150712270e060306040b1314010c0e010f140f09040e01050a0e0f07080d030509030c1f0e01090b060402070f 67
    0x6202c80d4801913880381c002801079486030001d140d0b030100e05981403082046803045000c80a44101003c061175401003500c1040e070318140c2c4609081c58416101c050f901c0d0000541032058000602500c80c0155003580d03003924981850040d25517a00030568014184030000240c40d0403188101036024070b044440c0750417049031224035961510014548204007000c83e1582c0080e00514010404511403900f03c100103599a41d29131921013295440c10303044881ca88402406601d0035001d20851804650307540720345e9200102d042c0050002035951204404201507100d03902c2e052000101952800c510460703080392103401c9240040d000c1d1a01d40f8005940d503203004208001c03618140c000340e0810100a09441d104840c0088880d00d80c140b038080c148959118109441c9028400d80c045070384024104203403418a0b00010025050040425030081081d094660817420521180304642c1008040402040305480c1c903652806401401031000c2d128a50116034002030180d40380b100181c1607840510020080 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 942833255 1250 942832005 942832049
    0x503060609190801200a050307140c1506030307150c0306030632091504030c0614091c0c0602161a0a0c140315040608030f04080f010501030f0308040c 66
    0x82c0a84641519503081800703005e003108102007240d05840c42045510f06c0e04024070803d441c02d52002c2c00705410800000a90f022001841014020104d03c91014045800caa060f600081000203030500e0b2080e00208403079800101d00a40401680703109070000700d01080200d80960041034903910241c46507060500204214480c582c0c00380810300b60340118000b00c051040b24a85012044405451a50046400c1e18045031411103407a4414400d10340310b4028955030b61500b05603052400003400844500e02448401203082c0030403580842401c0b006807540f041014000c00c2c09880c407202500c515800642e00550400c4940403140843e08072040d07201080d05401c1e5201e40c00d00032240d01e00610300d01781c9445000761054004200504000789668103584460015841c01e40300c0c4c0070b5441d8090380e611800901004207001910b050441014150b858910700201c1c2410703c1d094170810880d6074500401400001d014020540910340c052500002665803860035100c00040398000807134248031800400840 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 942834505 1250 942833255 942833299
    0x3132003121b15010e0c1308030901080c190503041a07050406110705090a0f1d0c09090a080a1116090c020d02210a0302190903020a15020d0503060609 66
    0x10b002045401d001c80c0c031054680c503031a090015a0354043c145888010001c145c80c161010740c00c0000940f4051138107c1124403112081019800040a600b000c51160641d603040340040360b0020110081c9072030320300541c0002240c2c0c1e07244400304042c0007000c030109050202000c90201074102c05009030000d0b00b403016000c3e0842e0040d101c0d942c0026500b0400e142013a601003031910440300e0291070100f040d140c10108a001d4921040100000c5071382c0c0c0200c820f8500c0501d040a6844102d80c042c080044a8009210295000521f50300300d681c07200c800700001800c603100700e0f00200c03c0385c03034440d99504035008490b0030302c2e5217480101000d004c00d1341c2c00b203841c00ea036501038003c54840b034003214603062074410306913144e0741b140c40201d600800c0c1241184048107d64014000401a840c005140910561072550551505030350300c0002101d066040c07045080c544880c03c003802e03042d02e000c00000030000c2e0003940c0b180d000308000b08000c00400464201d80f9014247c8402c0b02006180b0384070034450f950300c0955 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 942835755 1250 942834505 942834517
    0x90f0b0f0d06062f070501141603080a0f09080409180b010303020312011d010317130e06030705120c0f010306030f030c05100213120302070e0a060510050313200312 72
    0x40310700c0307a10000840300c0111301d04d8450294a02405a041c94980150f0300800d000381d4591002000700512521240d440c4c001c00c8240e0300c0383c3c952202c9030802c0c640075003c54054181e010b012500d0030710100b01081d0b0358010baa044900304c0c0c1c0c0c0806c014103d02c1840e0705410026000514400c00d0311f001004250700170001c1d120058220b040000a41c0c1e03a119904c01810320821390200f50802c020052022a07154402d19002c5580817840d5882c1c800c0c2124042e0050185500c1091040f00b04400c1c4002c500c0c0c1409140000c0c0011141140c64440c0c5101ca191190b5220080c41c0c410f00440b00e00b800d03942d0180d0000001150802c40c0c4540701074560401510810b4134000c1200c0c14028034440310034031030300c5109858441108042c0c0c0d803055824034080203840c403080d1b40c055055108014000941c08d801d4a4101c4c85202c10301400310f003e0385001c040c401010818800401400720900c1009201f000e6071041d1014240c100140345040644002d44c00040d03c040d821854040c01034031401e4064000304070040c10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 942837005 1250 942835755 942835787
    0x80f010b01090501081504020415110f0c01090b07020a090207051c0305010b070f1a070507060f02030c160c0824010b0a020d0f0203091c02010f090f0b0f0d0606 70
    0x100d21081000116515a80b500655011611190103e000441241502004010b01500062400362121000420301c914492203c0c00119551740100301e41d20103006200440b00041c000780000c0c1c26a0001901c0e10503140682004070001040510a5544085680005119100045503a41c481c0d042c5941c46007107030801801e0f02600c01c104104860f110303108280c121600300303c5c028103000c401e980b1000240c91041095400d100f2400c068184140c008040d64001e00c42034a40580e43d03842444c00c98180d400031030841301c04510500410070309103402000c80300f01d100c200f030b050120303140149829000c0340041d0b04180004d104910b50f140b004245400c03da55000715400100c640d580e030754071064002d44295031302100181c00c4034060524150013421045c005881500550703051000600c08101c80855031066030403842010040c401c01d55801c007008900600840ca0844942c50400e01802c130081003e105181104000185c42101e0303d06100c103642d003182403002c05001c1d0360f41d5042c2c024429900700312102 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 942838255 1250 942837005 942837011
    0xd0209010e031612050a14160b04120f0201110d030b210d050702180c041a1603051e13050a060f0207060e1f03060e0a061a090f0a080f01 60
    0x1a005103000100c400c1d200c1d1000f000103e11034107000c48088002e118500441e400d12480c44800300043c00c04807218030a4012030000c004140414504c030700881065030018800c4681000103014000385880d42000c17035900608405604001362004035502c5292003160740260258054100800743d141d0094500410100c602c60002c04c0590000d40c2d4041c0c1003c94100ca580c02500c4078084140640c0c06464080d00003400c0303044102d1000c120790140d82c000c8520b8141514000f40510682010051006240000f0440b49007081d65076805103000c0c072104040541402008903a608408400c44103060414500c1154541c840c1c00725001400026281e0281e148a000c4031b01001c02c20900c80c81c00011042070303990040102e03030b181c6401514007843c1814040d402c455242482480c00074000d1a00c1c10210040c4d4001405c1468005010768040010306480b02039400e0130004c02800a0600c10000f114455030151a620140b01c2c5c0082c184050241c075042c0c0012559400145962022805004074100c1074024 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 942839505 1250 942838255 942838277
    0xf09090e0c040c030e03030a09080c0316030f080402031e07050d1b08030708180a03020904030f030b010e060a030b06090d121409060d0e100515030f010e150403050f0d020901 76
    0x1135054402e5031801050b2a4402c1c00000d041d04071a400c8201945d024180d91442c06240c1ca141a0441c0e2005001a03142c803102e00e403000405078009503000ea02c00e060b281072800c0303003025030005e83c0364890417010503240820100c00480d595024080e10004203401800303100601e2007442e01e040d05e6a6100d0041400d079200010004d49101c0200c00c07601e54580c4280b00f98075040220040c040014110340441e90407501c611408001a11450b502038011402611010203555441c0c9009041c1d885845d0b5481c10801060b120b42c0d0386491703c0c3c3c05d550854181d8280818500d201c0703008510a802140c65480c0d2000c0101e0380c20050001c00c540e081d0065481b07035100b044200c4136121000d800d206040800d50800c1040094a05002d183d5108040301e00751107080d40d0400c7c5a649450041d0b034010b50ba000300122001d41004000d241c100301e000e4a0070550380080c0110100d03c40011380740c460031262110082a05400901018456030894840c58041700613640c03903e1503602e000c0003d41080e62810301180c0d0704494 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 942840755 1250 942839505 942839507
    0x120b030124052107150c02060a0507060506010c05060a020a0c0507030b1006020102040803180409150c09080115140114070b10291b06010308070611030112030f09090e0c040c 76
    0x122030000f00f068005002075498004000314200f80c1d421040104801d868490b401691204010b10154405559007030700c43c0c806040000451303101509550601503804402000144040703003541e44240780c0e81703006803200610181950300300020710004000f03000f01c01c8040104684692150b0007903421268140e0b440f5200c0354140c1c01c034841d5008015155009022001e2290b0022420303526000000e07101080040c01c036a11186100950b00601c1c1c503807500c91040001e10f41e07011100000510744035009000400c1c03980350700d10001529000e07851023101c9041c1c103003125074042c01020081d4000b911310141da600c21824040c07400780060f51214440c4103208000142400b883c201c0e80e600080703850112122503814003900020f60b00a00d19221301c4036118032000035010003440740600840c003c2c10b9456459a141c60030404441c1d9440c4c010581103001d05c0144144100300d004101d1450749802c003400c0001d00c0e60ba09a030300f280203520040065040c028804646540411031250510b0142d605000754020150 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 942842005 1250 942840755 942840799
    0x90f070221040902070303020906030703060501030b0f010e06030a1d010902010212070b0f06011107090e0105060411070618060606200f10200f0403030905060a120b03012405 76
    0x80303190040030148420f00c006402c0c0c0d401044030600c01e0400602d080d001c1c80215585420881d105404240d441008020550300342c05040801d00045415614540403074001070010b079900b400c81801082c000c0000b03011002180d01c592031210b5a0041040841450700307619018002402040f070050160b802040501e00e120000c0d20401e50b030142580705903907903c0310720342580e00e0010516410007c00008500d119a002d022400151000400104020b410f580c09036083d10809000d1500070341c50702102d1980c034012682a2466158040c0000c9071140030f4860601c04e02c0c1c25894050840c81c5819000a10180c103c00740401491003003002210b1003a6174008162141725960400c0141c0c0c04c00c00b48211303d4191a4010a0003000e00400504148400c0d8498a5690400c04081c1e8910a000409001303140e04a01c03d030004083c00c407a07030b91405904440003001340e42c04801043c61243c80d6400040c569400790407201804190302a030002c083c051a940b82c1e115041e510402d0300445a07d803c0b1400080120 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 942843255 1250 942842005 942842053
    0xc0810050402130207020103090c120b06030703020303190306031509060b040c08220b09150a0b0604030b040f06050c04090b09011d060613080d1715060315090f0702 72
    0x24080d5403c3c000040020002e0b502c6582e040f4101651340144000007140000310202030404410005400040b6143c010103000c0c010700b410f4480c1c2c1c423a96040005aa000044400c0340c41412407082080b80b0080003a4082c1009070401400c00d034800007524250303800c1c2c0d0f02a0004030300800d405e00458050303e0a00086903035410003840011031388000140c1822440036044520100041c902c060012140c4425183c1d2100703880c1c0035400e0708a50701c914036040350395a040d50410300c0080100310404100300007a00c140f240c0c2c440109000c0d0315000107814080071080000505420080600c114548040800d810368018000e0100180c508a05280a030410411480c181d4000041000510001c583c040c1209200108803550015003044642003144000400304001c0000000619002c00ca074203010b40540031500c1c4409194100104000c50142c0d4160f0420800380281c0e00c0390303a1ba4491501001a424600500c1d5030006a8442031100b1440003000d82c5114052990903580382e81090020004014125 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 942844505 1250 942843255 942843259
    0x91e0c030602090a0b130806010509010612110904021b0601060e03070b03040629011b1a041104060e04111021022b0f02030c0d020d11070c0810050402 66
    0x40205200184440e0300825142c0e00091041c40083e07514010240340b036220300c0003428601c140702010800d5080401c40907000d800101c0380b0284139810014010080400d41591400c000e4035990700110524440b801c8031043c0b1000350095548120003140c000c0703001000040c1e5109842440f0000809a101d02c8010114850041c0980b5145240954548443e0405801522010f5844070350009400142c1c030b10307410001121400c2a4941c0da000d0024000c000120341150111a00d00c1c455170008000008481c00e804a2410760109a1540c0c103201c0c01c02e800c20813255800501d00b40012078403c0d00004924460b0740309201e4004501e51600a21918000c90040c00c000304000c00e4100c03c0c02c0c1e40000701d1444c0410311507070050401403602129068041014100d401c0040041e15050b0521254001e20442c0c1c404007005620303600b031406880140d4802c43d41300b0565286d020a82d024284a80d404c640ca40c02080d071115901c1740c11504280360400f040c2c0c41002080d125941d0700180b20300290007824400c80d00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 942845755 1250 942844505 942844523
    0x607092108030604060902070c030605010515041e0b0417061602071802070807060504031b031e02070f0807170f030d230a020319060e0604230a091e 65
    0x3141e03514051900050141c960107a02c5460200b0a1503061001e000300134003802001a0342c915505200c4110385040c0c109900511940c14030383d0703000441c10112421184007d182044482804060528002c82c54002c44095640005e000410300704c2d000180c120f40340c1e075409841031611111002102101100c0c0b2200158002d40d00c10011150145402c0340801c0e0120f5000d860b00080356115802644410011230301113507540188400d143c0d20280b01e4080d20861022554964400c0d200036080d06070b941f4140d040c410f0010000e0414602c00e0003210000c09400e400c00c58015190006c0c0c54a42c40c040c050a00b100440a58445201c800001c4034585050140007640c6088029244940504405600312030740f000c42c038000540640c401241144079030a601070042e00c80c01c040e1141340c10008126015a10309045c0344040c4941c0307850a1106400c65001c803400100a101c5c8841460002c00035100315400b40c10300800c01441004035003087c1c00c0740e40308010f56078584000003c5a61001343c80f00d000303010000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 942847005 1250 942845755 942845819
    0x6050a05121c0507060603030507150b0f040203150a0f0e09070b0301260321240409050a0b0906040c06170a1d10140703050c03070509010c1202060709 66
    0x620100140b5050b640760441c98582281c517000e0170349215a00860001e5030001c0c410040c455019882681c00d01c840300103010550b900c00004095010000855109660000c042081c2c610348407201000000040d0a45503450341d0750901006c61071992090190f507401882c0050750840000c610601602d80e02d040880c11642842d40348010b1009103101442c002c4e11405400340200780405c080d094500800c0c207908800034140e985582000c01c050002550300c1c03016018500450b07410383d0300c0e90710000c060782c001a4070b1129041103450220040005084c01920b641071190800c4003140162007580141403860410395621012502800d901002c0710860b44140045032011003140c02c00d07006101240d0340340c100c020011082c1800c142d107480094103200ea45090280003001000d841c25400451814104110300e40071107410740c00d1100400e2041000000201d8541c90ba00800c6a140403c2d00004020445060404080d59402c000d8030302c640860320306440065005260b030549200c0203040c03085501010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 942848255 1250 942847005 942847033
    0x203030f0603030906070b06040b1c170409020a0807081e01030b060316171603020105090d060e150f0a090305161406131208010e010e070507050a050106050a0512 71
    0x4805020503a043c0010041850a82c1d43d1901070000103004010400721418950208001c5500b00d0000c2c4d401107170a00003900c0501c60780400d6008280d000b1520040100b445018204280304a400000d801c40c0f011460180365170384029940d10030701d09070700c0d1100d0350b84a030f500500350710b415614003d841c0030801005000064000c9061504810702404841d2140c0c000040c010034507885400c10903400c0d250758030510300920200b040448000729034000710003041c1944c000902c20310458814030b004102d1070b018030b004c0220311f6000e080201e00385002c0e45d0142880d200b0030b200f50b071420f0b943d440202c3d0035440480c0300c01b00705106001160741d050312424602816103c3c80e500017603621070b0035251a2241410b81c6203035581841914400c6034011041c0050001518041410701421a0714500700581e5074014040420000300890542e094106039548542e01c44008881c240301c0c02c240107007280581303054501000015001501a940e08070366101c40340c0c0e11003040c030003001124004003903150302c4603810059031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 942849505 1250 942848255 942848281
    0x209191a09030a0b01092c030406050310090c0905040b09070c030f050c0601080a0317070f0e1f0e0310140c030703061e06020709061805061306180b010c03020303 71
    0x2603200036043c0e80c961440b80c3c40e40c0d644028264060703144c0d80d80740c0d051050619030704001c1d00044501840400c01c07800c400544c042c0c0d01e0056015600034420000007103034480c00010224002082c0380c00c400d01a80d05a64401840071000348919806076041007051051450212070091046290360b542c60511500364808852021403c5062400e000041006041084003801054060101c000017086800d2191030024901c500342d100c4241c045890034140f00c0d40c60741c4004402a081c28602c2d11004034900c3c240002c441d900013421403102e00c89c0c0c2c4011404115000403440c0c2c6005c07011401e5851131141460310109482c4480160f400b00407100001804040758280915004200c0d07250000f00c1903142c0c010410440d607200780e86145007212000400c6526410040c1c500603142600c0140030841c949036030111652050a83d58800d0394a4200003295500c840284040d140ca0300c0800388006582c1d02b0021802032a001e08040b1882d08081010311a540100309100c40154103034001c5145940e04a250900 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 942850755 1250 942849505 942849517
    0xc0610030f11060f1305031c090e0a020f04060f0306050102011b0809120412060606030c0c140f03040b30220501020a030605181603020c1006090209191a 67
    0x4001e40c2448280c0d16500d0303201c091710b0345d04500400c5c0c0d40c9641c103060405107011b0031820010504144d1400e900c05079680014802c007242d483c50110092034540c59640c074060300400c5c18407001d19002180c001119a8402815465000107880402499480d94012030a032560b1648180505010102d0301294501c00c00d00c041d8009101c0050b2804040701524034106540554000071403004694094030602c407061003a2001440c881c141044007920918014051404188010744840700181ca80903014106011603021038450724140da0f43d440d00c507050f640a40e000660f600e042d00401c3c0240e1560700c401980348208100c3c100e200c10056039594903103007040303414904002c11540b0080e400e5600042d400d0024100d54a00703a00c1c04540d1a00703050901600418846500041003010b400b4000003980b0b070800350210b22041d141c09680d404400c0c11080c0b404a48c4071041545601c0c0020010780002c103503010b085074107c112076a159101c17043c54400d00c0c0241a0064000c284044070005200044840040c24 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 942852005 1250 942850755 942850759
    0x1a100801051e0406032a152105040308090106140607020f0310060e1e1506031003080c150c040311010807031d060105211c020c10050c0610030f11 64
    0x71012080c41e003c42c05075184d03075108403000442400521110502c2031403404410407000003085a80d845c2180340c040764010a40864203210105007100d030b42d00e11021802441200034003003400383d0301b01480c000385000821102001079501e800004078a060880140e46041e450052509080407056001c110070a016449403a6042c8200301ea03c0701100e409000714401005000008802840c00c0c00700b000c403206200d404500c1c2860f40c00304001c9407541c141c000325051041510155145d039510751901c944490160005482d13a078020403180384ca030740006a640b460009401400c0066155155090018004d9000007058500440c2000f001940304505541d413180c02c0b881c0c0400d885142d000c9000c04900068003664281e000100180164100042c1111305001640425100c9070510300304207440b4541506c520b03107010b51010321141c0c1d6074820810139a098034000c0c40720140b0740900d000a45560700c0021031403030310b009000025043c43e60a000319401c5940001c403980e54060aa510000030702c003085c403401c1e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 942853255 1250 942852005 942852049
    0x30708071e0e13050d08090307140f07090f1821050d1e060e060d02120106050907050a080f060a180f0c11060f040c0b0c030f0d1a10080105 61
    0x101041c040901c0750003030f5100c0d0180042d4000e07504025007095006011141400584024411200c2001040b5034030603030842400010210403088941c10002d40300f80600345d9100c0d02c180440e10348103aa101d0820300c50322140c1080038120034510725104031032407000544010402000c10641201c140b050b034001001514100f4070306010801d9142c102da2030440c9110300d90300700d03a4150100d04158880e0704054803070903400300124030300000010905a17900600034041c0b07079100c01311140d5030f209400140c00303080f0040c03403001c0c580340481c1e0051070307030b00045801700005240102048040251110700c03401448094400e4180d00d0420701c208024948010082d10102c2e40d483d1072004d405121f1182c1c0c40c0140160b035450183d9040a68500c0c988107004c0c0800044d01c3c0c50320103200c009002d80c6030b0a070807102c5606d6129143c4281c454802d0840c02442a82c3c001c44000045015000e032403980840c14051030010070131449070f403400c280710341c811800e04074030085206240107004c20300d458203200c0004043d681500d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 942854505 1250 942853255 942853259
    0x1305120c06040513090c15020607090803031302040207300503150d0f0b040b0702070602120904090318080d0306150807110c04060b030a0c0c05070e0618070e0f030708071e 75
    0x1c0c1d88219000d0b4800c2e41546030887c0c0101d041541400030940128061030b0100005090031901740c0c8a12000d0503d01c00811030b4225541192981c0c0c0613640380030b410120708a040b10450440c60f83c2030280c0e00c140000902d10f6410109040c0c0a038090b2801209034a02c103110420319002404690503207144107440028400c070203440010b4174000801d01c41c6200f42109952418062006071030003085411260641d0480c0c10001002c00301042696a84c8208a9012510750180e08040d030700d44101d00f4003880481d9a4001c0843d4075940029090000f0070695801c0016917525580006000c2c5048800340c0080d49032008a8440c51041500840c0d00410328255440c50402d030300081c1c1205c049500c503105a150120030000e522107540300341114001c160802d00c40c1c900c4541d442e5626640d160080c20f140400300b0001c00c10a0700d07038400000340e03001c40c0028001d02d8103204c4800392070f0110310f6102c0340c443c40b405507040381c40d81008615641120340c0040100101c504001c0590802e034244149404240407030500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 942855755 1250 942854505 942854513
    0xe0d02040c0f0e04060311210f010b090609040213270f0b0115081603020706110c16050a1a121f05090c0307050903010605061305120c0604051309 64
    0x508150548507840300000b1410400000e8250394010510510843c60104100042011011003c22044044038244420010b00d2804802100c417018000310030300c9102c141c3c000c0442c0541c01100000400c03522007001d640c1d024100501c0420481d0025008485054008505140c0d0780240d41c00e002807403600c250500c07920f9443e1a88a040c5c05060b103142e402c1d8220b24061080c0035040c80e01422140b031520740c101c555500084c04240000d403103415541c41d445140f007007041c0300f603058038613540e4070200c24403852034004010040fc0e0449001c0100034000c1030500a0000f0180203d8001c0702c2018100031561850301040e501210f0b0082055607481904100d40000c08030307508111842542080760038119540780c07502a41c0708081c0c03500803c0c052040341c03092108201c0c0c404180c0354030024034a4010f642d2440203003c280540b81c1c0b6805079401080c00306901c842440183e451106a0344280c4406c04621300320421035640d40d08a0a07085d0700804200800c0c00b02c0e05003441d002d404464a0036000c50f288546680b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 942857005 1250 942855755 942855761
    0xd0b0a1a04031103030301030f0f0f0206040b0c0136030201060b070c0f12150b0105190e011407020a050f0111030c03041d060906012006150406050603070f0e0d0204 72
    0x8102100c1400080c06004001010b18911800c0c407065005504540c115919402c0030342a011015180701d0001c036100d41002024015480e5060780581a02d449550341c0352000740c0f940000e500c0501c2942000e414214041c84c03000407050546604121a07110006015403c40c1020b40c2030b020b4003123540710035002c10700f80c2c0100300070828144152035269403d8a40b001104c44e42009402010726072584807807040100d5185990801c455035450300014418120741e0060f07415206000c070404800c0d480403541d401d03c90700700d01101d0030780c1401c0e220003600400b40458020140b01e596402940009a1a014006410007050f002040e50040c10036005a59440029071f180d5009080c59030895480000d00b4090100000800848101904010042814440c0010b6000c96008103154100000041c110030103d030140d220031526580602951201c0c00c00c02c41004180c1c10043c80c0c2c0c1c0c01542003920006d0b031030800c0002c80344030315855074134001035020b0b02104952840076043d10710b500044020540d005680c440c8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 942858255 1250 942857005 942857039
    0x301021305010906050a27030f030e040c11060a05070302040f081014010506031308090a03050708150103051216080c03030a0b0a0501021216060c0215100b0d0b0a 71
    0x540382520440c6040001400600603810480800ca0203100320b4031040d8000d40e00c00030003140c14a021100c030090710022041e1b401c0075403000c0e1240740810310b52000e068200541d4a40508181c50138400001035240940b4903451189254126920207000600c007504a0751159401580174070307000d481d0035601c0c0c0c2c1000440507203401c00d240c641c0060074000c90790b450350702c87c500707002e000440c4518266150200060791800300030500c1d4901d041c498130401c00c01c1842e400b202c07a140c2008040301f542d1510313400c01d01e90721078503806050498494403070030240c4031204101450403280d1000041c03031090000c4500032555088418410361603051980443c3c0041c0340e007405010010300f5003005580300c1c030f00484503d040d5840c000c0300304d01480c440d942c207100d0359a0208502c11180c0d40610340b940d035a0b2404ca107410460a82080140410303150000c0c00c200300350b0214001a0381e200c020241c0c103203030b2110120b080071202c0e5840317905035003070703081100c811008415041161102030003081014055503415062101300109 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 942859505 1250 942858255 942858277
    0x12070803071706060909040f06110a02071d07110a021503070e0a0b220906060503040b0a0624170a052d0703240612050f06030601180209030102 63
    0x481041880d5030b0002240049180c0705080d0040c0d41080c0000c42d090780b19a01e0782a00440003440050144054940e2a40c01c9940c0031604100e50b030101e559504058111402d00001402a884000351b4298000781a010324058407032000c1d03207619609016100746507084114a00c0d0701136200e0440c096900c403940d10f042c80903100b00559032403512a1008100c42c0c3c0701107045200758000c0000b8010180000c0a0700c14a0f203043c100c122a0f90b054400300740e0f0540701c030340c00b180d096810010082001640040a14004c51188010000e2600d4100c20f00e8103441e280e0050803400030382c01c69106070b48001200611915111800c0641c80c900462001000071002180ca40a94513290390600c1103148e10103410303d4035684170340f0010280483d800d101c2150f001c07002d00103008041e200c0c004421004400c2d2688240040d07550003040895580d180c0142400c004401c142e0400d6180c0800102301e4841c1c410300d2032080c0c0000700a40b501d81c2c2050380ca0404c3c0000d00024262403179081c02083e043d034509100615184001c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 942860755 1250 942859505 942859507
    0xa1410140d020d0606080702061f08241e070507320c0303122715010501080a0e0a020112020c010612060e01020a02072903040305071a1302010c0203120708 68
    0xa1a0258400e43c4c400360302480410036514100a00c66501003103980c2c0055140d201c14010044d040322040d0a9040b9411141660050b00d1040351002c850b049070f80003e40d842300c0c850b0910303a51902c00c1202c4030502081d04140a94100000300b045200300002c004084c4151035140510401e11401130007400094201c00d866680701003180c00f009030401c40034000c0c400c12801189000940540c01c05111b07405083c0d054000003410a489818101c4c001c1c124807115410121194a8407014504418940170b1043d82e000c00d010001040351070b4928041c54610190000080400c0c003801d0b401143c82c0f09403402c24904d0355500788018564500280680e200503c1084050540043c05040c20b208840001000841c03981c8100483e00f081a000b04e130a070210340b0b402c6980c2146c0c2c100704010100e220780c0b0324200400b543c0004104001c05421038040e0031058040c0e012400c50030125250018500819038004d01003500541000c1300540c03041940510880c07000d02502e42e5443c0b600c5280880c5c1e00040740c12034980c40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 942862005 1250 942860755 942860767
    0xc01020c010522061a03030a090603180201050f0a1808150903040303080c13081603060b010f090504020f0405040c0c0b160503040807060b121b0a1410140d02 69
    0x5800d00400e43c00040242c40460102880b071000c0c964030010031030090074191588214040c02c4114190702c8213241c000307001c0d2652640d2442c40100301803070710f00495003c00c0c5042820b051503540740f03001441c150341c1071b10781c20302d094081d03400b1000781d0308101344200420070840844440116009801c1c1c00a00304500100900e001441094400c04002410005254070900041002ca640000c0203500700880c0100c85558144803042c1c00c81144d02e0381c1207503403280f04500141d164840c002405004070b80c007440080080318009001196a04c0740c40f100c040014404d01e1041c03220389080e60040001581c0c48080920300723940d4002080035154100c40c940042600c604844080c4900714005950041104611111a107008540542540005040540000c1000c161013080200303036031055861001c0141840084031000710066030391181803081041c110115030f495102401c3c0b00c0101720540e0b018180c100401d1038107500b4040c9040112003e0000c020a08810304100c1407150020030141010762009680c3d88 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 942863255 1250 942862005 942862027
    0xd1215060210060e0405060f090a060e06010e010b13051309060e0109060608120301090c05090d05250b07060b0301020f040906080c011d01032c070e0601020f03070b1003080c0102 78
    0x289807030303004d90700c5034928100300800240c0200703407998051480c0d0345580d46c86d190f01071118940030708241e00400c42890305000361001e11000031501d04803111119540a03683e21248083d0150041f580d119442c2c269136141442249802c10f01c4c035014402e44080010080c0b0140c42d1f0000b51280841c0b40c0646941d1a16000c080c4121402000302421043c0300405030000301c1d05000031184070500c5070741d003842d581d00110115036200303804585c00d4204c000d112611316205400c0440d1220f02940d0920103c0c1d5042007080022103d03c0c40c0c440171542d40c01116401c1441503202e05d800340c8000311100d585951700b0050303841c0c0d100048000d0000b41515150000b8241d00300b01c045841c08030a01c0e207103814010541c010a034104283c41d1328801100e420300e00401c040c4924914622951119695560694100d0f030940580351400a5024100c5001c1c0d41d120001d81c40d14001640c4840c208034003807040fa0000c20200c40800c04880c2e60581148611400214280d565180c1040c1c035040500c10fa10165000241d04c4104 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 942864505 1250 942863255 942863261
    0xc052d032104090f0b3102031e0f060109171c0f0f030b0901060e0a0306020f090a1e170304080d1706040b01050427090819020303090d1215060210 64
    0x80c01c0b4213500304071802c50000040e0400084100c2c00004040b040c010b0103a070201d12103241c0e0710110298095499041c410f1181d8070984810011940d11071041e0005900041294101402800180c44092403135062120941c0240f1010f03061481600c640c6030380030746205050000c0004000e0390303a50024800615800203018011243c01c030070426003800e94001643d5240c3d10442d044401a080403403240d00c05201007043c0380c510382d102070f003c6440402c1c001600d009178401050242d808442c680085030300d03a902c44858011600f004481409172290500480c1c0f102d113802c540658440c07085078286a0340d0b102c0d90f440d00e6400c4242c40c0000368002030b902c900c200036900458010100f03d0381408880360840000b09940160b200e08604a1044480d00c0c01c6070220285403007e0280350300040c0201c180c0c5040c114603580c8001085544058a00300282d22644040280ca0085882001510442c241c03000e04940402503403110300280c83e0350304003104040001c2c2180d200200681d402418465440880e0a070407 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 942865755 1250 942864505 942864521
    0x313060e01080a0614090717191401030807082d04150f1d0103090204052e03080f090f13050106030b0d0213050417160c052d03210409 59
    0x1a060840034001078158a61741d00e8004426103c0c03500d90340d149902124200244984001c0070740c40441400310550720403110902d00c0002c00702c280701d01d0240d841d02d62821710003441301400c2000d0900c1000c000031140d500510794a11010000030012400c02c08030703841400301a03018030b0303003035400201000283d410320651030907201241094184000c4d01c02000c0d201d80140c401d45030790030b4143c4513003c4090780640c1c405902d040d00a4020440382ca0540385801218543c40c20002403091500c01903203a0101c3d242160b000d90740d000340c03802d0420580c903084169980141c0c040983c06010382c1c14000302520b0310504030380c10596102c3c01091035454003d005e41251111031006015680710b00c0c008000d611040e090640c40303208400005410380d5141040082c85800c29542003400e900002c40500c0e00c14a4041240c855010b900c580c034205940d2020330007241c0101d00521500130450081024454440da5051222000074042c0d9217207905000001c1c00a00010f0003002440c1c20102c0d0034040f0440900c00c80003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 942867005 1250 942865755 942865771
    0xb09180610080c010c06021b01020306030118020d080f0712020c0a09060f0506070816050a030207062a050a05011b08100f030b091f0b0306131110020313060e0108 71
    0x5280342400160303a291440e580515060100c03400d581c5c810002d2903030485051092036012401c03491020f40e001c5000c2d60080ea1114030075030a00d5401444600805a0541c61640c02000c0714183c0540350745041d49508005840b803021513040c809031001c41e0100d504440403074001e5000d40891640e0300c0c108038454246400445c81c0c10f10300301d800c0c0454020041c0050a540c011284180c03035076030501e001e00040c441c540b414007051184000c404104140018202c1c901441b0707400340d458040d02c2d00700c00c85070313130b20882c03174132004201e000404a04001007032b9100000540a41c098441c00031050b100d01d820342d0310404050300900251a0b82c1d0701e60303590064a41d6041124240070220a07842c4c80d504003041b24680c000500042603001c0407a113951000c1214110240c0001000e402c600141c2d040100107017030380680c0b940640140c4d400a01e07541c641c41c040c114281e03445500043c03041661400d02c05078030000050941580310801020030700700b10010482d0000c00140d40e0b0302c0d15109003200014903040b000b512a030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 942868255 1250 942867005 942867031
    0x19080d1401051302095814010b032d010b0d3201060905010e060a0605250804090b011404150c1a0a0522060f0b091806 52
    0x441a0350300c070b24603604898541c0f140503072a541c050000901000c000454100d00a0840b07040c01409a4101d4014019154440c07115150000c100c80500c204030f9000305441c2c040a0740541e100001d08110080100c10100e2000058401d1451010a00d8100d00d44102a62400c2a01c0c80340f014007003440b4481e507400148070091003124a90710120301d0a0802d0340b0020034444e84450029601070611480c0c8080344483c4240ca51440b2030155018000c0c840ca00996000500380b800201e14a407401003014003405014103500465443c2c24000c46050300309007200d480301c1600e1032100701d55541030109030140354041c0300005e5941d41351140001c101c516600c050380c11720031070b201e00b4120001503c0036a01100c86100c0d02000c0619011030864646001070030040003010020302c0c04d820040e44a101610502110b5800c02003a25400d6000b2175900d0768401c28041068000d800a00040c543d41140e0080304a003070000c150002d0580000f02440000c55552556000ba103800342e1007140200009070b041901102d00f0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 942869505 1250 942868255 942868259
    0x4060f020a17090307050a060213060f0507120203130303030e0d0314040609171b0105010b0c031c150e04030311040e010905060d120201150b04080c090919080d1401 72
    0x7800890220703420501e00c040440c0092000f08040c02265485540b21044e10f0003200f041c6030640007904130301740b0803c0580014101044080c09000300ea60170b6031146c0c50350303414580d00342d680c3c1c66003e51408488045010911604c42880b164050103000f80d44030742c801140000d44051114a003401c100a00d02c00c050901044000744601c20806c90740041e0880c10100d082c84c50741c14500c5202070311020355043c4400018901001c840000281110b134001c11009004c0d903603840000c10064011151640324542040140a0341d1ba240c1589851900042c8040402c5580156000380740c002001d900c00012070303007100c04110030140c3c5446064040c003108111541400e013044003032440c0c0d403014050412400e076240e0110344d2a42c0e5236842c250035168030030ba4204446c502c0c00d400034040c0034403803400f144841215102244c80d0071032405460540381d6001c02000728022030010011000409458038405018181008105980c1d040445058600a0305150350314000b00c0b205030102d424400703181c0c40c810060401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 942870755 1250 942869505 942869507
    0x9011b0f030e01050f06151e0c160503030901031a0303070302070e070c030c060c030216110a090b09040204090c080307081804090506010501050318010e010f2a080a060e0702010504060f020a 83
    0x690b0340080c015a480190f10120b07012a80c80f1744141c180ca0b801c6503056000014185604400800c000461001540c0c68ac410410041c2d0280c0c0d480c0c001c160f8150428044600b0030751099004e903000090f920b10010920b803e09021a045502c442d10130707001a00b101d10300340038405413800c3c2c1507080940361a04c0d440d502e1305618018021a00344c3c0005003410b80b44c8240c0190540b20740c060301c1b42025801e0001d03000341d5032031030440e501400f0312103a54080c001e404000161154184151391004401904104055542c1c0c1c0c20400141441801119038035901d081c0410341400c200040c100c414031900c2070f00d41d6030210101c401c81400000d80554422410a201c1d4000688041400c40c115482824125141d4032403108001c48a01041803240580d842d01d944c076480d214054000ca42038006481d4108207000f10740c8804403002580b001c9052024000c4403020b104180b061281b644e20000111000170b07110341b1415002c044034010313200c3d000103039150780500003400030324450001b054018240031480d15400181c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 942872005 1250 942870755 942870781
    0xe0601020f160e04140303070c03090501090506030a09020307031a010608060609061b1014040b0a05090d08062b02010f021c050304020604030222050603010c1709011b0f030e0105 78
    0x10a2104807a4401190800c0317000303441059420f101c0c4098a80f20710740b4100041c0b0002d00300070140c1c00581400c0001580d1750145440340c0c241c880140065165036602810034000e00032405040360140b20b10a000800309aa0540010312641c0801d1003003525450070310f00500311034000c0c010741e214003420415408155582c1d01100e940c00900c0f1098072004020b00b0460b400c0c88000e070b210034a01d609041490b50880740003d40c0d9403060703115000340303501c649402505d0012117004a6410329280d00c50b00e0113550300741c041c2407902c1e0310210041c2050301c0407903540c004c0f45181c0640142c18102142656164046603085001d400907100a8401810503034054100da102ca0303d05409400309005c00000400e040d0b458541c111006150080d0100e5040604106201403013100964200080fa2400e40813446515040c0101401c82a00707980310100e00c41642101d41e000c90015200c11010740d80c980030885200c1100c04541920707105e1340c50325100c2100c0290054199080750240c50000e900d04002c1082c0383c14048 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 942873255 1250 942872005 942872009
    0x106050d0b06041508010e12040f0324090c060f1409040c17040308010f0b09060405062503080601031103011a0a0c061a12060405150a06030c0e0601020f16 68
    0x2804481c1e954840002040050466041d200581d1a00f40c9002c602240c0c15080f0001101c8444103c0740107488040050005000354090242c40d0510340c030741000030980c4038000001060302c0f101c11312080807400786002d0850b14029021504203081c0300041203044d4102c200940e00409038100394561801c0120035800c02d22a0050703c2d44199560000703d52120b11803180d820ba048103294030500c080c2080d00f4090200d078824400c130110280c09010101e2000d08900c15a001c220000d452641000c0c2454200059a041026102500d54240e0441460300840300121480c1d680640ca500d006828110001010780340c5075524054a41010001008000005003452039500fa881c4640750b1561010f04007201c84809800c805418141030001410b04800f012000010444040b19100701209000784215221202160060a2904408009a1090608607030194040403803000081d07519125a07a40b030b180e20441e00078034060070a0702c04201441d40c042041b00f503055510001040701d11044004405004030354 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 942874505 1250 942873255 942873263
    0x150a09050a06080a0606030b090313030b060616031e1107090f3206011e0e040b1201021206040b061c0204031e170a0203071b03020a03030503180106050d 67
    0x224002070551085034081000b0b08030000640d01422603604041000d00a5804151070700c05040c804500e52400001c00c40c1c8203d440320211459407451138440501c4184000e20301d5822035020070212041490751000000801d1103030b1100008a401c1c0c6501d541d900386c134080714409010403190288c00102c0d0019441089461100c0042150128511003a0140038400c031172569641000d892070b03440310201140307054082a401212540d95441d1001101c42d203502440d07200c14542d081804071036442c480e0705040000c140190020640306085004100c6c0a5900d03d46400180d6021510030502d14a4642441d00700a0840b82031003840300807000500a8801d6800342c0760402940c0003000d4490134260140c030700a5030444c4900c0c01922403d0702141d2200e43c81a401c4600906070701c01c0034400d141d030700180e07821180145d004600302444c2c0d94401d0000d502d00e10612841c18410140000140e842d06501d101441c801c1c0e480d1900c90a10b83c000e0b600c0b010300c030b00b540c8a0990511905110075140c4480060119804c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 942875755 1250 942874505 942874511
    0xe070510050d3c0b0303030c091002160b180402070803061309062c010c091e0305030301080f210904050a020c06091c020114040224160b150a09 63
    0x510000c0d46690f0201c0c1d00103840310041070403500c1d410324020a1881c0b4005444014491682d201040584910007101d1070f06140c1414000c01d829401c001c69980710401260040354000302e03000480c01407804066002c0921042c00180380c0d190300c44005940400400107840560909800341d4800c01140401403a80c0e000d11280315074042084840d80101e100c55400c40001c011085140c0300c400c02c985d00c804402e44000d120020368080c418014400c1c0c296001080e915402c5c1076060861402ca070165644118003400c500d0000880820010300041d4000d1020300c0c000e11100e10b01500580c20401c1070486240c1600014044480d144614002c880390b40c5001c641c002203544e0761170000741c001c1c01201e0b503030352461081c01d003000140680010418202040503c4d02c2441c4c0808207022401c0c0c503003035104050341c1021040418014207204051003030b5481129100d02c3e00400d1005860040d41000da0010583c402080440080c000210009500080600f069403002100c0c2c10104110180e0742c030400d500195 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 942877005 1250 942875755 942875771
    0x806070e010c150219110607030e01022106150c100b131503031b050c060c010204080a0b041209080619061208030613050f0f0a06050a06030e070510050d 67
    0xc070500581507181e601c036802400c1408450403c10003904600c20b188031081c0d07001c05070024a4000d03455100c800400000918695649040072009011000010019036409000074076050b9141256010480980007400000349841420403140400c0311181c141004010080c1d410000004130740c50039560100c00001c501c1009001c046100106c80c400303404111860030f0030045032031081c0103000c01128040c0c2c0e2103440614050100c2203c1000c1e2100042180d403000440c0780103820198043c281c0c0092650005003031a5441c0303000c1d42042e1402c24221a18640d100802041100103204407442c001c079860300e0b008560406d5034841c0d031044007a0456010700807001188007504ca0641200010740340c200002c8100444d0351070129171980055840c203100c0c4502214080c0003100f40d200b440e04c9040c0c40342c5102d4564550440d00d14040c0c1000d0000811a0303241c100214658507802c201000a02490f9000038154070000b04440c1050b0594101078415211030b243c21980327541c07000039125094071503038002450107 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 942878255 1250 942877005 942877007
    0x50f070609031803080a0822170903061305010c020a020a17390f031f0204090603081810020607052101080114130201050f0a0509040e1b09010806070e01 67
    0x1c0d9072001d044550550140220810950320081c1c0251981e585480725591110100703070104a402c2002c0c4210403e51600048c003044551085002c602034441e0034904d00106000800e09100040b206560020f074082c0b000700422009105911f108040b038406000020010703800901d140e01c0c40c3c450071402410428603021000360501031840c40d500c02e44c05840300c2030320a02d0130900340890684040e0700b002045502203900d0824012181166a00030084c0015a81100407240e6680200c1d0818420301d500b400f000c02e4402e10b610071180a1801900e4003074441034506012010300031031840d03690040e01c00369407500d81903800180030781e0485030300d08142e0b03180c0da501282c6443c101450f1084210004150b4000100702c80c06511070609074001661107503480d900d0a100100081c40f4180080c002881040390100e83d10340e0350050002c00e4500c0c6041464001003c00117405d4401551100d9007030f401001010b04202d40002d0503e030342e0071064460030784c251301d4600301c5074071a000100070384148080e00441c50456 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 942879505 1250 942878255 942878267
    0x604050f040e010e0f0f0105190c0c08030408130803130e0c16110a170309310b04050604090206090d031e0507030806091614042310050f07060903 64
    0xb0a6480008004507442030398010b030f0710b8904150042c00b82c007403003014500c1e2000c18020340b44641550348a0118a5440e40c46200040031255014010804d050a40c0c200040c800300c0118010750052a04c180c40d64080a0a19000c02d2598014000303070b03100b04401c00070001c10b44049400c4238040b01d0308100603030303845100d16403c0c400d06601101010b100c520300c504024050110440860056511228003074849a00e80c80050501025440d607600c02d0014040c1480c00391003e04081440103222613400444d11a20180708400500c001442e81e12600d220f0881c0c1041d10840c0d60001c000c0340d00b44040f00c072a03008900e4510503801d07030710701400b13864a2000074035000c1c54030200c00340852450075121b040c02d0700b001402c0340c204d110b0490020300408003180c1949004185980070f00c80b54600c149103113540c540261114180420880d40a440c18440044c864170b80d00010140007500c00900345454811004015004c07480c80c2a00007070040500c210301079000e6032010340f44110340c403820001d58528507013000c2c0d0340 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 942880755 1250 942879505 942879521
    0x131a0402011b03120e010c021203060d141b010e0a0501081308070b100815010b1e0d020909091912020109020603040303091b03020321041208040609140604050f04 71
    0x2680d003050b15690304142c0e11600c8103407a044a50420801492041145802e13154058603079001a88102508080003d14200a581004000707000c4054420160740309000a1030b43c4441810300d40146d4036501003c04501c1d40101c10800901c8c0c01c01e960400d000002d11120b000c0e0007051704007c3da01c40020344c1c0c411491301c1805140e41005506403104410701d0001e551100850340c04001441e8488000ec2c0385200260f4408010103034507044c0056800d001c1d0a940d2a003007640f151038401148900794890300001e5004040340e10101c0400351340d4104c1d40c0140704d25520301511048255101c4512041041110302c44c6400607540008049030a034000d56080340500404800a54411400028001019003590248503074034030072400c6882190200b000b07141504400e11010350180c1201d02070b404000d02c410b044030b8409280100c017600700f948a00c1c3c190500a41d01500700e4581a00140a00070280c000c0341c854020440319856007501c420420200c0c1c054041d51103134902940c1404081c1c034031aa6550401c0c11 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 942882005 1250 942880755 942880787
    0x60a0f0603170418090b07030506010e090709060306060e06250b070c0c080a050c100c0506042003070b0a120f0e0703021f09030b06030309060304030201060905131a040201 75
    0x80400044548802d02d42e10038840c00e1004030001d07102852070003e501070201d400750002c2c0000200d0351022015800740c01c008110904000509501d40d440f551020560380c02041c09650b11070885040c01d0001d02254901d4001105000b5812251503080c0d03104402c40d02204d0303d5110121030004000c01d4103015120424004108403060030803c02950350014843c01c2c0c140c00303004d030160b000343d8444580351610000000070b06140c100750040c800760b00704146d0700c0f6204049480d04903451600c6854050403d1410398045403d5400d071041e840148101102c0c50020000440151010519018440ca0f0b544601c1c103e050901a040207420780103035a80d400501090031000d010f004d1a5400011a500d51509000491245c5c8114a40c00100c03190780848080c4842a0340355105280c2c11070310b41e103c0482c4001e2940ba4140700030000c0b45419150700c4082c5005038401d40010480c00e0801c0076500944030001d140040d82540300f080d48011840300c5c070389001c0c2d04501103001c070415212030004035204940b40e130001d4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 942883255 1250 942882005 942882023
    0x2040e09010e01060e06060720030708010f0506010f080f0a0605040c21060605091905040905031806120c090406030206040b07020114091f05071b030b0f09060a0f0603 73
    0x44000300c1904404841601c442c000c104c015100c14140742d01c054203451240e0800c0b802d1007481c00242c48181540e00364503689804003424602600040d15280c0c4a800050712a5140d40a5a00c5891103002c2c07190040001d00340002c81928203540103002d5117005040c081140003d20205d402c0c0d440300d0703014101808000d402030102c5400f810b0003410f0006035071a21160202800d15841c084075952164905030fa849a8a13203103031a40700810450044852354079445543c09020380003a0315511441880259807240c800f40d5100d2254606084440b000200c505004100c20011420b85a491b42900741e88118401c540903100c0b00c204c000b10b0001e1a1540001350032000008000c5580c141940203041c41c2c61003607a80c08501b18484c0f100320340078025103c4c4035070440400c1406151802d0702c086000162415480c05600b840340c0c075112904a0100307056542855841c070722042c020b0110002c5c06d984e0000b50203032400500e080c0b201a455031540d0003001a0f8031582c0c1d070800c0041c0c0f100c40f40c1041004603080682e80d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 942884505 1250 942883255 942883261
    0xe0603162d050909100501050a0e190e0415060303021207030e1008090c0102011a06070519060501030c05030102091e062802070503160603020a090b0c1024031502040e 73
    0x64065030043c115903214812410020350441e61070000c82080c3e84040e51481d0038191218000c0d600b0920b403150041c0e201c551001c0c00d140c0031401042010050484030b03003154080c03c16083c40c0004103003c018040043c1d04040c0c040c00800d400080040c45600c04000c29035486c107403418101c1c0c42c4860000c10a60000043c03100c2046030381e02850085c020078001c015a03940005d80b500590032a249454980c070102c55040070001c01e0b20388800503002c40b5006100f6643e150181c134440405102d80381c001190711503681c0c0b00620500200400f1540038107000d500840c039240c51800001c608843d6008185c3d00b505070f6001c00541c5880755070640300138440409001c0940303090f2542d14060b0b40b100c0c5038001d006100d200340018045ca00081c1095181d1000804d20f01900d00b0000220081d40c4410500c0d0140802c00f040001d07240e144000602400003000060030b910141561a601070380e05c20344007c0d04522000c0c1d002c101c8440200c081400701c0760300003011880c010b10100b15101030302a9900c084d03150b0091800f0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 942885755 1250 942884505 942884507
    0xc0905160806030a02091306111b211e0408010c03061a09060f18060a0305070e06090f011101112101060801030c06080417040801020405010e0603162d 66
    0x400c8610401a4030303450200c0d60b884040c96500e01507a00003a41c081545e03c04504c0e4000c0e04140300e04068021078003c02e40066000e00104142d011b210342c00c541e1444c824a913800c4103010300c400804d50040c3c52541003102c0303031254002c03114011224820801c0003007004500e80510600b045800074a1418000d1000b41485070002e00281124410070408261094401c41c181c00f185048882805004086c1418080c003071800040d141c02040ba40342e1008403103002c0704499a01c14014000d596281d03a404211894080710080042404034406070050006001040b40c84d642d0021040501c603003171030110303c214000303030341140540104280440700e82c0000620003600d0040541180d404100101103516176680e07510101d40c0d8100901c4050054400800241310191050107043d03042030140b0202c440b80c1b04414000e080c0360740503034011205607500003020232413940c02c04244109113104641603070940c0380501491011641d03001d128000c22800c0302c0310a0116803444000e00512500900072044c0d0120400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 942887005 1250 942885755 942885781
    0x901230705010b06120c03130c09021b0d09060c031209061b05030f06151e0c070504090b0105010818070608010512012a2d090503030c06130c0905 64
    0x80103407800e508245811100b800e200c4100e604a02111140722801c3d034031030400d100c1c10f0b00041d240079440c43c41c1003440000315900e8281400645484240140c0c0d401514000070b403044085802d40322244c01c8184c039100090340100f80b03001142c0e09400c00300f00350502880e040711020030090304550014684461a0700f8846175601003803802c0f15904510b8a080450742c41941c40e800100e445070150613090b00040da15080039112014000f840081c0030b401c1100840580d5507100c1040e005103d0000082040c40b12503104100d82c00040006550401c041002078072040420503050040c20b0502c00600c0100b1410200200034103040701d040000d6175880c03511444010b000a400788541e9224030f010140070030f1107203418411002154940d400c0f0881203641c03001761810a00f0344030062000c2c05440408080c1050701d0003248034070140780b98a40500411101ba01400c1d500d01c0d41c01142c000e40c014010703048603800c0006c00980011100d01007094120385845c02c40a420b4258000402550070b04d014403610001d800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 942888255 1250 942887005 942887017
    0x10090816060e0d110f0d0206070b1f03030903060c05090a03030e0a06140a0809160e06090f01030c12050c0d030c14011505040b0a0801051008070f050a0902090123 71
    0x69030342d00310841180100300c1c0c40150014050480c20110450390000e240040130034030541005004030782504000d0300040c00a030000402036800d950402c04001c10542c00640d0300c43e02c40d40003240300c400c43d401c41d20020700303121590000402e40b581c5e030344110788980c2c002c40507140c00c07030740040045e404030b6280d2130000c2a8440c00002c5500a5000010205046000c2c3c40c1e001c00c0c0f100c8941025081c000441ca0844000601519806080c041c001524200c1188980c4c1040981807204050340f103400c0040501041e000c1c0107101644103c00c01005000049148540104503240204102d070702c1c2180b8201f0a083c409801300040c0d020b0032020b034501c201030b00008074900300c1d030090110070502c0c407070902e042c0d0a90f44083d41d08044400020340600c8a4038150380211022000540780d00402c03512040c0130760031960141d400c20803c08a407e0b0402040600b0040c07100a004a81003c0000c94a01000300722940003078010441c007149c011030b07000340d140d01c21142c0300760401c0140b050203c002140200c0d00c034952310036 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 942889505 1250 942888255 942888257
    0xf120504051e0d11071a1e0c0304030506060f010c030f020f03030a05060f0406080c15040915150e0108010e0c1201090b151804021b0a06140f060f1009081606 69
    0x51300210034900810342c0e0301164505030034181c40f19100482400c2e50350004581007039200c5650280310724210010044c0044210140003140c1d11800e42c10182d01d001002040300c0e20580f002d4001150503680180e851204d258181095058031080707036010303802c1040e403c40b0115248804010884504019000f55004400035600f0507520b841036814032080e82c4580c010400160b108804428090400c0310740310008031101110541050307250074046090b510f0403980600b4890300d28009002114100500070001d107070310704205030780d03809140010709a048144988108505414005022080c02400b140c0362400e502d03c4201c141c0da1108401c0b4003d00c0007800e007a01500f9104e50030b0031443c61a070b08680e42002c0700b04d030105016440e581044003030f41c0481d840f41c500c0d4901c2d0122680411040201c00c0d5864491800072450b4038880101c2d42d0940002401005146958402e01042761a11104a01014800d40e9141d440e00908001aa84031040d51700286041c460b10f51540c12101143d035446003620f0172 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 942890755 1250 942889505 942889517
    0x10b010e01021c0516021215101503180b09010e0601090212150301090b070203120c030f0a052e0305010e0309130903020109060515100f120504051e0d 66
    0x200d004a0303890141010301d036040800e540418001d1800307800a000008030300d01401ca00310b1400c2c0c5c003199414050f00d080c003019502034800c040030300403801c0381c403940220001c0c10b038000d40789000003461101224040503014140d50300d05e009010b20081540c0c0c0802900b09000030564104184181e000344400c1c2c1540d285070041c44004101000035000300d500d100ca0b83d101c0c8034051348803801c01503c0a2004114507a140d13580d010610001a1994004c40c42441c940c1c000e95128500a10342c244c94990007081d4004c15a070410802546000e04110240c100c403510f4400941740e41e900007100c404210000062075120000c1d02c034035001c440c900c03200b102900e10590083c014800007031503a40d5280541c5003031030f510940040f03414485002c0d07540412021406840041a4a01561a03d40407110140c41504065140c1000107140381018260170161403003d1078440c45000100b24010b10f00b401400150208a40354000301c2c040c05010081c820b214410324070200701c0400c00803183c59448100ca0803513004110 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 942892005 1250 942890755 942890777
    0x80a020105061e011103220603180c03060207020f03010219030b0f0907050c071d270d0c11040e030306010f03110d38031011122502010b01 61
    0x40100710b900443d000c940303449411012407030043d1402005030078000c1281c40306000110050f0340d00201c44844e20266000d851165050050040c284c900010100411415045c0310400060503080640120303500402e0040e00da546510006000f1100b00c1002e17503040d80040b0700620400181c41805003403038140e440412040480c001400300350160f0411040d48050347d480015030541c001d1006040490580050b9280580c40365200c007114041c940c9031020791107520041040c26a0609251903a02c004103445114420a003000d41e0b6883c0d1031002202d0412070b4200c1440e082012101b00d09544000c010400e014107118032607001c2e6030345c104880a03400a1000030b80500e4403402441555060b0305002589440e107000c40c080c18003c1e041603c00041ca4003001170244c1b4a040004810000014294040540c582802420145840b2401c40103844003890248818800b89001702141d054101ca904200d00e82c4d81c5500000fa000c0820048040401068a483c1c059055042d403100c5c4d880c2000b40c07102660f00f1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 942893255 1250 942892005 942892009
    0x15030f1e060906050d0b0c0c0328020109170d1d011a0a0305060f0601110d0818030f041509080307060f0609020f0d2406120b03121605010b0d080a02010506 68
    0xaa964803520390040c85c441c0e0840041200400b1199000741c0c2d40c1d20707540c80e084044410500c3c59200c004801c3e8803203246802ca04800704c4e21028a005100b0f288000d10a20300c454440090b11a42080000c0201d800010a01000829900b0444c040003020b08a00b484035110022140070302061809030b4551200b1647c0038020307140841d03512080d0383d0060002d03c11a030354683d994640701c1d00130703040f541407007003001c50303041490401c00c81445d0b2900c01d83d44070a00e904180610104012001d041188140c109000508403000d8900035201100c10404885103600c00f103403410b541180a0707403c501814000000c03004140f06164210201a10141804100c0c0c60b0782d40f0210301c100c2c01b03a03005600545e9420007500e24000c071150451200e9508940d0340300c40c1c10003101d519280806240c0d104d4804176032460507288118080c0c1c13080401d0144247c000c2c001c401140a041920f910900b4180501850703900c0b25a0305003e0254890400a41e019010701807941e0103040070016a000510414019804c01002907554 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 942894505 1250 942893255 942893261
    0x20f15031503160b091908030919052b0b250e0109030204020d06170c04050a06140d05070503010218030613110d030e06070b0702210415030f1e0609 65
    0x2d158584007070700302074104680000181d00000038164403001c10110b1b19401e4400392607403802001c0c0c0100656a03800000c00344541d81c40005080c5291040d51a8100305c240c0381c3d0b01011401088210890144410744021020060464140600700012000420198a116200e0134000f44545641c80720903182006003101c405810702d2602d4005080c00c0da00308010b09240c0c003d031004e901c100d00d000c03a02e95207819404410150181c0b0300d0087e40d106160000c41c504051048907009120034a003400011704200e0444124403030b8940e1300e400364400090b1082840001e0003140d000e030600600942d900c00840e4000d8042c0d81c2c003c04464864025000454400b6403040042240160300103c100b1300c9510310810850175581c82c2c0d03c19001d01207080c00901a40d0f8941005000240c4201034202c070b103040555000b4903000341d1800084005018010380f840d96030800301514100c4880d81c030900001490340c030b4218060442600c110680f107041c200d800f50b210704e0020704101012415042040b10664810b0b0300f40503 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 942895755 1250 942894505 942894523
    0xa09080f19090e31020405040b01050103140405120a050d05040807020901060f080106030b010c020303030a050a140103032a1401050a05090a0c05041802090108030307030c030b1c020f15031503 84
    0x40c10003103543c9080400c0c1103001c036100b240c0c010851004e1000032a004078095500071101150510701c1200140030660b0184200da810201c01c4040c00994506507495640d140d11456001c02041d5003c1826200180300c0c0c0221208041c800c1428005800d007450f003440c06805c01c0104a119598032000402c8480c400e070300009003030700e0b035030f032a124503910f032440c280e0007001540c0d241030411181c1d038a0322000d41c900b08000c50144205145c001498640b100040040318000e0915070344240001c0f004002280e4044070406c0c22540d42c60055102c0c510880c411600c142d4940030050010315071034100d00c0c1e640010340c40544204400e120510080d55094140d9032035141c0704c1c100600c0d0f2600d441091020703040503404000558441d10b180280c5c5502c030b030002070881100740e00c6260a40d00000401c951140d1500682100c03040c44e040500100c8440000100804401e20200d12000d045282003002e5540c0c0414150b070f1640d001d80300034003540b00325209141642c4221580030300302902629400103800c001581b202 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 942897005 1250 942895755 942895771
    0x3e071503050601020d082e031406040b0712060302090f04140c01050726030c0705210415031b020d080112020d14120a0f0305070908060a09080f19090e 66
    0x396401108003038501e1b5034080e059415244c10b003c014440da074a0441c8086140d03c0d0101c0440d000c901e10714040c04d07181c0014580000c60f0f04107a00317000000c1d6400c80740f0703038020b0a00d04043d0301351072403000240002c100c1c55001075889070f200700c2400074642e070340134540340501d001d21105038007042007050007541c64080307a03107080c005101001484040351050395403030080e80c250f0b40c1e52022240b20b0801c050040d003007600c02a10f180400641001084001c1000706401010034180c250840861100743c00180294860013568018801c00c841006101b1340c00049103010b2180c182201250594000359651249201030002c0b07a0b201001040b50003103085801c4005e036008114035941d051030b03640c41c0108050f50342b0000b260f20445502404203114600902980c0d8003030399500107030400b013190040540e10090903a0050214882c401d01100c0c4010800a60044403c000400c0c03403686440c01c040c0503c221103000c1c03441507010030b2104800d4980c2c118480d401b1403a5560740b4a064454180c40c80d2003100b82c500340c0d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 942898255 1250 942897005 942897013
    0x513030210090503070b04030f0f03061410031e06080d0c08221815151202030702210309011b021b0d08071b060f3e07150305060102 58
    0x5060300a40c0c1050a00d940b2460649003400217590b10010024025a001c41c0468840400140c2c820382c0405010840d9050f0724003448405c2c40d11a40c00b485000348210240140480c808800105000350083c1c504010140700003103131312202d4442800244190f01800a0f80c1c050782e515202c003544101c600414a0390007040d160701c1c01000c50849001c0742c602280d0080c030031207040000030708662944030304008004080c4d40030420884014440e03000d400241c10045000114110200941d9400303854041c000c54241c500690340e44450038141d14008071445e283c6070500da0f43e80c507042d43d1400200503500800c41e80000740b010316081d080c07003295105400310b003000507484501010700441c0c490300c5615003070601408140c402140380d198084c160b0300007102550b0401c141814103c00c81541401074000304010319014180040c80c10b8000e1418000d9022081480c4a4031724140145404040c80c445071041c0348498411388050851003a01c64000e0703c034506520007062903c14516000e80946489003105078090 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 942899505 1250 942898255 942898273
    0x201020705060a1d040b03030301030f0c0905090c0108040602040f0f1a0724180b07020606010906020706030b031006180605060405090a0504140102180f061201051c17090405130302 79
    0x100341c02035030440c43c5a501036151b641e501d85648042c4000d602950240d22000c0f224115814411a590f01981c0125080d0345400200140c440707000c6503142c4000340034030300086e940c3c4440c2032070006801190000804010515000690340803644607940032a0b80b4040d918103500c034014000102130140c400041c0c880d030051150100620314960800003203500c00c2e03000040401c00a0419800c1484205084540320410410302c1002070b0100b10540d4403e40c00d1800030305880c20190002c1d01c0349620700c264001d0540361751140e500b40c0e070140001003041d091208100400c0303a4500250000700502400d9586440c542035011038941041030460b401d84038090315815460710784942410040500800c1982c04407000b1680c800004028002880d40fa00600c01d00000c0008841c1002642420506241d06c1600200440c6120000e40c244481c1114000c41d101095400070000600031340b41d1481001b0840303002c00c0d500010000b43c52001c1d0416142c1070b54100407956488a030004d07040081d14000d8050380c030a6501c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 942900755 1250 942899505 942899537
    0xc1209030a0801031203020d020a120f0c0e060a4107050a080306060d0501080d0e1206041101090803040f1502010c020a020f060708030f0f060925090305060a090201020705060a 77
    0x3041803103207058a8010714007239100d03581074102e811200b0201e00040303d12016a1840c229030050802c1c08075006002c01008903c0c0703501601e40c003442c80d98a401402d010441800550195101852403220003100042440054001602d10603200006095224480040c02c060302142c000390740120394000010f24411100743c56141c01e581000f4401c5231b0205041061007500c0c3c4a600134980207100942c0101134403440558041d1100c80d103008528014154400800d0681c040001d00a80090700504401081c003501c00c01280c1001d01500b1912270307444001000100c5680440c14a400c860516807c1100c0c1d072400001242a100d00e0010640140d11401500c4003520303226981102d903d02c014555481c2c11a0b642d101d02c25604200c8000d40c0c1000c401040081006200c41c81170f034028400c40d000003203450118000c07000100300d11040a00112801c010b0005980a104018040c40e0400e048410740d01c0c0101c000c030080c1c030340418104d0050003019000100b90610009031940c107052078480c020300c2c2100c00d030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 942902005 1250 942900755 942900773
    0xc0c030212072109050103050721050408041e141c0308060402130609050a050d0503070809010c0c121713170a02101211090a050919050c1209030a080103 67
    0x982540d081d0030f0312200c180041d158907418040c0341056254205014603003400582111401402d000130f00489545002d049500384c4100643c40510000014081d107940c00c0115841c0103a0300580703441c20000c84901103290f240401002100c200ca945141c80c40b80c01414800b8143d0b166600700003a90182c02d000001a004003659648108058001818941070059007541d030b902982c0504046000340317005001c50f003040300f07040b000b40c40165018103080001e503030740c070b6900d228040015010341008a41c803401681326000d0030090503009151100131035120032800b2200c12644030300721802e00c142e080d00070b8403260700c405031040c0140f0900c06800c0140303031205001011280010309952409a40440001a61001013450411410755202e42d220708901d0301c8002103500901c081a0000390503c5017020b26515031802d04250b03902a103002e0525200c5030b0400d103c501041c5043c2c0e660301e084c54100035460400e60007500d0310382c500c90560440d580b0780c5402d094492081642c80000610960010b1000c2045d20b1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 942903255 1250 942902005 942902017
    0x260f162909100e10030c0206090d17041a0a050601030506040902030601060f0507021e090907032402190e010e06130302150d0c020318040203060d0b15061204060c0c030212 75
    0x420034966000c81c120004a0305800f015480010980d1001b80307680f0b0503810000d0381c0d03008008070010900d440903003070080c0c0704c210072405800314003010200040410580003111030481603141d20ac4155401c20130210b00140804a80b424002441e100000740e06191900905a00d1500500600201e9081c1081180d081e0301702244181448010003205005860b10040c0000d40001a4542c1401110250800c41240700181001c900c030344c021102440403402d0440300224480c0c8081c400314104040c2107121001e40079030820741c003801d2031280d2400c02c13a58002018000d046000d9071811031034510760003001200e00662001e40c0582c49412001c0c001810080446142943c20040003410002103080c01015a41d2542c08180141c0010800d4074540c40c8200800b00c5111342214150704510b80f20002c1030001c000c008000d443c1c0c010200101d1201c05104180c1c1074a803102800e4541d4409180e80c0e0f03014095400e0310200c3d9500d140c41c0000350020705c680c45004000b0b6055001e0207840002c50802c442a4003c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 942904505 1250 942903255 942903257
    0x3030f150d02030609010203100e010305030f16050d020c012717031b1f09050d0f030e01020f031f03022116060f08010f260f16290910 59
    0x41001805030743c08001e51031080150b000017690b289840c464990700d202182d030206490742c071040d00500c002003011042e10340580000c418070303844401d880c00c80104042c8111b4003404902494550700d01042d40442d00403030030142a22400250b200038244144044040308404500721000c042c18030071860340d410141d4100d85004200d0381000702039042c0d000c10a4040e80c1d0582c55501086240140c1c200604030480310150a120400108256031120394441c910000c03514104209065000c0300c9a00a5101003045214071008540300c00150210180541c0162203042c081a5600c490310f1200300c45159000660361701400c1d0001d0b4030004081d8540b0b4010500e402c5046c0d01481805107202d80b0030b540310500034022036482c4844585012405000c1440c107810004140088003014019011039a903521501d1074005a281510010545002c2c180700c10240d0141c524014540070402151076420b103101500d401d84e1141080188008885100c0d45002003201b283d02d009100b804503a1030440070801c009111 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 942905755 1250 942904505 942904519
    0x51b0f09150a1203020d020d1b030c20130207080901210507031a120d0f030603061505010f09060e040e010b09010837060c05040e04061b0203030f15 65
    0x10040080e4090040e6040b11003942c3c03451082c41c05040d4108038000d00c00c440c40c00641030700381d18400300800900c8220031040c5101609400d800402d031151546076801900700c010940006031581050701550484000316101c0d168030702a03842075440c40d208840403a544910046e24005560005407440c0c45500752403041c0d104060034000c0d60a055002c1c0d68810052540c2c0011080428030f01c1124060008003424090040d4105140341d2010004118242040d1810041700c10011840300b00c018000581008001d1402d2018041d00030b84150082c1c015a1000d8848490780000d440303045802441e1480b400000038000b4002e281e10b42080d611a0990b000c0b48400820041481004585075071002e9000302c62030b6002012500c0f1954586205079542074161101c0c0740c01600d210206402105007107000380080c1d58901d035584203240207900f120010700aa00c82c64003640703054145980200002c3c29480601c4d08a4042c001c3d6061010046900c5021044080c3c0c2c2d6940769225075842c00981102c00d2034020785 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 942907005 1250 942905755 942905791
    0x150207080a05070e01120b190207200109080d080c09270118020a0507080310030c0605040812040501020d0f110a0809040b01050418270609051b0f09 65
    0x1007800038140ca28041e20041c824945000182c1040c3c61050b03100d01c2c09084203404501c001141c030744025410018440445480503050f543d40341c020b2040b401c0090a144e580c03589002c00300c0c007494440702c1c40082602d401600d940d0791403210751650345060480f400540164001203d202101c0702501c09808050002000080d180018010b0140d050203c1c0c0385001001004020313030105103015a1500e84007030000c2d030034a41038000107401806400402410b40b42d004c40012441c20516007090021600028030005643e910724001e80554003a000d280024010001c080c803030340140340f040350708495041e4001c0c60100380c080011a4080c6151500b1030402014403084111940b0401c145101c0d640a8643d00f5990f22405003080700300c0f10344420480c10b0110a10080010041d0210501c248854084d40805c0e140c065550340040385a12000814404c204107480380180f020f55405404c42504c91004c40c0d605081404028041c0a00e00031000e0740302440035031a01d558240181c030f03260418892000070103000e03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 942908255 1250 942907005 942907019
    0x70305191406030d09120f021306030b19020405180712060b0408010e1c08040c0306050c0319050103050c011215033c080f0d0c0201020316050306030601150207 70
    0x111945648034102030704400344030440c5400d001c2c03441d150b8281d0030300200c818a40a49800b00c965444806041f1100c800d2400095480b60a82500134020b80301c0100841e54a03440c0032058030800782c1c1d07050b00303029140b014441c030751030039208079425214001c262008032041d100c90f50103140801003440341080324660040000c00058020740015000010a594665003456642801c407944400d105006610001c800c80d146082d00b00304109400c0c1510f0500c4080e60b4504180041516540c00101510f02e804100f00d0441d88410165005000444c0c90fa03500c40d2071003a00c6000d6803800c1c0405003940d0000031440080d50b0095400f10a0031681c41004600d00904003000030304600154800c0e170784144413440d1840f606000c03450130051600e461500070022465001c0c0100d00711ba814000038440340c00000c0d5003004600440981e075092560180520003d465814002e020b90416a125501c841c8910f12409565024000b601c0c072414028000700300ca030780703040301c89a820710001107001c06600a042002c5201 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 942909505 1250 942908255 942908261
    0x903020a12020601060212030c0a0c0c080d020105040204110c070509100e01030c06030e061303120f0f091b0b030c030604060e04030c050c010e01051204020f120a05120f0307030519 79
    0x402a02d40280c201585840b20190a045500608201e02d0908100f00590005400c055a403200d61601d00740c0c0404807103207030000c041c1401c7e400c1201c035841080e400c1075071250705400481c4203503c01c0c0c0c2e00340004031403040364454034040c1015001e22a0080340c01417085040144a0341da20642811500100c542e0320801400031000a070000e940361040524107002e0303160940113820b0700c801944010300c41c502d00003481c0320320350180f201c0007410803d0044203448900c80741d82065407240c01000041244031600d0400000400140c2011581090500410030215003007030705180494944140b928a19620a100062141e00082400b0340c4107a9a000202e82c68610078504c0748124400d0b15901030504142c10900d240040f100e8049041141c0709a0740c64903a603000040d240c440420700e1844030603807282c0c17001880c6289a4049950004098900b03c1d0800310300140e404555401602514a290205041e4043c5441903540b03040001c0b6082000c11079080c801d074403a0f0392140c0032900d0b04040100109080080d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 942910755 1250 942909505 942909533
    0x3050409110d0b01020a211e0522080a0602090d0c030f052119030b091f0509070806060d24081905100b01140a0809240a0903020a 57
    0x109803404546101e10340b00030302c00d00d031201109000810030403036641c0e24070743d5038050350703070320f0404200f00741c000194040c02030100e124014228031b0b00262000814034000c100350841c114403070f000e041a0322416190854600810265040c0c500500554003594a40d81c020794052642c0c0b03500b01c3ea0b03540d40039020600c00a00328000d10b100303461041e440b074861b0420f00c0c64001a0195800c041038181c0e06240da0040d0b00040750300101c000c240480505042d800c0036001003401c02d8645400809100400021626102c00c2c41c00001e0001052491240c981f010300403155001c5681c0004903000c44d010074400e20302040900101c0c1e05002011426107084d420340381060403441c2a908402416040503c80700d031081c043c13a101e4060a140f4440042017a469107a51383c40e000f45540354107562260220410b9200c0d8003001141121a964141c1e503901c1400c00414403541110342242c1c2d405600008140025400650769404907000501a07217529a8200700b001456454011810751155142401c00a607042c0e6880710 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 942912005 1250 942910755 942910781
    0x2060706060f0e01050f100c0203060403110f011b1107090f091703040b0c1308060c0a09150e04020307030f0e2a060d0509150f070e1008070c03050409 66
    0x81071403810300790b20024012508014010880d440044c080e60311801c148214100003105c96041c0c0d028482015904111890340c041c0d0180a61001c210500d40c2200510701040c100c0022180c00711216980b8a08940c20112805882301c107901009004900c2030000c2480c0314010002d840c80a0356804a8008450351400420309880c5c41d851060144000244206031141c81c0c3d031403041c13542c540740c0c1d80d049032940002d025901c0f40d0004101e01c001000000c50030406080040202c64003820186032000c4c5a402400c2c1c8000000c03048140440c1414042274042060981c0d612030000d0351001200b08030181d00014004010140e0b0b0341843c81000c0306500600c0b084038405070161880c0c1c0b0403405003030040d684010340d0701c01002d254070f065061500c90000f1500c2005801c0c01c0081e00380c951146140c01c110125010340c100040450500c46e0300ca20350b10742c0501a003a03a07200c01e4058441c0c081840614a064242c420200d0003100014020501498142c81d8107446894042e140c0791f00e4240c04012070f112507031002 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 942913255 1250 942912005 942912011
    0x206040b0a0305091b032e020406030f0f151502010b04060314060f13081605010516032301030602090d15020406030f090b07110f0307200a031707030c02060706 70
    0x1040485045c01810084544101e40c02e19003015031000c80c7d51543c0d4540c0020103d01d40345001d20740302004100208410030080c4040d59180d03503440b0020082d1015005403022070349040b0040100d03400d03d2240703102682580b864a2181484c00f1504403030084601e591205554a40c50800381c02d585a1003841c01541c4100503110a02d01c86940641c98a80000e189181a120000920284108840a201055501c08a043c7d41d4580842c5100052241d1210080142d8200401d00c001d1811031015815204156a0300f0031a02c07900484d040d182400c11424100c100d0800c0c4014000f02e2620313001800c91540c00b03042d40038200f2881c3da07100303403010860742d007032000b1580450140440c0b82e01d406545203540b80c0c1c174010700103112191501070011001030f04150902881d0112074a26813428049410a4182d01003620f440e00c10174185100d6442c174041d1b003a686424040501f01e424504000c07800240c0e6040204618031b0368131020324084a522444081d070030702810f01002030050303603000001c0515a02c03601c808 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 942914505 1250 942913255 942913261
    0x21e030412021204090b060c03280201020f190201090b0406060f09060506302403010e1b010c05100b03062d040807021306030201110a0c0509040206040b0a0305 70
    0x107015058900d112040440d008484000d0080b000c040c10b88050b58000d004c002503210704800000d40314400d1200003283c038080407070f02100d0725114210105486095006800404400c013030b00301c0c200c2c824003000c0c2c4660700040c0042507101800103460000784071103000000343e0342801e0300e8122044000b19070403102241c9840c0140540340100304040300814101e4010300496040000090084c00744100240d01030043d4140081060300d0004d030600c0110481428107030900b0f00007414041d09581d80c80700c845040c4240150b0301682014402c8450310389000c005010703031401e10360b244061280c11442c1e56040019075440c48010810034404c800301c3d141d4448000070141001020b040c1480c500030001c03a028910481114001115072200d200f034210b04900300c681960320344c9001e601d14016408003940020031000c8001e04e0310103d0b8001c1c0141e0b8000d0302c03200128071550101e640d8038404000020a401a05002000700d4140450707015000b901c021b0805003026121601d0f03200b20b40060031540002034640e018 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 942915755 1250 942914505 942914513
    0x20060c010f150611031b03120709050a051c0609020402041d060301050c070b0411190803090a140a090504060e0f0a0c0b0a0f0f0207031410060b09090c0706021e0304 72
    0x450020704550404034504c0c1514080242c49004000201d040384006400594805d5814000c40302c0c50086000707542d4460403d80d6000345051400d000369070281e4140000420a03240501c4403d084041d660052105a94181e07918000340c0341d011b100320b802170380a01010070b00103401c03030036401d445a00c0208030724580340050405082d142e014008040a400805ca140c000c0b03141d20a81f10f90058010002c10419415080170840c500311480700b501c0402c4d444800802c3c1404081300a002a8000315603400c607090701e4038842c03031010001100c0f081d400080c2c00b00c1008040d0084d0042548140030380b1002889104c03a22a6030304091038480c5020140d00002403030001c01c40d06503c040042c2c0a950250f40c1402d00003003002c0c00301c1c05c005000c00180b1815940c102c0186108000b0760000c0c0d81c3c8181c4006000c0c031400c114a50351400d03903180c5d02d440c0e0300744040802d90111074010780c0d01d0054000c28841303460700c44000d0140b40d540106429030740b140c0c01300b1000700b41c403500640c4120f98098003000c0303998902d01814 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 942917005 1250 942915755 942915791
    0x406090e0c0a0305120a18090501080f280201050909010b040501110303100603050402312306040507050d0507020604030806010305070e0622090c0306050d20060c010f 73
    0x501030712440142c0700c288041807000807100c2039007404407180c540d41c4c101030200343d6480402100d1003200c0c031210240031484080b2034004904071400001101c41140c00d02e8501c50f125901b00e0495003100742664498001c100c906c00362281c02c40d00605195140400c1403000c204241001d07000107120300c000041c10070a43d44e000352500d145031564800386040d4207040a0341031003044203100324000c0513100ca0119041d5510703900c0c016603105200788045660440d0684613040c50103d07645050b0181d1410419503940d00c001c4024046106114448405a5803040c0811000f40005420707441082414001c80b221803101c4d20a090240116400070125860640380090905500078000c0341014141424801c00710340200b03074000700b48411681e0302d807685000c2d00b03001803043c4002340342d01402da0b005000003040403403075000550580ca00e1394184501038988090012002114400070400b01121403001500c001070704a200200d42c1c000c02c0305141802c60070415003910b03500c00008450580c1d42403204600d080420b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 942918255 1250 942917005 942917023
    0x181f03051005270c030f040f020402091f09060f0c170408250902040e06040c03020d18020306010608010305060f040510020a02100b03010501060f08271c14180a03020406090e 76
    0xb504c4140b440c500810b4181e01c103100540000c21490403c003250302150b4843c3c042e40d84211016228840b50381610f6240501004a40b03100d00200d0000c100100e40c0034851810b5183c6200340d92100c0c041c5844a5076a861744141072054011481d60a20010a0040b0180700c450104201c0007504001150311048038060111941d0207000d841c1e20401041143d13014854485510203011035000440e48510103040d03020703102d4556040c503450b01c0c080390f0040c440800003000c10868025000c03a1996a00d400050300c400c2c40070700014050b82d100500140220009a007603680c014410b40030740e00196001e1107568282e810a44440000d60807815a8078070055892052545442d03080b402444194544080034080e41d100c0504c40080100c2a40084c070350a081080300600503c83d9202e2000106d2100790064a03942c21440c5055100000080c1c0500c0b64410b244450005408509451078000004400d021050b46110301304d070840805c0c240000541e40b18820035008040390708011404200071031080342044105 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 942919505 1250 942918255 942918271
    0x1090b19050103020c1e012a081f0308030103110907170a09060908031006141317010e0d0e030106051903062d02181f0305100527 57
    0x24a01914540c544001094115082802e005035648400590103040032402c5134800c514401c0c0340862000304a05502c100c6140444c900410400c80c00458220030490640b460500098907000118540c04ca04200050502c4080c0348030010036982c80d07642c00250340090380f041d5180f201300d6520000c02d051000303502ea40407106280010651103890b0509069403030142012900700c3d50b2780c0101003000125403004140a4020390030701e131030b0316014a5045540c02203010343c3c00003c50325058180070510003800e41c0c03641700c4251403404640d810302c4540c1201c441a8000343d182d42d0b49036900c5009050342030219843c80c225503900c0c610010310880a060035504981d015602541030030180300c0d4520f0603d8940b405480c0c2c841c0d40410b8004030300d40a9a12031781214450308110000001d9500c030045c095000784a5804000004c0803090486c0d010008908000c4a0707286840d10007803020071030140300b50300640d4450000c0c41c82038138154840303020400414814068603449017403034044907818101001907036845050 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 942920755 1250 942919505 942919519
    0xc0b07020d0f110d0e0a05031b0102010b01090f030818060a0c020a06050705070504021b030c15010b03070c06050c192001060f150210050403080a0e060106141312080301090b 76
    0x20030740c0404d035940104500c0504000c903145c0c80c01039940d680b0010000401c0003c00b100c1100304030784142d9110880703556000d40035600c1e002e4440c0455020380c02440840e00c2801c1c20038465407450702c90301e071680c2c40f000d140c1000e90b07000314100000c0d40e904005441244000d80d144d5080310594410f10524414541150080c001c1c184505000201d00088550070b0f00d2040d078000da211440310010b10031440e8400c040954a00010903464510200010041e900001295500e03801e039903a00b40d15403880c03006940c14800908450410000b2883c0c64204a42044244400b5490800b4442c44000001060644980000c00d1440c00902c0e5804411695140203502002000314524107080304c1c10100320741c4507082c10500d0560003614210700074007122075100c504070340a001d1441c007850000c1402c10704031201d0340d00b580303031042030010139100043c1607050701c80640354202e1841d54080341c4100707900110f1510b001d46021005c0442c1d900400401200340c10310079107685483c0e50601d00f10707006a0303059403412401414 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 942922005 1250 942920755 942920777
    0x3030c031608070209090d0305010504061d04020a08030f0d1406091b0708030106031e0c08180309040c020c031e07030201031d30030c03160c0b07020d0f 67
    0x500401100c040c50640c20440c1c51074415894866098040c40750065880130000040040f507260100e1001114480c1e40e900b08001c1c1e8860003040100c1c1d44038001c1d041034000c00c600070803800510300040380e04a80020300c00c07081c00d0758074489075207145c1c04036000d49244800070680203036100e101c0c000c4104605a03500209018540a00492000302d001004c40e070081040c00030031402e8459110841c0d4455401c20754240e642d68440202030090300511095519a500241070700305c1544061081c01c103c0282581c607868035464518100c880f5030340400349600705010410003031650395510320a94021440c03940242c1000e0601500309414105072000103c62007116009041e202c480100c0d0349010f6aa09080010340f540701c030b54014051030700480c40b001480c0b0030160602c19281c0c0740303000304031401240c0210200c1a911000c614403580008e90301602c00100c00c0c40420450850b5505440d00500b492138410180201a01c51240f884800c1d9044801340e00090a035180d02940305510030b000d01c1927030130900f0880c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 942923255 1250 942922005 942922027
    0x60603110c10230403020105040c0618060302030606040e012d0e13030e180613060e061c1b0e0a05070c141903030f050105040506011e17010b07020f0303 67
    0x1101500710b00b151a9101c018500800350b100460802e01041c0d550003070146081d240c046d000701030950381510741c0b02020400184892040d8130a0780e10700150f03010100960714001050f4083d4101038032041d130140c0d0078040440c07682c0b007a4441c43d0003850080002c40c0b0b002c0c818000c1701a00f04403402c240c2c01c0d4100055041c00070074078081845400c8504a41c0310300a0125600301101c0820061031010303403103242001146c00c0000100403850040c14200d41040c043c1d010043e10200b00d0b12680f045611280710000069540c2c81d03c00d0310301c1000ca40c50ac13a01c0c002191256905200002402005009c1509144060001c204000400e691041c5901010000360500311b5004d403000d850090f00402c40119400c405200360402e022000e522560032025103c101d02c14500034001c0c0011903402200c481c80c140002840346450300416015020684030409400078090001a20511040c0744c14140240c0404001d042c00050000d10300800d03000701100e03101e85003441000424800304090610aa100380106283c203 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 942924505 1250 942923255 942923263
    0x706200c070618180e151506031f17012702090402040b150901020c2407050f12070317040308010b1305060d05100f081e0c13060603110c 60
    0x99481c5090005603040c1c4042c0e81e03201e45541e0b13000780c40d1601140c4d240c002840d40e1074001010941d064401d451a88203a580b070800c8500c421a4140c80c10390120a080d582410f000c0002d5030841041c03002d11040c03140c54841040b94414640c0a9144c030207240303440b030310f44200a200740070913806902140e20305003120240c000020b458280d00a4850003800c1c0104046545550101307078a070300c2c0585881000907901719049510341003892954054010b550312080c032032034001c0c16102c103010f0f1420280c0700030314020068055504400d004a800340f04413503500040f02001c101c0790748a030041c103c500c0d80c0c400883c5401040c082002c10240ea0186d081409d1200007a0403025590544030140a29615044580c10705452002680c1c0b0168101100190f80d198050a40d00000d10941c241c8007100503403030750362460090000080c42480003a4010003584000c504207800c02c15a5002400b040f150000141c90029104044180700c000344580d4a2800304149038142c0541d10603020240d41d560b0030302050286c42c40d15 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 942925755 1250 942924505 942924509
    0xc06111c0f020f0a05070e0a0b0a0b0d1503020315090a0c030503040510050a080718030602030a0f0c02030a050f0918070809010b04060303121104030b090609070b0306030a1709060706200c07 83
    0x422441200010f030303145296071009d842031344002c1000221540d50410503106600c103091210106040c000d035074502d60941121002129405030062039126401c00d610034407a5006070200c40c0e0741c041d0245800129162420020245010304083c559403840c3c50304005044241c00da180b07060010501c001e4500360f81060900e40e12800383c0c100031003403100d6440c1128261581d034100901c242c5c804000c1c80084280307580b203220f520802860401c100c0c102410140c7e500d025540d00c840000c2d200b0462011001c1115010303000514000e480759011a40c004100004450201e85200c000340c4407004000c4468024041ca030040107040d01c0800c88a819601c0040000b003074480080d4910340c0300d5000040620107078080720700850308070f0880442418094219a142e0005039400c640b24403480d140480c0c0902010112405848010001d00e4080026a160501d10002d010240500c1c03506101c1c80c5810340f902d00090034058415480003400f0b4541034541703800501004800701e442c0d0403e10810222020009824003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 942927005 1250 942925755 942925769
    0x6020d09061d01050d11070618020901060509062107230d021c0203010b180f06030a0f0f0c0306050405150a0303081801020d05070f0c0c06111c0f020f0a0507 69
    0x441c0341c2400113139024803514035030408091604115240049650380a03000c1544501801d0181c9503d14074144004500250701079071007140c1c0001005118055001400340c400041c00f111b04001000c03108a520020481450807600641001c226005502050300c0307aa201c2117080107040d003001000e241032240a042a070031034003039000404401e549400003800d030311140030060079540e968603401a90015000700110b80821002400300d091145031065800442c0d4402904803421551041c2c1101c004e450308070a0084516541c04030031491803c0b03400303580c900c00c0742a01c0c080b400b64600010302040b500c005126081c403040c4203004005640d9101d401300d00322500340c50101400d4451445c804014420301c507081515620010350f03581c004d0070310f8204a124012944800201503049036003602c86469098000340300125040091005e00c0c000d0080051f42d003090740c00c440c01310101041ca040480e4050b50781c10f000c103201007409111a44c0c1008105414401c00c0f0103003120301032582d20107688080d1402048 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 942928255 1250 942927005 942927047
    0x907060c021207080a0317190f09020a29030f060105091c0c0f0602460b04020a0b121303120207030905010306140a180e0304080706020d0906 62
    0x2081d0742d905030b8060000403003401500c5202e507903515005d6540080341012030104565031304450356081d0a41009220300e811035401f80805140340017607002004505d611517042a5100710700c0c000f588421401402600c2000c4c03410007500f103100340e114003402044042d4a101d01d010410800a00350b00c1c54115000780c1c081c00d00c0d90f00c034a001d40000d5071045040c481807141c442488a20b2041c000c50394085c00071074000c01d908510b400d454a0080b6150022151019030003241e4014a125a42036207884140d00b80c1401d40210710500c4040340c800744120503145c00d441401071402844107519051041c01d0041842c2c1182c1417410b403440d42a1200384100170503c0b100706443d1401d484c2490301503100c41d210800740600c02c55407020300e40f40280c0598842d010751800130349400c2020421020125080003e514020860f0f5000340c07420664a50b50100341072050074103900d03070302c03030501e850000c00180c0081d04914019005890410700c0c020b15002c0b400080c00200000808100032554200e01800320040003402c0d40 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 942929505 1250 942928255 942928277
    0x605011416080c060604050f0915251e0509150d0f0c020a0b070827030904020c0601030b060603011809060e0f0d09080609030405012d2105090706 64
    0x203441500e60241d4050404800003070200b004150114070750b480795408480810854880c00410b01c0c2c410012243e904440e80f104151503682820800b03041e034415140e080f4a8000031001950305441402200450080790a81c00e00d28101f981b01304201c0701d100c90318501030707080422540005038903500c2507001f0480d11400007180102c4c50001d8103e07100f032200b900418042a00f030503030001e54403914040113135040c144400201e17042a00c075201d12030243c000380422201c1e0a2000c15200f4200c030300700844400c21b03c0100312103403064136036001600b2001429005001c0d2580b40d41407450450000800d0305100c0c5104000502c007a900007080282c04425803400010300f0340440c0341003401040d015080080c140f040c8500046070309070000d02d0022440ca00e941d1950340c5661008404e80e2042d00351400c59081e0001c1c0018025540b080f20000129a090141a1941c01072042d1400040c09100c6000707001a2040300c0d080d0311640d00e60901c0240e100140c00c00c219624224840948580d40c900580041140155003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 942930755 1250 942929505 942929527
    0x9200708040503070b120a140a0b030c090108031c0209100806060730020a200312030c0a2d050d0605150c15040506060607060e25080106050114 63
    0x15207014040140c2156810398840790106495040500c40520460700180011040003050148019240d8a407a0b0b081702e40d103a010f143c002420804035166018425004202501d07500e80c59810700138842c45024642d10781301100d0000c0303070801c1445107440c0240100001059038035030040c508240c00d00c51030f00b407403141c4400002a0540c4070f000c001420021554860b40038100d54030070901d401c0c44418840950200c4940cbc42a610b541560b00d02038451071003002448000c0080084450000d038000302030365100c410609044480c2d070070035a514004840082140104250411000424614000c05e46a0940401c980c000c043e40d80443d9000c040010201c0c140341c0c200102d80203000030f00002004000c20f0280c004d20030f4080e4000ba805180c1303500c1f50407084060420f40300121802507030090b0250120380c3da8070741880300940c001d80c8100d840d9130b9114a4004444404e10070300030340c0000668107440c900c224451480341450203401104d05039240c03490400031603800007807690800995596543d01ca0b03084070300f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 942932005 1250 942930755 942930757
    0x1905070c2a15120e0a0b0a0207020a03020312040e36070803070f0203071205120a02030904020a0c030e043309142203090306090615080a03020709200708 67
    0x10107994810301c200100300200750001d014401201002070100910f41446868603a82c4003c10f20250180f101b0001298665240d03800030030030300780013500241415030750b680401e1400380d03580312400410310082400d00090000c0d091040d00312a003680c1e42508440d09400300d03240080201c1030505803002125412055840c03e1042100030007514054a03164082410501940751030007108a201c0d00982c41c1c08078407522808504110180c1190044c041088410050001c03640410564002d41c402808404543e90342c4d03000800708406256196820710f0802d2034080e140411102c160f030310560078103c010b0400740f42d80d0450001a121b034808405070600354005465429101c1d000030a440c2e003044903100c02071004000c0540a03480412072101c0c08002c6220300342c0240031001c0014000354414400300f020442540100030003c0c0a80c400048000440d800018400e140d44d0005074681c0020610383d090507014400c01d4002c010118081c841d66081c10340d90300008000107020000380d2400b0400c0030034401424 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 942933255 1250 942932005 942932009
    0x91011030c18030d120f1505060c0a061a090a0c02031e070c0e01080706090605030601050a052a010c0914120f010510050f060901021e01141905070c2a 66
    0x3505030344d08640f01c00c800030520502c1c50719409000d41400c0b10240080301c68030405442c6206201d000d0141c50503c01000b000764040a2645654845c008050f40490b061b03124008950288542c0044540515020301a08660040c511040d040c50800300c50304003034021040702d01803d080c0121303510901c0c00d040a040309020301030700035003a070300048804a008004804400c0c140c5080c10304955405644150031186c1545500071040010002c1c0085525035000e0f5019000c4607500703080607030420141c3e42400c103044a400202c58511200308121f4200c00b0000c0c1b0981001000034075022101500f841c805843e502c83d552400c0d401550080711140e600101804807041400c0c0c008028041c60400e0241a001c00c134040c01200c0c0300d00c054002114030307458440c088690106d41a005461050140380980c4041454500d80c080c455407141900c842c2c1e912092245031040042c12805a030320b00c1d103c0086006c58000070000801c0c41400e10840e004503401e80d0a80c03c2c8052020010504800662600e0600640b1a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 942934505 1250 942933255 942933259
    0xa0b01050d090c080c0607080d0f0b030115030303180b01170a050a0303051501410a0507200612060604090501121209210219030803091011030c18 64
    0x1140c41102040b80f085100ca040b58031050031251420140e004208891140e21801890307074000700403441c0844c905030400c2d030302c01d10504400204e1900e02804030b0b0a4812080c1c1ca0950450803034000d20800d03816101c0c62424010301a03200da0b4007009650f401c0004070060103810380728204541d0a0f40c41c01d5041103030300440b56001d410b481031600140740c0500070704401c1d240107188040d61018414694820403420300c0c019a94a0f02c019008105440607503103402c4030b031008801c18200c189101003118510000d02c82c02c62195243d541d40d04580c2801ca40805c85400b42c06000d4070a20a00d546540e070f584251055072240012601594645100082c2144250b6104841c1745003840000103d502c0200074101c58070b4007462003100c00203040c072011102c0b203019000c0e40c40c010b0901c901800c1185804060520761a101138410761a031403426201140c140c0190b481150841c1000080009408041c0501d5804150a480a1040c10400040e015041c04020590740040c203000c1822286029400345141d040303200 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 942935755 1250 942934505 942934511
    0x8040911070b1b03070e010e1020070305030f0d0b0d060209091e011509080f160905090c01080a0f0f020306040b0111031209031201090903031109090a0b01050d 70
    0x41646084601d40041d00d06807800e40a010008158407080c42d1060b08080440426030b20316074940c14203407061045240314074108141c0a06680c1c142c0c0305d0a101010f03109090b200c4901d250012a0401440c0c0f03000c8000f030031035810190701080014000016944680c0e04241a152070351b0442c08242c0c010101d588556a00615204400c0c003440000d034010910759100751103c50707841e500d20401d00503c42d5800d41890203e41c0703001c01000304134003100c890300c2c03440300516208c0c0d41c1c0741e5103180721071400d608543c0700342c0b55401040c840c945804800618000030700c803100d0184801d00e03045050035216841c020703a041c103001801d0700180ba8502c280d4015000081142d10800080a03c0309210000b50403c5a8050180d4503000200300131790301501b405100040000015460700b04a500c41c0c5801d98005080890240301c00d1198141040e0300c6161503019203501c3c8800525284203040007001e6a4200704e40b5940041c0c10040c070b001d16100c00c2c030010361003820010b01050440c011001220640309407040c6040c1545 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 942937005 1250 942935755 942935771
    0xa05121b120d2a020a03080a02011107060501060215041703070c020d2004060e13020d0f0305090a0605030c0a0311040803070b0405071d0a05070c150213080105130f080409 75
    0x1800004614804003c99248060b960119255840c0c010802c036000e03520050540c400c0000038500780081180803c50b200100c1c1c407a2b8600d031041d40c0c0d078010704012100140c8990050160950422440003040e040368080c20319070505490700000103018151090380200c0000c00181d1b540d0007001c8034006258064520314461001d410034003407400c0d0400b0703007074500038503140c102d90149130500502082e034110071803c01098960720250100c400c002ca00807078011011021100101c1c2d220000d213002617000340c8800c3d9554214108000e0450a0317900220180b101c188244200c91814100756800c1c0310943c00c0001d001c0c10003a40660460040d07601c44042c40c0300010f20712040103560a007650091b80300300c0c100da5040ba03c0d52034040c004500d41019003074840c0c50400040f81c1c02c200390046500801142812201e511040c2c0f1903110390b4881c420708030202900060580c01c00d5402e40610300c01005240002c020505001d0280240318011100207040c880140c12200284015801180e0087c00000800c00c0740340 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 942938255 1250 942937005 942937007
    0x120f0c032e121101030506030f100b0d0203060103081c0501030b16020106171612050307031b0501060902071101140307050706020909160906050a3e0c0a05121b120d 72
    0x201c2d0030000300b800a0704140204082c8d040002d141c01750340d9031400207040c07400004c00702c2c1e900502194003031700da204404038203140241c2c41c2484101d01940c0a641040d60350191340f8401d4105040581040e410180307400010804121280041900702c1c035aa000546050500d5004038090074103174004e12007010446021040c45240003881460004584165144083e51075405500d030600245016020350420024440001d101c3e00181240390062108681007c4040e12034a0031070312203801000d056503000880105000705146800c0c8c8104c02403074030500c3c000240c0000009130001074a504180280403400c5030800c00030350103845481d400527101c80d02d0b034a464000840a00010110030012403000000030655510a10072642040c0d00c0c0d44540703809854040583c1003d00ca202100d4081a124000700d84814440c0d40d442c04103440346070300070309031096294100702c0c50030340581c40948106d403a00004c3c074240c4e50100d000c0e41d80e039040d10344003903052000794081502d6844070482180d0900614000102c49 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 942939505 1250 942938255 942938273
    0x220c0807050f0306090c01050c0708101a030d02070311040605030a0b072a030513031b150f081f050a0312080a0c0c26120f0c032e12 58
    0x1d8000316030711a00b0242c001c080c55101c050681d031114064000248003211540250020303d00a80303646e08a41c1001d580700a803504080304450f07813103405603c0b40b994200d9420401c141c410100c10460280800280000020f980c47c099840000c1c458448840050342c0c80d40d9980c8444001d1401800782c44002c601d0b85882c4140d900101c4840010502c45004030b0b08101c482c2f000054000b80455409000d9002a00c1c2941c264001d003c901c60744000005000c00020000d03840b10101c1e280344490880e02500300307400f0501416120301f00c2800c00494898a401455005100d10b40000081004070018a040d2950070240c1c0104d410454100503615000020040309000810070085a03603a07102c891340303504141000340c42e124020600000d18420504011603800350300704401d400d1242c01c113188030001507040e00303054000705403c0c01042c810008002c00003102100302d5909c0400301d0102440d501d002c03401307150000900343c40c1d22600001e41882101e0f000c0301d4400c000c00350400402000d00e40340307649030007180 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 942940755 1250 942939505 942939509
    0xa0305041d040203120c030403120206061011070b0714060405060f0f0c030414070e0106050c01060902160b1503031801030b01020a121107030804120b0f01030209220c0807 75
    0x3000060301070040340168201c05040c0100c0d4004c01030030008a008191031846c2c0c214007041a4540010400000050880001d101c3c141c1140d401610b9145001c504112580c441a42c0c48001d01144078800f0742d982c1030100c1e06806075002900320980b00e80c01828481c12500ad84582c9010a01c2180d0500050000008034140f1801c0e110110b00c0752a55810500001d8034000c0c1e402200846050022500182c1c2c2c414090b6a6030703020808803804681c0e90803003c8120442a030203500407540c002070368100c0b9402801940050041a1303070030352400d42900807241800ac140100034100d5441c20340071a10f0520004840103245038000e049030b860380314000d4010b160b60302000510740800c3c5880d0120000d5400800d49001e415009852261101065002560000c01250164205001e0780d0310200000e00c2e014042e0001d4502020a000741b00c030b1900d0f10701540c0300054014a0905081c0b00108011382e101040d40f0360100d41105655403007203110517042140d81141800420039148054082440d9800041c00d0007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 942942005 1250 942940755 942940769
    0x9050a051002091c0c170c091501030608060124110106061d1807030b1c080a0305060105031b0a05040504050a140601030207030509040e0c060309101d100f0e0a030504 73
    0x10034002c14070241c07188400c4e01500816034503101c1420000b402c044490316071050b801005541268200400058140600304c400380d120400812943d40156030603c242c0014040c2507009040340c1d4100b985a03e4800c03400391011161520900c80e1499483c401d80402606442000083c014191141d8010b0141e400c068609100d0503034035a8521311a01c1d10084410107801c0c9100901096140d0203021005800c0012019400c040c5078090320724480740780303440381a40394060690b0b1a03c0340c0f1a0b24005055440c040c0c840360400c0310902c103110030507038107003030649800d98548212030f0385001d22202911140030b545d010a83c024a85010040d03000f900b6000116402120300341200d803560f1302c1c030054040b4010050081c0c00a401489254000d003031540c401d00041031803900310340035070140720b0004000e540202c2d0541302a0304224954007191507140202c0303212201d14510034441c244c0c16400c07036640c0c9219011182c00982c0700c045804070503060381d1014410410f4541030310204155810003070465031091141c44 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 942943255 1250 942942005 942942019
    0x30408150a0b06030403230918061008010602120c070906080a03020709110d0e0708010e0a0b10050d2406060201020a08010b0313031d0d030c151b0309050a05100209 72
    0x6903c3c68a1000c903485107a0646400401c0c2d1441d5400e00031001c10001c2403520780504226100f51951004650348800d035070b2007011043c0d03150120510600e2003103014994240b2803280018081d964010800a980c500100340d100d4903041440a030500d00082c0781c0c02145058500b12020402030070106210542034003d03001c50328010390740c0c0001c1c012105104002d08103a001800442c9009900b50401401007440d801120b42d41130302c4091590844200c0c0746066070642c070890810080041c1072900351340c0035048030702c40f0744c0d07042c509030108041445601c1c0047c0a8102074180740c000c002480001c07811a400080104041c58580401034006d40c040891000802d211f1000010518071400880744508164005a1007407020360341e003950b0300031850503a09401a108403084842d9207494802c3c0340214003076034030428145d81c82d040a07004840702e85000601d081c20082d0566940d9a22082601070007024a00021001403604185003800c00c2c2840c001e01d103025004880c1001d6500707402800200200f1141d203 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 942944505 1250 942943255 942943271
    0x4051507050d150b040b0c100f060e1803090f03010e250f0317160f060b01030c020f0c12070506121f0f12030504051c23120a02030408150a 61
    0x883d901035118071600314620f800304402c1c04001310130b40c09825071880310070443d4080601e6508500c15200810705000c03d0a40d54036003042070001d03040131540c005200500500f0060580c0b40b8464503032080c140e06500500e8010b0250261352800d6115404030281201a5442840710400701c2403030f4401c3d8060500b40006558010606101d0f08907410200e90380f100c1034802e2a01c54500160545d0455502480c800e915005004046407031490f000396840d1041e07500041c141960000501281da0520325201103511814824540c0400000d03410041c0d0400c03150744458164035148540b038400c96402c84e5810050224200440300071089116001c0c24034122904041e0342c4030000a1074400546c4108000c2d8402042e0801c15480d03c40d210010351030103440c02c0d500e860b03210004514404031024549948011415501c000c0c40080b0310751440700c03800c24032540600c9104081e90742c2d861400b100b210010407000514521903030b000708201d030020720056007036414a550100101a020200701c4400c40d0142c04c0c1010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 942945755 1250 942944505 942944531
    0x1020f03030f04030e060f090102101a040905120706020909010e16050c0102090612040c1e030311010e16060e0901151d030601150e06070201080f04051507050d 70
    0x102911820400114210380c0c90303005800c0120005070080e81404046014001c15480f0b42004200d10280304d0134155417052810700091902030307800000c0003024a0024041c0c15489205000d6000c140304450114040985080080c10041e60191040382c4250004010040000701c3d00034084c8001c00320744421a0740c2e81c400c540c58880301c040710140410038a00044045190140010f04078200800d80018100107031000418981d0703010000b00e03c0f01c072510034100003c00011101034800341010f142180035114090860300d004030054000142888a03880300d200c101e2109601030208202e070b61080b00c0c01040803511581f00103002e4040c8000160b0b203a00c40d00114244190403d048501000c04070720b041d1892002124040c3c4401d0381c0080c0c40c018a00c1c00c0000390b41c01c1002c03601034204030034041d90740150a0400381109245003101d038050181446428090307070b04800c6807940000300386140c0140342c3e03480c40c2c280c0c101800d440c505a5421280000d0151256001025000501c050315007041202520710b0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 942947005 1250 942945755 942945763
    0x40914030a2f0c1014030103140c0d05192904020a0b070804050d08120a0204260703030e0d051b010f111e120c0a02040b060a0203030c0313050f0a110102 67
    0x4102c5580480100c6005040c110700e103801480b4a80781000d00c2607020a0501c005034020380c81562070f40568003996030f000300107000500084908540c8030340000304680d507840e02c8014031001400c04c0c407c0315401c4d501340031403803104c40ca1582d03040c40400c2c6491984420201d81d080309031f6081c3e006000010021555401c9581290051a040b0140c02c1c1040e02d0502041541d001546003180d245c40144020062000c40641541c020481c0c4080541c985080c419540000d01c200307502015040390604101243c5a4082015003d8030f8040c5049030f001c1045001294014010100c01800d5105001c00c1360150581100803010a440c01d985841d055440c0e00e50807107c401c00402d0300111034101ea100b4542600d0740c0019202d0300d03a480300c1075405180144051000d61b030040440d2800f01d4020710564000c5141c00d01c00c0089000040790800d003003400448000396680170041c16014549030010108808000100900e152113a01804803080b40c0d1002070703600d0b203130043c042040741c840380c02c1010404c4560001c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 942948255 1250 942947005 942947087
    0x507080c09010e150424030201140f030c1b07090507020d0c201906030b0901050909070b090a09020a0210140c0708180a03050336040914030a 62
    0x181c9450203450340b01c03050311000104044d8a40c420b0790342d10f041d503a40000c04030402416001c599900c1d445499400050000078000e0405d1855500800c10182429102c409590300860848400e548498041040320b8016410742600e0f2032600c9035510006100140f44c0000b40300c6d120644c251840780d89014800e84803402d041e00010000d0101440300c000a010300440c5298040001300b903e5000c0c0d00c00c102e241180426508040000b0b503c0300c800100d41c2c2410900c15005020a80b03040750789140000d0a90b40b114018015a606503400003440401d84d51000445d40107000c9080f411980c9541c990406981e44650303d40c038841845c10843d40070030011110f00107a02c00c17220710142a14206a1b60342d00c50450340000301d0180d000040c41c90401480d101c003003546019501ca0300085545030500c3c44041801841144584100da4601c02e000300110301d4810f810b00401415140070919070360300c0c5420001c40e1401d05940215200102c0c0030441e2660141545007100c1d5020486400706480881d03c0d9003103c1c0342 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 942949505 1250 942948255 942948269
    0x120a020d0206190902010e0901230603091e07080d11061602070501030b061629090d140715061e030f0308090a0611072f120709090507080c0901 63
    0x80401d91507283d00710340180f805944145080308410b49403900048100da801c0c0c0084000c903a44803854000312188490107841030f0011154203055103810310119a41d0704010448140b540310254181100341400c04c24a005084a0426100d4440140c2002404049803d0b290085880b0340780100e00e00c07440074040004401c0141c1d014180b45400d003001500a01a801440c0d81c2040d0200143d084400b2072403950310800d8401c040780c0c04c00b580460344041100f14100311846002040c0710034022160000039403031401143ca07040251840601d004c846010b40500c607005442041407021000a0364129408607041d12030b9510410b00f841120740e00441c1c1110140401401110102e0501e000329001d41183c540c007001030400c0302c0d001452a0340f1a0140c0b442c100c403c103c01440400c0300070400c42c1403d41035441201003150b01d80c0d0b0f0036800344001c0362104004011341c003621b0b090001112100040c840640641241c44040c00701440078a8043c1c0d0721100c40c0304461040c012030701000914941907030014100c0e244 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 942950755 1250 942949505 942949531
    0x16090821070f0b2a0c1519090b0604060e101802090d140d0f02120c030c03040306020a1d01050901030c260103060e0106060f1103070210050310060201060b0d0e0a05120a020d0206 78
    0x303406c810404208010301240c065510a041100c0928a82d01450300c11501c12141c1c855282415418401940d07841d411421800c580c040400c5642840112000b0032a0b01c00b04215940c8121342e01c50900900c034074007900d41c000081014620611100a03002050440c0c00402c503510040310000c119002c1d400510301c00010f8020714200c1840e18001c4015050125010301582d00e440008001c42d45541d01691046481c5c030380100b60301c2e00e038641101583c2c42d0482c20840d04040d103400140020494410446428181551030710b06904080c0707d09502c01414240d9088501c90700c0c5800d000d030101790310074031080f101981004d18038408003006001d004104c49140e00d40c803a421807a58400d445181c5281040f400d02e11046c030070003000d070340c640c000d031103034281143c030f03030a80c0d82c00c1640a4006403902c54000000b9a0b0409508001028440007101c20b000ca03490000185001c504021500f800321188010302030344100c03011310310030b6a030403001420364804c603800700c5446900000d4166100c038400c840710390b00015 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 942952005 1250 942950755 942950773
    0x1e03091a0402130203191515121a09010302010518060301180b030c0a062712140a120c02060408010608011b0c02090708180616090821070f0b2a0c 64
    0x6c1503004681040361008208041c25140c0d0000e40120800c1e600d400001020040303054201c0000d4898007003030b000d8007140d1141c1c3c108041c02248002006120007410400005070f424407403402c0c9405011480c074024140760341c80d43d5900c2e070714044003039200641c0b100c24505001e2141d6454002064039000c2d00c050540400e8600c2d01c1c000750f440900030300350840c2102d4054440d48401000c007030900d000d010000c48000900e102401d242c0300c0714544207407480b081d82c0a0085900820b1040c00c1c080030301d40303003031a000d040710603075102103003c5004560290043e9070a002021690b0300c2e06420a1603900d80d515102030308100c1c204801c6482c01c1013090060742000058000c260b00700d11545015520000203184420042800c502243c0b52400071214404c2da1038604080400090b44180020300a0200400030010700e00c40301e030002c2620482c0d4140d8040707074070f00298501c108200303c0c940c002c40715049005400d291411940b0390207840c10051400c0f00300f114000d403070b200756204681036600d01c0c5401001041c0d80e035 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 942953255 1250 942952005 942952051
    0x302010e01050c030d150602030309150702030705060a0c14070b01050603100305060f0f0106020708032d040f1a1c0e0c120f060a0c1e03091a0402130203 67
    0x1080d09280141000000c00011881800402c0100800051180b000070281c500100c3c0d80f004180b16049102150810014049031110004e07500110500c001c0d088070468444082c207034030710321070000300134194014082004001000c03984105070a030000e03203a640d29681c03150144292446687c0d0020441101c0c0c80050180d818014040c42d40903117000080e51001c2d480351106403400300215440d1481d855880104654070404503111801807400340011300031b280c1411100794903800340e4610010b0f00c0b05070248191818404154a102c2110948415996561245400a82e090060141c0a44140f5101d65000f005074928112800c42d0680d00d2200b9034102461482409081e03110203416840c480c1400280c2a59518440000124030780d200800850041c28121401c142c00188585469880d03d9580104141c003c1c00424550010300c0c0d80e5901510305203404e80c010800c0000250029900130981641b110790a05211b00440c022039070300e00d20080008010042e03200c200d801c49192090100841740c08 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 942954505 1250 942953255 942953267
    0x206060a300f0f0605070e04270807060203010f0f0b071e050c04020c031305090402011b05030f040b04140306041104090c172404030519260a0b060c07030201 69
    0x40d0302c00c40400e01485600d880e8070200c0c220140d41950304a82c0c81007404140358002c202141e0380c900588080c40050250f1412403d160740d4050f00408003524070b9002d50421991004981000354004000c40d2296150301c4107070019419401082e103031900a09000c10b051f55020145c0301980e9011450f01490304004c80c1c81c05540360020000c850910903481c2070403442d680c0c4d0002d0f00c107980181005680b118030f12070a0780c00c4503805a00040c0240a00400c2c0300c0981d9104203030081c0201b80300030030020941d4610f0064614880e4000c5018058404107010802e07400c104018011200b20100c03c07080740d04504105038172180150703002015900c11529041c9242410341007100c001d4000e0011102c0c09607a1204568422014490140305070010181441320685d8803001c2c0d5004089060170f60654981030380c0140413442201003040341d145403500e84403411031041400001021a4056031040c8040e2001c0c1240b00c905d0542c0c2940803113040c912000355030b04001050350651100c400c0180680c601d543c00660300 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 942955755 1250 942954505 942954599
    0x623030115270603020a0306090e0d030e0f0115030201030515031b060904090b09060c07110f040912110d020109031d01050702090c0304170a0509010e01020c0406060206060a 76
    0x1120190940d50380545880302c010350014401500d0140ea255071403000101190255040390807400e280c05a100c0030150300185e20540c0a04c207081c002601030074582c1c510314000d00890450041d44c20454854502c2c0048441c80301264801c3e00c00f48007a8032510080740b084440c5625160b0143d0107a03015820f1429486500e039221400506054584103804c00803c050f210075940c00da550780c4040081c4002c183c02005402d600503582400241086066600c0190314002c0400c0355105000c0110012850380d074a50102c1c1c001517000d038100c1f00311400c403240a00881014586280103025150300c40d640c890041c09100000342c0c0c0741d03a5400002038486440b0b41001c2415105d28100601405003400503180c08000b14020050540e1b4107403a07250615008501c02400c044c1c0b921188006e011103070407550010152030003c4024200000e2064484c0d004130f103414170000129030712030305008001819540100b10603028100940300e4055198545040c8020803c200320402d404445030600181c090080b102e009030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 942957005 1250 942955755 942955787
    0x1a03071742150d090204060b070317101d0c040506030907090b10090b09041b05090103060515041502030c070b030a180c171002040623030115 62
    0x212044007990001c1501c0300c40c1042009030034000c1c09040c151624121404a94002120196151001004076140d2030080882d401241501c8461040840d52a6000b15001d44043c0c442c00307071a0748aa0500806d00310124219a00342010640401c9496101904000664041f0800076118882080c3c00c645501c9000300303000001041031001042a41c1c0300c800440c000d80f02c0d040105012070411245074201e45145041502c5010a1b00d10340603015008404102100e98007444079484c0c0540342e001c503026054500c0e40c4200780300300c600186080c541060140140300700c282c1e001c000c4540c48809001d1110700c9204482080241400300304905e04103645c2e540c4100f003507072043c3c1e03007441010800940f51403040e4008440e5580c01100304203130440c0520400c601e030040150070741e41034940d507241c1074201292809081d4600c0d41890741c188048404100c5102c41c0043ca6030215900c42c6d4400b0002c1034800c03618803092203020000b20b01c500c1030f000d541c1034905031101040c4072040105110404c2d242d1001ca4034910b8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 942958255 1250 942957005 942957031
    0x102210706050c0c0f0f1905150403080a06051e061e040b0d0b01020c2103070c120201031407051611091e10081f0902060d061a030717 59
    0x240950203028042c10003458141e0f11050006416400c4c08695110001c0540c0725050700c400481c6e000035107619051b0840e01d03840d100d603014245241403501030f02e032100280c010f15050004040d40001401d200e209005800c012280c0c0700c600b0446400580c280d6001480e0200d039804407a40750074001050648103040c15469090b401600d491881d0708913030702801c140440450a044100c0d22170003040300c01d04003440900380c12681c2d0000103c0d0452a0f094040051004180d45040c01004008a80146801c2148180b050b9941e80c442090b00c90b01503000c0b03000070f04110f031211060110b400d402d40100c0884e110302d03051000300714600300c3d2030b190b90384269002100e2048006003503d902410a024801d04c81c040701e01001c3c071306405001d900004c3d001451300a80c09000704540c000206943e500300400a4188a00089120304200503018056021754040000541c01c0100300043e80404200c486c000c445a4100340701c07000f40802804219000c1000c00e460140703549018400305101d81c0d001980070302030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 942959505 1250 942958255 942958267
    0xe15070f172511180703241205150f0109230702010f050906091b0d0c0e0405010f0605090a0b1f020a031112040e04050309040504080301180902010221 66
    0x1c200301c5407070084403003005401902c1c03060034000340f030703080d405500c80030390b103a2240d00b01144211801c60380080c4810f04266036400c00707032450001c0d030840d11001b101800301260020703112031010030080040c07282150548103107041942c0d03440c0d0b40325810b0b200d803000340c0040841ea0b00e0000044040c141d81481c000081d08948109030162a104160702e005840307560000514012403420001166000307064424903034031881c00c206c00c1000c005010300a4880c400e41c404860703151400424000a1428070041406120300c0d00032902c10000103001c6c1c8124092802400b2418100203544200c400c24010250080c0785440018103040c07440d0011201c0403000391440c00060308841500c0074444807240c107240141c108040b19818580d000c40c032000c00c101c01101038013450284103015104d5105520031030480c09003100004017802014070a603010035802800901c61440e251030b10b012036900900039070f6000d4a00e04c0803c80c8074411849619903443d4103030001c005040085c21801d820300031940c03440300091010009 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 942960755 1250 942959505 942959527
    0x3020406060c050607020a050c0111010b0904061e02130501080411090c040f0b090a060305061c0b220209191104140f0603040c12021f0e15070f17 64
    0xc120040941c1d55482c8500000351800505180c13000e0045170441d80f0594900c4007040003c5000c1d1000502420140001d5140505680c0500019a42036512000301002c000034841c0c290000920280c801c4610a43c124085c1c03180012401690000700782c14010741414082540624142500b00340106e0005140e240710000040c10700c41c04aa503088590404941000b002011002e140054200d922700c41d81413000b803202003480ca0f08a40300703980c20140c5681c0441e1312500c41e40c103000e0860840030845413015640b400c11402e00901035601c0056001d2000108004038040c2c10b01c00d405650082803001e0340d88585084034401e20292504010070b907a60344c0980007807840c2c000100000e050a04040c40881c240004000b030003031242c15001c1c01800200104000038441407a1041038400da54034405d103214a0380040745820b4118110005023110080c150b04505402100380c1c0340c88003084401d1400302c040080d11800d0342c0103032000280081da5003550b02e00021003103e85e080300c0c0011026a00e040c0000024 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 942962005 1250 942960755 942960761
    0x5041a0d05070e240d050c190305010501080730110d0e0705040603050604081806070f11011812080f1303060506030a1718040e0c27061009030204 64
    0x10b2024049a404101000c1a0800034504520a0610045900c29402d80325424801c2d1040d003c1c0000d00560320700006194080d400282d80e00040d10b0303002503108502e40c0c030024000301002c0c0145400309a445000524a03841020002540d40134051604d0200740d074403c103200150000204100c010f82c0300c0b0318058244441401a002c021840080418200c91126055040030140c2d0040f5004600740701c000d00104400040c4182c105038085a01a5550901c1030441d00032100404a00d0344120001660803c3c00300c00c1e030080701d8480c01020807940483ca01001501d0001c0c55031503070800900c0c00481000303818249000c1a4069005489440ca041002c00c0111441c1c0d011a5096503641004141030007841054400e5aa0090081c2d005119920181e01c41240380d2000b440420600400020000d01c600d040306010011000054021720050154502d82c0b511920305140c0030740a104003c41020b042080318048900b09280c402c2425603a481c0c9600303010382d0030303041302c964424080d606d04004016200e0744 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 942963255 1250 942962005 942962011
    0x6060f060d0903200a2d0807081c020406120504020913030903050106030c0e09210708070605010e060310091a044d030c04050a1107050a2105041a0d05 66
    0x2c000b90800000ca0b01d451158032845200c06824200050140d10350f00700d20022600c6c00da5000b4980c2034a541d06031034024003030721400d04400b6081e2a1440011002003c1d6000f800c20390700d007600d0303141c0c081c104076119608880c000c94000e50300030320f003001041e005d00309524a5580306000c3e103003200d00703207480e5102d582c00d5580c40e9008842c10129020200302c1c05106c00e07143c80d082a00c440240111a01607a003500c006418100505414400081c001b42001404801c072003c281e803040090281b03603504c803040700b0102403c942d414040e000e60095841021039500c2034200c0c040c2d11a40404101c40d09400c40351040382d00a104540d004242030a2444c240b5802e81440b00140002c03020206800686103400704030f090071581c4449840c1242c0c0b80d10042e43e40440e44030410401a140003403242e66210000c4041d11106040c42d01c02d50780024800305100012914040103402480030740d071000356288a110665480880200c0040c90504c418041c0e2403040905031070a203003501c1c07040d080c54402d20481044400035 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 942964505 1250 942963255 942963317
    0x2030c070b090c1011101a210106050103020408060f040f0b09160603050906060d0809040c033306030c0306030b13021206060a030f020d0507030b0906060f060d0903 72
    0x8482000c2551401c60f0f1100d610b114140340c040200b40d80c007445d059480c4c13000740c0303a14030103a00e0b07014602c441240441e10000c469402404980240c00c1c8107440318000d5601c4c100c0300425424020045102d502034000c03503080f04c41500c0100040e03a03441c1e25504038040080d00c210b42c030341d41904900001c126160f03c09409004810098203a0004101400c00140050b41c00141454180810492443c4020610a61005080d10703941c14030030382c0d0310f0049494131912182c039500620305100c01d100c0719855408a00300c065400c3c43c41c40b21a01858180f40d601e0510807200c01c07607503a0800c1c1030021a08ca5007050032100d085040110b00281c0b2607944c000c42081c1101c0948a00c00994100300a500d40305140810804148000d8407540c1003000200e044010b0340e00001d402000403125140444d1581e101c10061150464142c400c02034407031404a8849205940010380342c42500085812441c11400c8589480401014940b80041a400041c041c29140340c0c183c0600c400b220a0220002c05400c001b060721800c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 942965755 1250 942964505 942964513
    0xb2205030c06070804020a050f0d020909010f0f06360f0b0102011d07151101020c01020c15010f0918060606021c08010302030c1917070f08060708040602030c070b09 72
    0x20341d00501e0420010501c5080003180c0e001d001c050b85642c050070741940d400340c4500307481502400103d9005800010002d42260084041001c000d01c1940000c1140d001c041061112408600d00034042c0c1d90540100c046603143c0c00030b40c04079529200c0a0384850039002e4080500758071058056012298082200c2003015154007150300f00350390a05c035118403050740102c42040001d403440540d5031910580104403016800c40742030f0074424003031124401c544200030000e40d40c9400344000203010b9004bd0301801d07140d10800312138882141f0341101e090305841c100b1240700318036441d0440c214007a01780d550058071050303c0c0110410210b16140030f0700024083d01d4008022580700d5007001e900078220340244008202ea810b0040c0010303a004226100c0e95002103c0d400c9000500200544015200d81e201914075400d00b0200303401d072080811103000700c0320205403000c005070740e0300321240e120710044400d0b0000a203510000380000382c159018580040c5170007030050800038188d4900081141c03d94510700c10743c0c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 942967005 1250 942965755 942965767
    0x13081602130207050a02010f0e091626130303142403010603080313020604050307030c030309090608190c05030a06020d0510053a0b0a1109010c0b220503 67
    0x3461071000304200c1e00c0140841c644400382d12000d496080e0200d00a0410040503481091207200304039440e00c0700c5009100501d982824400b420740340a20050860204600c218949403404940d8103050810014494054a07a641d00310102503007070800004800b819543c200c100c660880002d00148140c404070017000c00821040c46405c020303445034861510aa04002e014000070340a00706490300400040240c42080401d44001340c024045d5400840d01442644000800d002c00c2c0190101100c0c0607854003c0c45644a480b0b000030303203040d40115002507106e12480c51640302143e058072a1280100700d9818040d45a6002034204058594180c0708070307401040703201d4655510300c202d0f84c10803411884440d00c1407034035008c01c4c0c0310400b010216298081d50b80740f4410b02e81c1c3d10450050980a1030994000c0017086103072442c015202580c05582541c503050916001c0340105084418515058450001c450004c0d901c44a04450040207440c800c060744540c68050a02031f100b500c14148200003840c7c40346 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 942968255 1250 942967005 942967009
    0x91a0f10051c02010503040614040b01060e03060f0c0d1e020a021014040201110f0a2406031509050f0607020a030210020f03010311030312071e0203190813081602 71
    0x28041d4100d548991030b240000240b680826a4401c1030030b90a00b4140d40300d43d03ca0802000a100c0c66925118403462241003204002203060901d050750020346420a65a283c0e009140c0d68441c11620a41484486c0d800310745a659801c0160040c0c180016002c110500d030005004001e4100302410068640c01080f2880c0481e01031000329010201168100461640074654890208001d40064144001c0c108100403c02d02401070303c035000303141c0c021100c10b117099103404040d02c8111502c080b0b0f503402c1880c3d4410300000e10b0050b81d0480307800ca14158060b01c0c401c07840100420b6403e9040395070f4801c40d00201080e440a00060b4440e90403500030f0500b80e806814040d0074040d401041a51881c81040035140a000b05820740341500d801c4050039401085103800300b842c0d071154000e08180c0355000010003112680c400b41e01e41d22442c01076500c4211240e00700b4140ea5030f010f0302d455540142e192810360480c00e44905046075000c0c07003030082503280d20803d80303820729680c1c070816a818038074100800080940c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 942969505 1250 942968255 942968281
    0x2040f090c080c01123c022208060f041106130f0302090f10090b0103060b13090c031a19051203070303110319090c1e0f050301050702030a03091a0f 65
    0x31411280062204440c44482c00c0102400220302c081b04a200b1840c440300701c1c0401d850041c25030a110411950303460420600071300324100c10480c82031440ba83c038020814100c0032a083c2d0066015080c445004e444540d1084004035025461541151003030080d080c0c000c2210308007400804504080301101070640c0148000c0620050844208040030802e00c00c071001c002150004070b0b5181d01e400030384160b901004801500180e0700081011101103500d251111030301e208441200c1d01d03024100643c038946002a426a84034003442030307200808942c030394000e0034001254915204400b10388440729485600242c0900c5032044089160352003c1140010550940b141c90b00d01d00380720192a00754a01510280105006026100d0606031198805030800c008140d68a002d440703000303098a2001c06800003031400d095030344618100800a501c00003600d017418030942c0d00580300343d4013035460504540403c2c0c029003050482100d001c1c1e643d00e0000320032410941c2c0716018034035040030414a800d0112401c800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 942970755 1250 942969505 942969527
    0x1d1803040e01030506060d1208062403100501020d0504060822050a031107030b0c1e04060c0501150b090d1509082d030711280b0f1302040f090c080c01 66
    0x107291021f0300c0e48049490390003080c0001e00705242001032941c1d000046150100c6c8650280083c0c090840e580a074100104040c0d031040c0312442e6440209955240120ba075110848501008a0f0080106000c03040c8510100c82c0e1120310362042e9100d0341140440e8010810000c1e03400d59054000144260030103501600461007c1001001800c94034150384031044842005070040e80c000b180001c800803590f0350801001c0039006092517140d11594ac8140207807a1182d0803000700d801d54a4025030200c0d8401c880014000e0f183c4031401c0c50300384600d0f4028000c80c1960700d0000c1d030f034040740940070040d901240e002e0205c02c41c0c032810b10b49868501038040e081c143c10440c0500f2031860351070f41850445100801c10b03a580241180303415464164a0b100d03a03420f0080c1500c2d40703007000c410311301042c010b15444000311540510422405819948060001d41224401d071104000d100c140d001c41750151801e604076541c0414103c40c0003c50400964450030484c44a61040300f0a800a500003400c641c1c01040b8080 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 942972005 1250 942970755 942970759
    0x130c030804080a3807020a05010e0c04110309190f171c0c0206041e051c180f090915180302010501091a041d060a06080706091d1803040e0103050606 65
    0xb580480c40d001c0c41d994840743d1103500113014810400620051320800c5041a110380050003000300380101c1c00015215400c2c41c4200c0d0213241044180c07400250741c0b008991040550101410340040035031400044200002c01c2904d0100e0411083d0001c1903000417042e1f0000560407a6030fa86128009411510701c0411311914030f428607200051030709980120341c00e64003070f920030305500c4030710250002007120041280d0054400d100c0c010100642c401000f24080403210716495590258101c088119001c24080c0140b6281302c0c410b00d010802e442281d044071560034464088240704502c400999802c66500c0c00e200304450068151080601d602172003080c0c0074000c42c420034006a814401c1554044030420640d078040c0b0354030001c3d0345055803503070955800c480941e000da554a00746400300c82c01a100500a100070390040b0f05001401c107014115a4007102d100201190100703030560040b109000b802080004c0c03900d016548445003007014402003028007980c0100192650550a016241c9200140054 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 942973255 1250 942972005 942972053
    0x7030f05010b0a0e03120705010b040b0a06020307060225050a0b0a1a0d02030106050303130f06090501120b040b1906120608070b370f1403130c030804080a 68
    0x84490402c1c00201e509240a6041a0404a240401191402d0641d0030280c1100340085401001c100042d0010030390b0340c4040341d00740400b4084004004200d121481410050381c4100621800030303440744c02420043c00752045001c0340103c0100e0f024001c80c4032150403140c9820288540007003007080310007150814140101004400c51842c0d0f85011039110700c402d68841c45042c90780c0c030215034094200e82c000c3c0001500b0b0fa03403101c0d041120500f2100c20b900410505544850000c9001d078030450a06040702ca0587d24100f1010000e040400185209450190095251084540103403901602c011100c80710450110080b4509013000b4811150480c00c0400581044000c018600f0b00003032003000e54900a00e07259490312040c803411080c0e1070382800c04220b06a00c0d04107007094088040004205200364446030400d90f070080c401c45001500c905030a541074014000709107444e0310b508a20408a219150905c2010384a403142c4170560003c0d030203441c056000340d0004d4108805c425940b403810a23074100c10 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 942974505 1250 942973255 942973259
    0x1018180f0b1507060e03070623060d140c0a030311120304050c0f03160f0302182517010902031f2d0302040c0903020319170307050714010507030f0501 66
    0x15112034011031112242c00781c08140c810a01c00b1541c40491039400220407650380c0c4843d4030b492009004e03851103054201e0b002848c0140e00c402c5c02480c9038800c0074000c1c2142e0450006a4807600c00d001c80d65070003036661040343c400b951140c40e99644000078501903160401c010704500340c10781c40e041001c440c2c11190901401070100042000030b221210300c1d000c0300d1649a07003045401103460300341c3e00c21410741070100f03000c00051007240141600c0e00f0380c7c0c000d4441051642906441d20384c4404181c0d8a82d49514086018a110f5943c0000d03150003000350b858515080c920307039004844404001e81003034600e80d40c000b00344100c0d40c9a00742c0449401001c0d032030a0040500e429a042d42d104a0a4018914090000c000d00201802881d50030301a40e0f0040c8100700044008034018a590b100380001c90103486024181c1500081c00d08802c6105c9600080011605d00100701c0d144503508081e0104c02804810b04c9504000780160703215075a032800c030100000760b510740024000c061700c5010003803424040c40c00c001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 942975755 1250 942974505 942974509
    0x50301210f200a060c0c05040908120a1e060308030f07020f01020a05090a0509090a1b2310030b131e020a0233010501081b0c0c01080a02040803091018180f0b 69
    0x206d01c040b50001c440024a00c07159007802c1d6100d10813601c180c5030401c2c0e88800c002a4407011b9011031103c80b4480c0c6550300d00341307035210140c00f141e00710b0002500049041c40020b449100000f80e1903400b0708644182c40301014020392450036030300000381110218801040d11001402c0258685000349400c50300c045990503c40755054030b40300c10a0010b0075001001c0009143c4004100c40e4000a00f40304102050b13203102031403549104281d1b442d41d1403151095085d0238018074480e009000e6035400003002000910031910301540280060740381102c2e0400c103218235058030784d860303c00351108a016801420440a442c00d0f500c0603082e0741440080c6429406c03000310441140c0564440c1034030b00178227129034a83c4512180300300c25030384103803441e4000400003100104030301c010904907404c01007070321140025210403000406030302560080c2a5035600034844510580b17130400092014036003070300700191a02c00e03204502c0d5100e9a1034000c190f911550802180c0c4621051180d44035501801c0303802c0141942201c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 942977005 1250 942975755 942975773
    0x3012403020306061f050a090e01030c0801380d06020f0a020d0f0806040c0203070f060b01020714150a110d020c0906010c02010c0b0915010e01060f050301210f200a060c 74
    0x8420003030045640000c5c6406048444050303c481c0c0c200b409c056a50b46012900f200340c5018410392542850780d02900359940320703501c5e222441d070441e1a4400000e00c4001c804120214108946d010345201181404280a4801403045030081c0000c3c0d0303610100e40074040d18001a0451503030800c41c3d03240080300040d07804007010360000701c1150041a070900d800c1007245140200c10002d0940d110039070200741009015031142540b02000e07005d5454140e52a51110981c2424107203094202110424202050b22410028842d0403041e05000198001a100b11854482c01d81c9540c409640410180e0b21b80d803824101d500d9001c4000d1910002c00340c7c10358002002038076545e800500040c0e4030380110701d94600510a26100603034a40107400b896a44551a0b144042c4c28418900403681c421007149050307128000326410f80f590310b030500400c2500c12490810300010000709803181e02c42d81112100003000c1c901000a840c0c4042c04690744803113100c08000303610701c0e941d0000f420b001d020180c0c440001d120302c0c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 942978255 1250 942977005 942977059
    0x106021209060d061e06021b0307140d080a0305071d0d17160b1005010c08121005060309010504020f030d0c02060904020d1113080712110301240302030606 68
    0x7481d1580c555024010fa4030150583e50444900201140c4a409400891181c5402107400740e0303003180c11030f0303008008414074a400320071842d4042d00012014031000440c101e902681002c0a07019100c5400c19803507140054000010400010351284203001074181d20282c0140d0010300780f00a20b880c1180030000039001d0041e54070042107080501141714400c400c00040d9080c0c00711100101c00302450a1030841102502140e210890200481011465520401c80f440b441d561140f9124a010702c51503640e400030380014240086078560707420104007519042c001d580501e6170700d0004219810140304011b400311405189030f00070303803245810005655012000100654050784c140e039540f203003000494040e2080400314a800c41c00c1c14031410a28400da8010400201184c500e01907182d00c5400960325070123148a0030461940c024580d00124030000303480d0105001c001c0c00090785d42c0016550700310203005400c5201d00640c45920420a60805018160380500e007101c40c8204100101c900030f820070854 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 942979505 1250 942978255 942978259
    0x14070b0a05040e0403170c0705010513052104080a0b09010b030a0210050d090f0309050102240f06010512090106061b02130209190803030a0c0e010c06050c09060309150106021209 78
    0x24004070b011305005581c1b83e4520700d5440d00040d903620f1300054040050b403040500315019840e01c00007a1070b000b03047c40f000e410381e54414040c120580c2ca01e41c0002d008640c5600007031000300c04010003d0743d13840402500450620a03058246245018412982114400100c0c14083c0d001506103500580c0c4035010f07803450124900b00303079841d8110700a00704000c1540caa0010a01a9521610b00c18190481c6424003110800d90031640c1701c0703031244004144040c000c021580b000c0106170100f2070880301d42e030354190f00141c185496070070315411911400404e0001e4070b44440695407640148461507000c0b004816564920200307006100c0c056010526800f0022805a007035031303000c02c0510050b507940d003403e0380300030209600c0c0e1520b82c0c41d00e213515101e40c41610758460140c64440a11b02203402020903002e00a8161290303d501ca199072560006004010142079246500f084200d1080d940c1a01035800781019034004c101901160202207101714068100805651110302c0408078a9041e80c22541c1c00001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 942980755 1250 942979505 942979529
    0x30709061206090e060405010b010c0b04021509030d1e14041404110309100b0a03050606100504170f100b13020c010b04021b01050114011205130f14070b0a0504 70
    0x10780302610014600c60308920f20300c60030701d085060881400114180503034000c1000b046001c202c40010b48201c01c0e5003500820758a00e000018026103807000b510703a014406403400300d14080048000a092446a03840e4001048201002c0c02002101124044403c2d1440c1048030781d9024039480c040c2039000710310468415402085078044252a240c10520240c00c20b400120707141c0c180720031070a458520300c4100800c100c1c40c00390140c2162402205590031a0740020180041c1e403140000d20000c000a81c500306c050200400c000581d001003840c00006140b142005001000c0d6502d81c00c40c106421034500302ca9041c1858580d024964641485440b9800348150051740e60100c281c00502405e100d005155219101007050b152018814282d00406104000200944d07a221205c0404800321a00e40ca80014660f0440d2494000980e00064206400c02d2144071608010340d0703000680070105401304c80d851039283c240008440704005001c0a010a5045c46080801c000002040c078002c03031207940c000d410 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 942982005 1250 942980755 942980777
    0x1003020904050c030f0304060f03020f0702061303020901081b0a08120a11030a0305060f100e0609150304060902030f01090f0221010903020102090312090f0f4203070906 74
    0x10b081002e480040009819100103e00800040c0d4994100c0d108800c00b1400c1d882c10300e01c0d024401c1c4222011007104c28401410700e2003540a00400c0d0b00010207500036901c1006021000d6612880c460b4001c14404000780350040700c2840850200100000715405440310a000740610382c80410010080b280100c81661141e201d03607402c941811203481c03162043d00002030040c3d10181e0540245200d240250345000180a282040c4113680352820004000603425001c0d20601c2d161100003856400401800804021400101030702542d04c160340840d0020b50700d0314400c086007814401d00c1c2d15420000020400c000039516907050000c0002c10080c86a071045808001c40e46502a001d407183c010a802040f229119140181c002c0d0701841d041403180c1b06003c58184135241050450f54200006010081e140030802c0600a204a00b0001560f000d00c003615034034490101d4444000e0607001281e40902000c6644040c0c3c20290310340c60500180d00741c104200300c0450341250161003228068a00000d5000b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 942983255 1250 942982005 942982013
    0x2060a05071b15170403080114010903020a0b1e070309031211060f06013905210904060603180f022101050435070206040e090f0f01051003020904 64
    0x55904440c2c01e101002c4007001c108688180740c40190740b042602d031403029081c1d240c6500c801c000225401070020704403400511108000c1c1022021010060401d80701c2c2c0b03516540007901c082d000360024030120700b0201c0c0c01b407240d40544e490000c40c0203482080518015541c2c0707000703149450501010340584c0182e82c2c5000400e00c03552007001c00e03e90140070b8039810f013814521540925001e071007190005002c900c110f16114820304015034425842c20741102da100234280444040100303020284c1e0103004025922441d1240040841c2e5040c4c140700c9035071750b47c2c0c10080401040311b0198009108151420115102c0307020300304007003990f06410819901c0729083da4070008020a21102d0203440e10f1481c03011008404405401c12409075210750b44000d0403140c5100c00709821044e0132141107c01c00b00c480d1000e43d05880400074403042e8009081c0034a040c0d26540d42ca2459035080e1505490f5921007100c4c002c4400f81071003a03d80380300c480030003441182000c0c0340380740b160032642c0006480b404034000030130104 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 942984505 1250 942983255 942983273
    0x705070201170615120601110d2f0f0d12090b0106030203130c060e040b09060a17010f021b3c01020705160e0907030209010b0306130908041d0402060a0507 68
    0x101802444c0715540e1003031203d845003004410390f2443d0101c0c010800302c0446000c041500e140c4100e8503900c000031850007540341190b51080d903240c0c02c2c0403070030406880e01c503e80c00e001034001c0209840c0180709051500c41d000306004682449280d040749010100c500240d82885da481c11124640f6016880f61590200031219041990300145103880a05001401d141c20902c14070041e0b0007100c1c10000d0b10014000e2041c010421120f4580c084400303a024488a580d1031403900b8091441c031b00015501c55520184400c91344640116070039107801e0301d02100140d00400455170303c45003400c500d0040301710008400c80810203020710341090000f0300320321303203c165002d6041d2694103400c081110441420200360000c4001c1a014024100c00c9100008500e141d0000341c0f901100e5025106166903840e1a21100898002a1100350300c641000b0b0f060044407070b5400b8091030180a42e010a50311494a809884440140b59044084c0c100036020440565103c1c400d4500d50388083c24055914400341c603200c030745 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 942985611 1106 942984505 942984529
    0x1809020604060c26040e0108010e12090402070b010b09030105070206010e04081602030a03020709061509030b060307050a09090201020d050315040b0111101407050702011706 76
    0x1405109101c000c2e2100c3c00744d48a4070720100c2144010750100102080c2c44498a80401d0621151039800070b00c2c2d005107913030340013007009010654102d40c0300da51040d050306045001140840003606d5980417148101e50108840d02c296840e420f40d07442c6030b0024031142d07000f03618200c000f400c441e00001d0450b042c0e0300781006a420b56901c1f41e443c0d480d154051800d00a482c40041584001600c00300079000e2400d01c00c1e00034018107820045083c003159115481b10781e04601400701c55800300e8018a403201a00e40029100d80d1a99840b004a840c1c92000d40c0452303040706040000040c1501c4942c0140210342c400d07400d803010106202000c07111400203036495106440c061900b202940f40c140c0c032103e240c43c01818140c07070301c1d00000d000034100029080442030301602e5102409541c402102081c0d440215801e1850614200e070300020071440042d00034101205041000c2041690b4060650700 = true := by decide +kernel

theorem cover : BRFrame.Cov 942805755 942985611 := by
  have h0 := BRFrame.cov_init 942805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 942805755 ≤ n) (h2 : n < 942985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
