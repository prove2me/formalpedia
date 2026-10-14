-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0977
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:36:51.44898+00:00
-- url     : https://prove2.me/submissions/74bd55ea-fe4e-4c87-8f33-5693845cc2ea

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 175539568 ≤ n < 175719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 175540818 1250 175539568 175539571
    0x4060906022407050706090b060a0603060f0b090d080c0105010510050703020a030809010608011d0111030705120915070201020c06010501080c040b07061517010b010206100506130302100203070218070206 89
    0x71103008482910f43d400181c48a104130b8101804880c1040e6001040c8140c00520301d0282c5001e80740c112031580c2c1c0c1e01c012412903c450091082805501d0020002a217061005d400b001c0001002c81c00804016a101621036100840f01040c69446100401075881c1c18405110b51035124203150380b50080b079030b0b8000d40b40c4201080040c20300c000036012420b4041c096000e4406051072200070030074408001440308070006a002c0307209696007001c10840c11503601718207580c05a40c043c0c071020b0401c622900c841d141c1120051074a000c910594a007070b41e8182c2400302240c0a03042a4000590328011440e24a0808070140c0286041c00140e409000841c880802110225101090b00b5a2111140c1c80d0500140c01c0d80715084c1c43d1030b1008200420100b08080d02512032034500c00c001c020b0568400010790f1281d5085800b0030881e41240420080e6081040007448580b40e4642d0100b0301540300c2d0300007620651521098030041e070002c14410214144125404100c0f0906030130007445160031513009540300c80 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 175542068 1250 175540818 175540873
    0x10204120f05190c09051e010621022a0f0601030c140f030d030b060c06090f0609060622090c0e060a052e0215130b07050315040203060a09050c0406090602 68
    0x3030b00c4000811180150103c404c0f0401071f0b51500c480f550359142e00500c00500200c42d08142c1d050b040b403120a00d000c600c200c8540341d961410090301071040070030301115107050381c203019040e00491040391a1110240195806540300e14007000b01141840b4a090441c4205461580103040034024a221b40d44c0000b140203050030356150120302d580340140030030000d00805411500c0f40c40b940c07041c08220180030030344c100e016001c18110fa6641d561010610fa603100c00303440090308520304011000c08805410b40d001010300703141c0c0000c01d05803c0ca503a810410304281e4010240b01c4c500340c042c40001e03e0000000c40017050112190114402020b581f40803c20324950f030400400050103e81d10028002c0c0108020000c1802020042f85403800b024100c014218a0464508040c0c0c000186400c1c003400680740512288400e260140c0403181c00d00009510113049580d000540c1c0700d000a0042090091510407032440c0b0182e81c82c0c83c5003000150100405420080c1950001e003001c1c85001c407101d80c41042c980 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 175543318 1250 175542068 175542071
    0x60a150b03071d010309051515060712030b010206041106071403030f0106140a08180705060a020102070c09060e0601110f030a090f120b0c181003020c0717070902030603010204120f05190c09 83
    0x1c440f8070703400c49e0555003841082c1d00448041051418020000c00f170200284e101c0e2418000d000d82440120303103034141220001c3c29203844030850035050400380060302035644150b021198094010314018595017086416420400e0880018070500d41c2c0501107181136140301a10f2818410990005803441000610311010302820780c0307400001d10020000c0c80000e10f8050030082e50b0b0311020350020302035801010300b503036015840c60000501140ca4410344048a0301c4850503000b54070383c000115401c050726642c5007194802c040c10340203603c80c01c1c0006c00185815031030b0050100e141464003982c1070740359400319500b10358020034440400d5041043c60740c4031a0f2030308400e9540512003c181c0302c5542c041c44098010303400c403040110058040d4018843d0ac10514203d400c80d07580c0750030319240841d449198002503000441c04201c0d0b48440e4000d96005100100054213140d01c9141005035401002c03019254040314808140a0140c140603209001c4024001c900281205486803581ca1400348198500309 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 175544568 1250 175543318 175543321
    0x8060402122103040501091403120105100507080310030c1706090106050102060c0c0102070515040516050f010309030c0b04030f0f0212040308071a0901200c060a150b03071d0103090515 81
    0x6001e5010032406a8000d88e403400b10300c0c0214419599410019103540700c0000100041468908140d025000302c28541d1960714140040d6101c079400c3d08082c2158445000c0400c002c0001b8110010500242014601c48801c81008004091a21101419a06003a4942101845070b664003040c2c40793700c10328958600e03580c1c0d080349486900900c9001c8001e809401072007000c140004020310118003541c0108212041006c500003c0030945a031441007070b6000c54051000300807940640c2000c02454007a08103080d20400684030f0f00341e0480c0864003100003d203160b11407481c0940040040100b40361602c011b14480d0300015844089204a00001c1c01403e80410700c2d00400c1070b80180c1c03504c00001c1086980c2542000c0b0250340c041c240c540d40c0c410354a01c0904144044000010940d9240c14042000f0302d401d44030005010020800e102104203800e06a91022031110090030055002c0e074550364460524011003d442d20710244c00702441810981000d00700c20204100251f521241e18010b4503103000c6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 175545818 1250 175544568 175544573
    0xe011a06040524070c08011b05090102150c0906040b07050105091207060f0209061809070f090e0901021204120201180f060b0103020d061707050d120f0c06060806040212210304 77
    0x984c002e0041c001e0605209140100f032280040d0885a0300e464031904040740102c00c050203440a0140007003c03401684842404804010402d0300503800088000d1b4407460642e1100100740e840d03020340c1002d20341e0b10001403100308000d424400c46030721800603c0a800d01e201080030443e180d100324400989200c1e15007203580c0c5a04110350450b4000300000b011340740d40310002d50102141002e40c5202c0c0f40704040010000d032081d4001d50402c2ca441c0d54641d1380c000001d0a02413076461070b00014100404ea903509100074114440d084d4034441c051402150a074041424010009007500c01204134101c0c4170300c0c1500d001000404218203602515445007000c034803e404140100c4c000e002d008000c140c00c41c205940003c20105040000751081d00c2c0c4025100004c4d204c00030300c000780101220040c429035840184840281c4110401e103000b140928140c0300f042846d458200a4440582104000381c004a00340001c51a259200c0090000200e001e00000c0ba011684045030042801d102c620b40d40002001404 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 175547068 1250 175545818 175545889
    0x10020a0e0a031101020f01020301081e030904110304051002090f01050903160f0e061c1b0306230f0412030b010e060f09090109020711040906020d0e011a060405 70
    0xc1140018108040702030b5a424166848482c0e01440c80c050701035002544030115044c000c99050310b0422000740030042c0300314070081c161401d14180c8151030000307015007803841d17442c3e009500f60820290704c0c01e600da0038142491410010a400340050143c81080aa15603403aa0b10700ca003061a02400d03c1a210b00440000c80d00308002d03810400706e103800034000803944405500048064490a64020110359550401c0c0880560300c20150034044035410b0f14180002c50725082000300c6980380300b01890700c40e925990003040c0c0704048031000c00b00402010050702c40c050055030f182d1206004650302361a081a032581d0b60103034141340c11281010780707800c0880e02d40c0c8d000d00c03084403604502510b43c1d540c2d20041b00d15524580c01c5120703040d03c074000c440000500f05610f4002d9501e00c5820100071140080e1010410005240b203220450714a40c080c48420151240d5105869030780011400119608102180d80030082c0c4481840d24410403080c082807142d80c031041711401884850400103c060140c4400500 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 175548318 1250 175547068 175547087
    0x1306051606090b0a0c09080a02090408160503270108010e0604021209010204060e03060c0a200a0308010e060406080c090c1201031113020424110312100909020310020a 73
    0x305002c2c10200382c90104002e40352914403c80c482c440401407a5001c4504642c3c0324960712880e0220383c0070040c2d20340549801c8440582152083c0d00803482c2580d0300103051400118050b040e01c00b030b0400b02d10820700b0003401216954000409140030091480344001801c121418002e4600c1800c0303000002d10b0f0b94540d40d044a60498004602901c545060003000d1702179402070054200007514666110428140002d036030340aa044018a02d04001c1d90a41c119034028000c0702900c001c00700001c0d264a06d200070300400000034000e40d0380140a40c18100b00981054003c0c19070342c090b80c81e00303004108a103070100e150781036908210340c0c844190b100c0035507143c0c0e03900484a6094010b28004000001c0000300c91030858004802ea070041070035012003210342d08034000c9100e0802e604401d200030000010061500c0180c001c15828500d103101c1c0c000326020f1458000700c00109080402d5002e004890f4507440040e00200014031082c4010444d82c0c1c00300f0f0302c03005504540007000b42c000c1240151f580c0a6850362 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 175549568 1250 175548318 175548323
    0x240e040605030a060905010b010207080d03091a04030f0801053703080f0319052205070b0307020313081c050a030902060f0418090b0610090b0c060105100513060516 72
    0x54031080f07030b43c0c242280208201a812909036180c1078180300309500100d001012500c0a501a142c801039840042c0c0180611540454914103c480e136000c42c0e001451003103006600a07034030400046e0342c0d89005060168180c10280c898284008040789000100080c0f0705141c2405001d01c200b00302010700b100c0710305d1054000500b2404041072102c681010b50317018522032041c0c0c43c0d0700c40504d01000c40d01c1088440c20b80b609000b03543c004001310038120003d59510801c512560172112179969602158606400036240c00c8010f800000c0e900c03c00c08040d203c1140505030000182c1107000807944102502602c0400324018020007040d171101c1c0b00d000741d0040c411a50080d11156845103030882d8000968480c0c09213140300341c0002c0441c20144114400d408a00d50f0000c03400d05036460b48410000105011300e00b403030820428440c08102e40744524064800da400c10b40090040e54100343c20880f010150b288640d08000c024803a400040d0603605554046601c1b41c240660703900f150150541c030341c070700c1084013 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 175550818 1250 175549568 175549573
    0xe040f09020a350102090102061b030112110d080408071410032c060708011d04150e030c07051c050d03020a2d11190b090106080d09030507240e04060503 67
    0x1100f06112042d002410103110981c261440b40d42ca481903800c0300c8084414005940d0014001404600031180000784194011a9a0001100e50703c0000b00030800e55681100c82c2140410b082146540801c1a2009003140742215488029041c000c05c0fa80c07410f2075104010142c4030383c000d180110906c1d100420510000140300000d0251158140e03554106840d90000107031110f00005400c1001c203000707420310322201c4140c501c940300c40c2c03038409600056480b0300c590346079a0808100c0d494001c0000303041820300c12000c3d20700107143c1010400c1c0f200d0030400001907060503002c6400021404910403907407400a080044c0c440400ca08121401c0701045204c0f102c00d196403444116002601440e00558001740c0d0354080c000d801b804501e512068640480004018170082030380016020b042d4003941f10380c201c000020020341da00c05881c0360021302140103010070048001801072010500c1350202034400917014500b142c00903c0010306016004031b01c4801c015428000c140190340e29001000205402000c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 175552068 1250 175550818 175550909
    0x20d02030a0c031208160809070f0909050c03060603060403030926090307090b1503190903050a022a0f04110a09090b04050603150405030909070e040f09020a 69
    0x902c407607903000340d02040c1c403a001c800d07150341c2d00c0c00c0c071030350700248101c00240b4081c41d0f5078031203082919034400140c000c64081c040c118003c2002c40018841e58010010030f8004501c50415080041c00c2c0751034020f80a0007a088041008042d80380080c280703822a50624002684140d42d00b020241d64030075290803503020715480b01c20001c2c4002d681c054402c90b44200e0540b61519950700f284400c0380d0580660326084900c1e09507465020074071b0380c0a998400c064440f800c014880c00c0400300121001c502c805c5010502c0401c11861003a810441c0c6100300070798003501d0341c500075a000c4404c01407203070580440c400e5040d640784540c140c5680e00300400310150b07002d002e46c03241030602015010b0307402c9018481342d29240920560f510700c0c00c1c3c0034aa004180c0070b03000c0c01e81815401d0441b01d543c84014000c1e251803104121a9040e61034402030540300e00020398800f92511031500822058940d1000a5851075003044940c5016a0300c03020b2800840d6052140c0030201d400c44e100e041080b4003004050303460500d0100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 175553318 1250 175552068 175552073
    0xc01090315020c0312060405090f06070f030b060c071d09030d050903130807052e08100b040605030601080c030411090601020c09010b03060306090712030302090114160b090c0603060409020d02030a 86
    0x45041b400b84804982c10300c21560344044440d0f4070941103403074082c260701420102d28000d016604402800d182458046507a81e85080414071540c461101001c9030b42c45100304100f0b100c0d40307024041005071111054040340c00c0500140c0d50700e002d203104500e182540c0d640800c0d2514020000c9520143d8000d40e0301e01c509940307544454071040d261141b41d0060030803d03c080b50441440e02c443e8440880001d00d042d20000384401258040300042650725240640c040108001140b0806407004000d42e655040e50307854000d00040c2510f0300a889180c40c040c0a2040c0130008a101c02c1c0f5a040c00016900c008086c0c1e51400100d190005920846070814034400c0041110b588070710095100e98801c0e001c550180e101c0540243c0e54804602c03030325031212804204140064402e070002e1403601c3c0145000741c003654100241490a600c81404060b01100c46c203070140c108150175030314503400003c040c05000c40d80c3e440300c0401e016100040402e4402c0742c0e110a080d0455560003281100e050b0042d08440d0f00040c41e1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 175554568 1250 175553318 175553347
    0x5040b010602010c0e0d0b04020d02060f09100306030201050711220603060b0109420206060109060f0e06160807050d0914061b070b030703060e090c01090315020c03 72
    0xc0c0503007070040d420300c403101442c03a0045204401d00e200103010503000d01c403142c80d030062126014001302d03032010580460401690f03c24002d000c45030040c0c2c0004d0f540d180080104034050103401c00d14810706090180c200b0150380c019054418182d000611842c241a800c0002141c0c51401003880f00084003181039614821b6140d03221340140c0f40b14010821000d0300c3d5100540d10410648108650820480f0001349a040c01c0b0340f500302d0b0040c00301c4104014150b5606440c80a03061480e020740103038001401c1110560b80504114001c12060400391921078000d900204881c2e40c86414600942001a201d40703910000341c000240180c10150050f225070f11464416150603580b075450300000c19681d008a5101601120074210080c000e1215260080b0290503442041c0031052442131400303a0031000071480c1e00d00008510401e80380d940010400d081c1480546018400340113407109501c8003203c400d1a903003118280c2c0c294ae030414103a2400304000d0304164081d1040c2c624058080c000880d40d0304d24044407 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 175555818 1250 175554568 175554571
    0x60201020c0c041808071e030309020102060a050108120901020a0c080703150c02060114030a17130902090d02040e031608090915130b01090e010f03060b090408190306050405040b 78
    0x600503912102d403030354204030a030f6000c0e481000c0c25002c3c0d124040001218000201607040c401c140007801c041c440c130040104914807200944c082602c603140c0108541c0d040c8542c0b81e2000100400300115414114241d43d608a2080302c1c41907601d00040c01c50a603802000b60f02c1050f0342c009420b08612740c60f00f00054071103d00d03200844d400a5814030003000c0880d58064035110180d682c0c01800c01d03a00c0c0c590b6812204d140ba0b8072198140c0074001c41000401d04440000c4030400510070322594514201c6440c484002859000c3c0c0401c0d441448a9811a43c070000740d0b241c51601101e0101d241051f41c0d41c4c2d00d0552040e5400b4a4000040d5984c01e4100454040a050174080807600c0070b43c10f50391485080c070350000754035866030f1012039141032500e5440790b54003064242c001071400181480d2920310044400c1030a801c565075030681040c0400030030900c0d01502414800a4800f45030744d04040d44c0326480d6004900c91010603420b90095014100d00c130358031500041074010b0051005007400e0901040c40d000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 175557068 1250 175555818 175555837
    0x4110c030d0e0c010c050d0e06040929011d0d0602040f15020106090509060f0405010605060406030b100e0d0303051b040303030c0807020303190b06042c07020705011d01140406020102 80
    0x100700f103c0400707600400025002540080180c82c244140c2441140c15162011850341d0221061001044c15071030351003001c40036440c0344030411405000100701039142941c0035406040103889030b01141450300080c2c031012400310540d11a05180c500c0c0c603145d00030380101d80040e0750701d829070100040e1490000401c1d18049200d40c008011682d1150b46020660b40c0482d00a5419030040020a400ca01d8029240d5807040c000e0000250361074580c40002c0e00c0760300c181e00c41d100280d01d51031103032010700d0a00c00c1e00703000c03000c0f50074404082441c09010500381824a14040c2c20315560743c00084100e03e075910a100008001440fa6560b95101e14014000300001e82c0400000381c0316200241c02140004112401000801c14004400d00c00d480f16030007408084132120341100e010b01000400741d505a0341c841d000240381e0130303000310340e611120000034a00005081c401150f00c0307914200400c0e600711034400d2080020701c00b0041e002e450180181c400c1d07603521040780e00308500000e0020703001c3d60640c044d008038031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 175558318 1250 175557068 175557073
    0x705090604020927010605210603150115120905070501080a09020405010e09060a0c05041203050405040612021503430518030c060904090201170a05150909070504110c030d0e 76
    0xf600d540c6c044030302d8040c0304d205000e295100403000d1000b10310040d6050380100f00030100c4000d1001408003480d8107601307038007101900c038400229100d5141c02503004980642c00d2442000341003140d8840c140c0d00d2119100702410f01400c240411191201078200600340c6030003800c01d200550303403080b0081031501d0480b00c8850034098807000c507071148074501840b88030342542d9a41500b86800d0a0800807147d00c0e607102101413103401c000000d2242c4030b0b405601c008042000403000010024014025825440f405e040360f0800d04100704181800400294009810943d026000359019101a8a004821a940160401c64012142900c0c542c80030041640c4e09580740880c1c20944c0b001d05044d901c80c184580c2945c0300006000e0b600980c10b00e5842500d1031801450200702c00900207440390255a030560390321041e26241c0d001c01015000160a98070072420560316121079103015003e1030780301c505600800b8461502d601c02103409501c20ba00b55001010aa82540d60320203000d401c03900140181c0d2002680b90 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 175559568 1250 175558318 175558321
    0x30f110d020d1d0916051e03040204110f04090f2a0e03070f09020708090a090603030e0d08031f090f1406100f050919080a051005090705090604020927 66
    0x1440c0d03a041c094040380d0f01805a40d059124088042032101e0703100a4035041010501c0081c45510b12a08100007101041e0040e036a01c0c21b05005020659010802c2c1044404003006401414400c603800c903811a00281b00001e01d207004440a90094a00003060343e002a51042c10b1400100400311110038a2166458900040809105158880d0a50b07c41c642924130302c00820003a2646903001016402d02c104e60b043e2074016040f0001c1e28423040b40e0440b20300c0c556115014000c0641107a4039600c8180203c0d000200d100c0c10b981d40c8070040c40300074000c84000c00b08060a11111440e00c68140240030740813014000d510141042c10010440b461074042e6805408000c21454140742800701c00c3c1d40010750f6098001c540c5441c00365403039070003045119040742d640440c0c0c0c1009500c070144d2601400354080034043c06404c030708040e441c10301420440c45102d03241200f4042c00040010b803045c204c84007660842243d03030345c03200010003c3c012100c0003a00803c1c0c415001d8081403440e40340c403011410046259a0b603 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 175560818 1250 175559568 175559597
    0x803030f091c0e04140709080609062e030b070e0a0e01080a02120c060706091b080d1116030b0106110309030a060e0f070608010503010e031303030f110d020d 69
    0x102c11801c9100c031800c8105491038030060384191408001c201c005400440c07040058442c591440c0d004541000c002815160144502d0206101c2c003030b0080c140d180101f002c0d05259042c2290700c0c0400007d000b2038040b00d0b48030103c004803103160100541d082201c0e41050f14055001920302c060180c0c0451007400c0307401010814055200e071060580e12010000c1c664803035503030300344000801c6a890410f10340c451001c0201490351002c000f04509841540041050b0f100c514000130405480309242a048007008001e103c82a400241d00808040a16041401213515030545052801d08400b885000b54003010200034810203c01c59412076200b6584c0501240d05000e03c59142e003b4131503d554550800344181001c80c0e002d41027244c80c01400000c2d100701c440d040100500c1d000c02584050042a503038001000280780070300c241d030320380c0b400407005d18505070071040e07854100c0b040360200405001d50b035044c00034130610965440c04c0890000d0203d0306003100e5000e0107940c80340b02c0103521000030303489510080e4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 175562068 1250 175560818 175560823
    0x2030709050d050c0906060705010504052b0c17090303040803040806090303100522050414010509070b310f030c0f032415031a060306040b070e040207060203010803030f09 75
    0x1441d81d0000061304070003900c80f080010084010700040d502080601c0364002050083c403c15004500c90750040070000300d0061000c6100b40040102049040203101417569183c0000150460503400300d440d44001d11b00013980c0100f8040d5100c4190184404100421014400801441500c61500c12180e440e610314818964a1104503081e6640d40800c100800c0780303081581c3d1040340311100c412030449000e4408070680480c0c0301103409031044a01d01000740b200c0d901c03c1c0318613a003020030030303019044a42c20408070010754030400900c6a4040f00f00080a00d040fa640c9800c40740e0748015828044159a682d400e140d07030b94034903001c02c2d41c80040c041740010b5201c1a0024000440307070311280010342c5203017020483d40c01c1700b900216104440c4d210300c8503600800b8090202c001030340c428492134400c0781140010700717541d10008000c640264001001d2002191401c815039a000d0080e180004d2058000d80214020b800b848100070900c0740044000b00b84504088081c42c8240050341102100e540e8035618903a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 175563318 1250 175562068 175562089
    0x804050321091605010207031202010209040c170c0309121e040e01081203010321120e0d1b031b03050910030b0123030a091110020109030f031b051b010f0203070905 72
    0x2405680000e90800008200c407440c80c5050f03492b07000047c1000380420210301610700340001c6900040105d60044000c82c1c0c04052990441035007480141585402c0c500c90f503031290621070404060384003007580900300b039499011300c0640c000c0910080d1290354078201d07004061800c0c0107001a5002c0c411505000050303c2090300e040300c1d00030003480040c0b030415000b51038691100b41c15104002e1f0000c401808a140c6011341000710000d0001411800b4440c00e0050000c88445070f6030022032100c00e06030002c240d0215851900c0c0001070300b0b240b08d48603035184c1980d0328031480400a42207681000b69502054059004684a4000383c035a0b030758061003402500c0c4170181c1c1d01d80d201d41101003480400c05e5202503a0003d80102d20400110b41c8510a42000805100b40d622a400040c0e4403100f61108150380004204a07184650400344031030100310101c002d45201c000144810000c01095003088018198112054480d00100800c41001c854400d040070354011984040881c54036040012103080a44812 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 175564568 1250 175563318 175563329
    0x27040e06060a060206130f05010e011a040608011514131e0b03030310030308060303040305011401080c060f070f030c0212011a0a0810050403030908181503060d0308040503210916 78
    0x1802070b2034a0355074440da014807540303055443d90350301e03403500c0d10410f42433240c03000d0181d04281007880340d40e0391000c1105840458204078000e90604000c0281040c2c00508201550f80b96094064454580404224040102044000c056017082040ca00440404065805a008014040c41482050401c0c16507d20090b02d80840240f180801080800c1c880d40d9182d422580080039249030036070342d840f400d0a4800c040400103201804074010060103004110200c442c5000b40c3e8843c0c20841748107203003583d030f019614000d01244c00c902c428004061190044043d0030f580100941c0c104c2d000007040d20300a00304030409403007140c4148000715043c941284107004554074400184441c0f0505030070100502009001241450740307a0308101c0000701440060401c1d400c0000c0d002500308072150030441403d405010f2803d80031010002e0103043c0e2200c01c007910701c240d00341c104407017692140d00d000d5141d1b115050b2001144000d2640c0740c01500a4407810a00504158045400c0c05629200d00700400595105a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 175565818 1250 175564568 175564591
    0x90f1e02040c210b040e0a0302060906010e011802090d061d061f2315030a0f11030f040c0b0c0a0308060a0e01030b0703110307050a0f020a0827040e06060a060206 71
    0x1080d81880c2d0980013140e80060142c008100e0b8254004200e00d49050860201c0141e00144200322010004102e080d00600441c1c00a651070b516114000c84280e15481c00684c88980002d03d0804503280e019071018500e50005040061540c01c0d008440055050788200006010302c0b0b001c20083d0030f5a000b200710f4011a4502a610f0f6841d003600071602201041501414004946100f4200d81e110035017110004d0341404c14075030ba403900b00d6506045801c105034131f250042c540204100e00d101c038241a01d5012010540035003068481d0308004610044503440301445020000c1e0407001c03101e01180c00480f50740f29480c3c240e880d444007010004814018010359000c0c00e4044010808075031010131141d000b6400b4100050a1081503c2c1c03a0120760007241d074000403403c0050308a12495004248207100d441505c080c16500d1202c0c2e65000d03003445019801d902000e0081046400d0808100142070b12a000900800c1302031486181e181e2520012a06140314022800300014094004200a403050300140c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 175567068 1250 175565818 175565867
    0x10314160201091e030f02030319020a120c02030a1808100209060f040e010e060405190c09080102070f140304060e090c0903010e0619020903030d090f1e02040c 70
    0x21151110251160501190b4a6103001000704130900b03040901c1c2204001d0908520040d0b0a014005104200b0350f4011544200f0030066154004002c2200c408030300c0c1c1d005a0b0341d20f8241c1c001c840c5510711041115100b45001305c0c402d842500080100340710340c41e9441d05103c031030340c000590000c018144181c440581105440d5204441d0079401021500b9004201c2800e20742607070b1040c0511f42158022148698120300140000000700c10b02c2035000300121018820381c0b07000090600d018443d00b40d854000d2703494070341c5240401d000310b80b100058080c0a00854448849040100d01991501d1058840c2490f07112210403c65001c03040760103540b00d5480750b56800c0c0111051110303d01d1300816040d03a6000c1480078103e60b690a0090b21900008040245090708141c5e40c40003c11078001181100a80704005d004d01ca902c0100a44491400d50300e800510b03103400b03003011000100b240030700520701c951032914070710a401030302d1071251200d00941d02048031400348907095444080080d00100e00c03000c50103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 175568318 1250 175567068 175567081
    0x18050c04050705040e0103150b0609060904050709090f1a12030a0e04020409020a08041a011508040c170f0106320d080a020307020108060901060516050c1e010806010314 74
    0x104401c2c0c00440902d0841e20b010344c2c44d42c4072500c070078081e0801c0751048030440d500c5c1c00d0080309002e540b043d6841160158a8140440002507a0b4800c3c031000c603018580390400200618001c4a1500c001c0071604424032981e0b81e070b83c59090050601030700c0020042c0040e00e80c40b11909003007114081348551080154541320b04500d003500c65034024042103900640800c00071407103a8446c0041c203010035180c0c0710f52581d400c0c03510700065951048054101d05001d031074010001c7c03041e014003e030305d510b00e00d040186203601c0c0c60401c0c01c0440d41c01c0d041002020321110f800c94030004005900d00c207001040d0b000700b28640c1c503626a00345004500d0310700c5006800803185000040310000c024108414000c2c9240014480382c0d664030501d81100d0038190140e000880c005040d560002c01d900c0d880072044405010315810038002409a0103002100e0003c6d0240700300400400c002001035604601e802080c5085041c3d018040341c102c4281d004c82d55001840d01070120300554000d020b034141c88818000700010680d142e4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 175569568 1250 175568318 175568321
    0x812030403050307110a081b102a030e24070807020c0105160f030302030618010b04030b100e090705130c020607110a0618060b010908060f0403110607021018050c04 72
    0xe05d81d40c00035000e40d030110000228808020720022002c0c01000c0e010080300c402c2c1e24203003265000c1d070078040c5017002d100c0d0044204442d10031500b02e800b2034021001d0000c00e9000c50007889010545142c44c821140c44030004420f41403900b900b00003103190001141d0340c84a007203d90b940b00344c0303644001d40c0c4106d000c0c201b158018405403100540021706928603102684032500c003803034088016000300b54008140101070800c0c1c001450b08100c1c502d00603845516096031812680b0681c44041c01c00a07440c40802e443c41c0000c81408020300c0031021019440c18041d0070036843d0307543c0b842420f1013240610303101b00364003106004007960074200c0e0300941020f998480003613400c05840b0144009a01500152000098103171041c52200140744507080043c510314540702045a030054a2103040c400000000c0240c4003000401130780c881e244400f000301d681c03075500d000d82c3e500002e200030420600411040040d02640082c403040c009207225418401d0400c1d00142407600100c01070301400c650881f02074803013582000d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 175570818 1250 175569568 175569587
    0x102150403030506010507050d030605040e0d0207091a09010f050103290906240403020415080a080f071406060415140402030c0d0612050601050301050106121a09070302040812030403050307 83
    0x11b042041c030b80011681d0b01c1d420600400d68000200e0b68400e801d104a0800e807094052500300351307008002907401c060000c0e607a5004e82c460b0035409070701e9403000642d40d400980a6071a10390040c2480a01d940c40c0c91401d0880d09040c012140000e14001c140c601d4088141007005604103c94407124182804800340090340340c006113140d0304078012100b48604040001c640c0f003a0080300c0b0016540701c5045104000039a511014010385a90f8410000c0c006003601068140c0c96640c4180c0081c1e951002c00f00103406401248009065106403009012401c0004a0010b20400007184d0800c041c400303101e120704c1540f00c203016006402d503035411a041d050801da0b00464002641034946030410281e0440030b410303240399070424241100382c40030340002c21400300300d46805400110003c0c0030660400c90000c0c02c140d1021007c00a00d604e404440d69003880c5050380c1902d13040060120a41450603c070003070041e40c03191041f16154498542100322444042090300d01880e41917640b9442e5803034010044540840 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 175572068 1250 175570818 175570831
    0x403030f1406061b06091e030c0705010f12020301060c110915040207020a09050c04031b05030c0d0201050d0c09260318030f0a060507030506120a06053303060601021504030305 77
    0x110f5031310760305205600300103251081c58000020426210140401c1e500341c0788503081c10b02c480d4001d100c2c1001c043e0300407908005a50081c44c1181e0300601255007210078140c054018100d842c4000004500703940d0282d41845210700801203007694000450910010900460341d074290300d20202e0b40340c0c80a00c1d01d41c0007481114001403031459081d0302d0b09c440f031084a6040e07a4905182200250410400080e1161404002980c101c01d5406030b02e8140802e45504807000b445210307401c07000710f420458ac010750940e00d038030800110070840011007041c041c056010900612010060910403103504440055440e5000140d1101850405000204880f480804008a258540140c4072201c50201d001c20104481b01d00540d000300e500d0510003000307002c48001401c514014030948400e070800c0c0700c0000e020030f281c59100c3d0700080c4580d034080b0014851034a205150b030ba5004c403220346002801c1c1c05e41602d411600210162107c41d140c1d440160384da542405581000d00c0044800240401d0096008a50020 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 175573318 1250 175572068 175572097
    0x20a140a020c041e060b0d0c0203040602070608100b0d05040201120b150d020c0d030902130603030f0c0c09230106030c09032d060e060c2109070803120403030f140606 73
    0xc11503240c3c4e00a8a00707a0700114900d02c0041440c6c44081c665000d00702085055002561400d03041c080700a454806600626090050a20201d404c0c59181e8520300000d005c10480c454486017041281c10141c002074500340e00050812890484000062240000c40ca00c018035549140d400c02c942821150824103030000d201c1d07821b000c90510006c0900c54070300e402d502e40d0b50004442000c1c0c0b040261008902102a000a14142c4140002a00004010114120360612001d200740510300f0003140d00c40f070f800046030f03a81041c21030f2400b10100405900d24180110845440d41e80b00d00c0124102c88800c0201d00c0001c40f10882000424054041684940140c5858150034041a0b03004c01c5084510101220010354a9040c0e4203008014400e0702d400210000241e07140101a07420701d166042101e481c64144412540810900390702040104001d00703402c0d084d04d88803446c1004c05401001c048405a0210b03080000b81c040d0318256119000c1407940b00c43e0042419202e0b8000d020140d00940b0360384c3d9048 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 175574568 1250 175573318 175573361
    0x2181210060308040f08010212010902070f050d0c06060e0603070b0f0706060e1510020d11011808070b1315090201030b0a080606030c030111031b0708040306020a140a020c04 76
    0x4900071403010794015900d00742d850b868a0b03948007041707081d03138864511a40b040c002c1c1240048440c031400d044600d0180003503104c40c1a81031000411080d004002d0040c07007448010300300c064101e0f01d034555036030080318100429640e40054014aa9003200c0d45030303040d00002003d00c5416038200140442c1c54012481c103081030620f80d18a0200c0c0c4003508043c6c0500700d9041006540e004d0305050120b41001960f1340c4046148400300039540301c0c40d41c1c034100c00b03000d11200b0800c030758182580404d02122075600000c40c480c0070350900004680c1f1401c0150b0b014188000004d0614201c842c1640c650356010884500307a100a042200081c6800c41c0d08a04054031070403104078650b580c1507404042c0003408050001c1e401c2100405203842200c1280600a03410202241e684000d0841a660701c480300009400d208076481358450154400c1000040060602060120500c41d90380d01802807010705445400000420208042050246813038510042c1c1c0003603270400e45810b04d508141080d094460004a58 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 175575818 1250 175574568 175574593
    0x30c06050a02031501020c010e060904090b041101020d0f09052b0309050306010501170f060f060705030a030b010504080d120e010c030e0c09040203030d050601020a021309030e04021812 81
    0xa8460035102081c01640200510038a102442005208030f042400146102419040040c01484420103003a2283c1e0340480c5c6050b164945810103010b86500c4005040640342a1405148480c80c10300f20b02e0041c442d24088103c42401002d20880c00501034546a10789480d1400300704107030910f01616139003041910a0000340403882e0b841e082c00580f0030b444201225003001c0505144c0311050380700c241041080c0c1101c0040c220a5a0000d40051940d0707040c11003a510038010500304819140c0c1d03160001e80c0065080d00340900400034000000b001c1e50140a130040307100044419020ba4018054580c01c000140310b42617024482c40c046179100c2c800c000c291111103271105030845e01c00c0c80301500403949a5891028a51007840300384580002160b4003869400c043e00829540d00422442d59940395880e004942c0c268003c200350915150700403c0c404d4102120a1400e0203025100c43c00c41c0456202d154845152410380241e640007040440344800345c00d408002c1042c8480103200710056406031100f00c100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 175577068 1250 175575818 175575821
    0x3080a0207051612020405071d040b031606080108100603150207170f07060e030703020c0114071707050c010f050d1a03060106020f0613030f030f0212010806071103030906040f030c06 80
    0x5100d1076500d001344806500600c410b071000108140304110070b2038010040359030990750b035000d210401d440009983c442000800c0c03801e02a54000b800c1c0e64034035030340042c05aa00c50780c55030681d80c06405a5450103042d82c24442030f5000360000900c0c008034807602d6801e034800d540c0502a05400b5201e24208071840030b0000e1032650061012003241c090018100f0184603450092058030100741c4000e42c175084868030001d460790380c2100d003141002540f002c036141d84180c14080d034211580003c5550350305514a01001c0044d8405941110315020707272b01c40c442d51580918001030341e10705951501403510740300f00c00c00320062500d103504000300740c4540003080c595101004010301038240f540040486818650303620345803040040854001d5070000380e80c00000307940800e607181540c0c00340c00d020894074400e0b6030a00103405140783c10040080e0043c0000b601d171000144150259075507844030110a000d21f2100e036107a1000302d031058656400440483c00142201e0400d01d01140a443c3c07000309485c0d190313034210 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 175578318 1250 175577068 175577113
    0x20d020c01030b0d060f0c111c18240e0f0a0905130b1503060f0c0a0302031302031b011805031518030c0d0206010f061e051e030a0b030102040303080a020705 69
    0x2a1000d0b51001e100080239000100460901480002000320028410b1030440c012440817411007004000c102e8071500200300c031818070280c07030340784900400d841c10182c50351890502e04200c030303000480c3c1101300c4106050040040e80d220f4409400e00d5841e50600d0083c3c0701900c8003500700c01c8a82500003e01c03000c10307003035004a4040e0061071507450b40a407910041510308140500700000303041c2208280400d0b0018003007190400e0a042c04c0c00b507141d42c0d81e081a0140a000000040c1d0580100b88802005180c00203610340011402d0300c48801c0c0c0242c109040701d1840240c050310350154031030440b1812444000e000c0950111400364401c003444401420b0741d0850300101d40c2c041c2c503035002030214404903405022107405000d00f9415100080d00c3c1c01c01c0200385d07544040342651080702850300801d00f41c0c440c40031540c82164075084030b00e200017660640185540103e540f00b0070030380350208036440c0f4a018001c8071f088070703050790710b00b19107448074110342d00203611030001102c2a2003014a02c0611030359111100c3c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 175579568 1250 175578318 175578341
    0x31a100e09010f0b030f040501110714060714091507060905070602010b0402090901060309030e060f040501080612060417040806040f020103050f0601140a02010e060a020c0d020d020c01030b0d06 85
    0x5440c4001080500c0120328042e04040b8607800042c1d41030010035200070559a001400c854003031130b16180c0d4148140100300401c1456401400000c0b400188401c001140304a494030300b0803200386a5502c0d0b012540c0e501c0d541d100f103010440422001e40c80789400001315100301b50340740d41d007458144980d80340300851324003540440312500515410040f064081c894503803004410b49095160900c02c80008800340b5050040c5028180c0d60344110b0141403051000e040da101024000a50b0780c00c1101902c03e05802c035210b01800200fa0400040386404c145840c0088410007100401341303612190341d1082410700d145841e44403201c06000029130580100700550040d8010030304042c4000c2d43d1700004081c5d82c4018240d084403441d070740c20300245903404400350b5104041030500c29140c2440e007504a01410301110300030b0040c03003501c3c14082500c0907a4000c202c01d1110300300b181e00f60030452006a80f00d880714504140540c1100000503119400380e0444410014020b0001212140c2030b03588004498814401c2d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 175580818 1250 175579568 175579577
    0x170705030c03040909021f0806040f090212030c0c120a1e2405060d11040e01090803180607180b0a1103070b040318050d060e07080d1e030b0f01031a10 66
    0x385e81541400f000f0201d000804805c4c0d031140b06d10741280504040d031f01030f00490083d9600c010f0000900311542c4200d078090b900404048510b0503403802503a60382c0110003901090300502e4030100b01490b1a1074500c0d800645c85018003500212034540c2403a040780003482d003060b0b2100000800c0021b041520582e60200001145211003650403015001c646c0001e0406002c4c0c250040320602286803c0040f100c600801c48010842c1400c6202d210b01520881c90028082d020101c10700400001126031500340510308422162035695420f004c8034400b0290405081051070300c9001c3c0704c00101100105080b03103a81c1001b031120451240c06510f1980000401d60b9011540d01c00d00c010954030200d98100045032a80709003000303040c600010b110019000000303241946d501c3c4582098202400000024100807040d1190804104006003043d455045550703a071805855079990414003a00c0b58030003001028107100440800c1100660050501201403402071088440c2600705a0320b0101e11a90000b02e03544 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 175582068 1250 175580818 175580831
    0x3060b03091b040603081204060b0409080309060601080c0a14040b07080c0d3b0604060c060b040c0c03210f1a03030304121202090901030b041a0103170705030c030409 73
    0x640d08024002c000807140f16604102040010a4001c0d09444014905424213000754a8a01d0b18200808001000c690013500b00741130381c010310403000c000d50310a5403490203603115541c69000440703894808465130442818244001f01049214040c1081d4800740034101c5481d0a40320440c904060b0030a001c12200e010000400141c00e10303046c403403c028001c4da400c201841c3c10145000b624108003010710003003c0700300280700d4001e08034207030941e690b000c40280000345e50f19200e5000400b50081c503401603e0ba1703410300e008000f90b410688580d9550300904c1d0394006a032440b45d0303403c0720054400e002c0c039135040c0300000009401c15100e00c16070131440c410711070000700405080e60700058144101080f071321941040c4208000300e5007038912156000f203a442c00c09407111540348403500900401d6201500285003600100410040c1d0410900650181c1a050b2110341c0100314101b0300c00c1d09000c0103240745482c0e00c503403103411100d401500c00203120f03400b41c84c2040c03c1b1211091858000703501001040d612441c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 175583318 1250 175582068 175582093
    0x30f030c06020f031e04020603010b0c0a021203091005091c11100e150309070902090a08030a03090213050702070510020c27011703070305160b0f040c08010603111003060b0309 77
    0x4200310388000001c0d940582486e280d00000c0143c00140f02d4aa2801d20008692241030300c2409800e1001c0da00070320204180400781c0d0800c0d520780003041040c0c002c2d5408128554024054801d480c40504c005054a00603030040562400314424420211003060501c543c41015980d21050b0074807444165840011442c0b141e403c0100c4012a43e80011183d10100309124064a012a915003030310680c00e800b580d10345210000c5000c3d1140b030361040c0f1040c040070441644850303040c1c1003403440b18022502d941c6040524400101124070a42c0c0b00005039000000402050a00c1e149030441c181590060303800c214030500214010100c8004043c040c88481043c0b0722548000c20b41040c050300040f10020030076031a9444459480c482c100e009024483c0c042502c0800b40020550700c45107070f5002c4100c00c0d0a0030b10558640200d001520101d4031f9000003400030860003014400c000c11280c00483c031a4038107110000788200c00000440790401c054a0b124041981c01c8000e000318040c2c002c4000901c80d02c982007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 175584568 1250 175583318 175583341
    0x1e05010c0206130b15031f050a050c0406050d0f0605030f0a0501110301030506150a03060606020d170c0a0c02040f06150906031b030507031b050c0601140109030f030c06020f03 77
    0x801001040f030080041c400441d02002c4051350007403c01c801040c1618035400000d01d0611049286042d20b48440388200701580ea0350007150003140580002d005603100d004110b64140568001c00c1c00044090108500803200d07134100707000c94180720304001566a21170020a0400c0d0b1a4200c0c0700c0315074807020b60f00040000034030603003089118503140c0601b0b5504541e6540e407030704000f4101052040b0020f515070f011355100e0021000540d030210341048040d42c0c0719006074680d44c034000300d1400304132601d80d00800503c45030030a601c904505040c0500d050003032071050350815818417045ea001a5541c0c0083c4115020f88a00d80240501c1403058103400c04d004401089152103802c010101341c14510000845101c400c4207600c15061030a0205081e03071514400c0380103105c5a030003040d1040e05401640c40c0540c0040040925000030f4007580c09903030302c8103030075120100d82c44034403800525040750800206818090201c0e5041c40f81c5400f10701c1c0300040e2500c0702640c101000c90210b48400005000b68000d03003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 175585818 1250 175584568 175584571
    0xf0b0a090207020f0a050d140c03070608010e0907030305040603090c05030102030a0b0a090e06150103090f1b0602190f030203040e01030b060a0503010b090c09040e15071803050c0402071e05010c0206 87
    0x219102c41c0411b00780004203078400345090005110760a02c0d9070b8448043c40c28040021350301d102400710303410140d40c0ca03401040044288142c0d00d103040c1501c041007203510003048400a99425889907403505142510440007400c1099040e1a03060310b103d000b0465070303028001075000d290b90b0f01c4081a480d401ea0100312110340c0f20352081850070710700030442840590100701c0700d40c0100d447e0b003118425248840160054545240e0042c031001034a1702c070100b00040c4260502002c0d40000c0c0c0c80714040d80710f580c16a50f940140c194240d03d0051042c101c0300041c0c0350000d0a80542c0300c0e1040d28105941c0c0c403103070140b00a0030f820464040102038200645070030040380b0b070402850118001d10018042c44003181e003401000c1c07c2d00b54038507800611602161601e801c60300c90802034000712107040000002c580820340080d00c024001481c1d480080e04084410300102d41500e8002c005030800c2c01058040000039408004100c491040c030607036140c0d00585241007500d9139401a000459901800c60b0001c0c2002c90 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 175587068 1250 175585818 175585849
    0x222020414210606040c030b040c030917040614090d0c0905190b010804110a0803070f0c0914010902070c09050118060812090405040503040302060310030b0702030a120f0b0a09020702 80
    0x2e0301c1a02520300003001908200207490000300307591000000c401070101c4d4004541c220b404e10220654441c0d059108903412030083c0100403d04e80040c1e20300040d07109a00c90640002e401940a001e2680300c20002c2140030001418640c050b411651003c84452680d8002d241c51680d0380d0030003000080b03e0381090810b03c2481420890440140e0010708605009803000c1c0c100c1d0a00c2050803043d4565108510103001d100d0216901e404042c07030045d2017078613468000c884d40e42c510f540010f031071040c6e4011001c40740107001c610709291307080403040c000941180b1000d845a1203820760018500c40540710382c034043c005c0c840034118141c5001c14a5030688841e9407088002e5406801b00d17048140c160001d50b02c55100844003c5550313103481c20300c2031860045801c065401080007007481706030060a1500b02c22a4801d0610129540c0d801c8004c2c0d07100e000745e1203100301250030040b600e18424250f5000010507140400b00003180d44d04c0c140422100c801c50b03002200502d82c0041d40100398a06081c1605030850b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 175588318 1250 175587068 175587109
    0x30c0b0109060b0406030b0a09020d0603030314010303091203020109021503011d060a06030c410a050712020a05060a0c03111602010e150c0a1502160222020414 70
    0x61401000c0c0605208601c600d1713041503501e00c2c0c1c542442c1c5d6030070134110051680b51002c0d91584100c10501d03006110038401140403d15240c220101701e000020214101c1c2e0b01610342582c114034002c0d2512581d00c1d07001c0100d0845d540d038104800103980e40e1b44908262546480c0c615200e60411749186031038504101038006200e4500d0410506541d00d07255007041c0d0f6010302c0c02142e00344182070305945c0a0b160020f07130706145000c0003100100140c41069249403094080d0126501070003a014002603114034040800080d000300400d002145500d018020380c0d901510441d0914000d9807070352401c00710203851030500503485129240780b5543c14040e14160b41640e1910303602e01030318402c02070a40d01c01c60900a06004205604152075502d003164007051680660146030f50b42c00030b0311b01544504d0300e05008c0f074404c0c410440141510080348260385c01404083d42c00301c5e15030362a408000203001103502d00801408040311044828010740060002080455040c0c44c40c01100b500b00101600203d90011078007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 175589568 1250 175588318 175588331
    0x807060e04050402090612010e0106080307020a051e011b05010e0a0c05030c0306010302150906030702010608060a05010e040f020f060d0b120c0d03050a140703120606030e03040605030c090904030c0b0109 89
    0x1039a5140845e9080081200d2031a8100f100000300e901600c90080d41540755441c10a0004221001100802c1418030842e410800c0030f44030b004100d201411401e5041070104030300c07201010f55018214501609440e5041c0301c2211045038aca180c01e403100c8441e103000c150031820306c440c10400340b41c0b8818023606040f000740050741020340c086941c400c0148000391192441411180781003110904551102802404a0b5038074541420043d0107006140700d40a014400c840008616010506c02c5a041c1e9180b2000c4508644841d26440c1c1c0c6d00080182c180c0e400344608070001c0040e900d020003460090320054000ca54210044100701c1c801402014030681a000709044141c00d60b125510b05500d564181801c0352a09460b000444100f4044403280142920000307540c0103054003c00d00c00c0d401e850088081c403440d0303140e81c4102c040d0b0320302003000e5a40303501c01d0105200302405031001c1c5903c0002580f6142c00c116141c40091580607054500303401248042c0c00c01380602041c08070b1217016049840046c01013 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 175590818 1250 175589568 175589573
    0x50c0702090c0a0f05160f050a03021b0918070504020301060309060b0f010203090d0f08040b22030818011803060903020607020d1b08120a0203073507050d0203010807060e040504 78
    0x6490032813003810484002a100c0002c61040c84150015400860030710b0245214901903aa40900320016400341c45020602d481600004d0301030142000085e060403c1ca441d5181689000b5032400c090b0070340c0d40a00c3c280070a2948480c405140240750030b030b4004c10b82019900380304007224040c0c00124001e01101a03101e0099800000703c4011400a079403038074040c40c60303090401031103080010052801500140009510700018060a540101617055640801c407021755101e02151070302c401001e1020600c1138400701c0900020086140506061a11070044081159000303000c4640080741c6c4507aa0345c01800c24194100320070740e403060b001e000400c3c1481c6140b1001e8070110300c41d00110110800c00007040d0411080c04141e0b11f9a80c58000c901f6500d00348403c0d2200030b50400c40d070744c00014803002c1e2120049104d41f0b00040400c14000b070040052a520b01c008281c2880041c12031082c80000c1152561882041c4019070090a28001030041c0605004000b031000d030541007018030641c20501403201 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 175592068 1250 175590818 175590827
    0xe1c0f0302030402060a08041403030a0f0c0206090a020405070e090103050d03140f061e0d03080906130b010902030604060b0406050904050106050f0d0903023c03031006050702040b04050c0702090c0a 87
    0x3220202070a280c104d5036510310301703101ca580002703c1d458403902010080c00030b40f02c82600040040c50042500307001e40000d04404903522071f02200e148030309501c100300c0710001d410982d000542041880c60b04c408220054004242e5044c0285e00c111450740c400300004c159a603051040c000d15050802001225080c0801180031480c80688403901c87e940d2174860200194010f1a89440e0400141c010031644034642000343c010a4101c449248a000742c0f000110624000e1002c8151a540012000c0382079007050080e20081d0002005980c20640d10000410200360703000241c001807010703580e41541c070b02c0c411082c4415110706a00480a10405000f03544070a01410240c9080b030090b040c3c00600d4681c1030508900d003480040108042c44245802d61070000500207800000254101c02459189800c4004ca40e0b01d2004682e130104950090006001e2148944020a40140014000300c0d52540f5100090212441950780c04c01030710340010300b4021810848101d5510100c505402401c03d1006d000160 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 175593318 1250 175592068 175592077
    0x1080715030212040f020a05010e030a0615080708030d0621081e040801020d0e060c032a0d0507030b030a051b0415120b0f07020706120e1c0f030203040206 68
    0x200c88030003001511841a200354140c40504400810410007800d0504240200b000746210a0707004440c201400300f031a500030b030900b002c03030310303014004280301c1016464220081034054624080394600d1080002d840b00c0c01c000581c003808101002d5aa101c003402890000c80b89030798480320b0f16450641c41d802e0070300800c26003101260740103020365540d010304540c0300c54902400c190315000c4000c0400c0200c3d08400540c00741c420102c00d99000c0080c0b0b03640320100e90b60b0b04c000b01c400c0a080c16007000060204030741001c01c03409652103808507550014900c8500303489504150300c00f41c076455a440803c0104c56040c0200d0840200643c06418980c0451f21001d4546003241101c060040487c084c8018a849a6203c21292403c41145811903602d48400d540f804114100984041e44003c000c05c5000c40407010a03802050640c0040001e58038240d019a4010300402400407095070314003018009410501c9803148001051a8800d40b03140701c164080c0c0740e041212282e60400d40306100308001600c45c40d040710b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 175594568 1250 175593318 175593329
    0x70501050705030d0504150e0109080403021912030c0b0f06030a03030e07050307090f060501110c1003090b0a1b0507031407020409050d02061009020906031b041a070218010807 77
    0xc55840c14203040140ca54407980c015698580c0c908801c12080c45000000c98804d201d801c3d109101000d04194240c0c00c0c2d8609517400b40214404010402c018645500824400d441049104408a82d55003266042c00034542c82580494003200004042154003070860350b200c40681d8030402c040c181b0b1008680d9072031002c07000a0505650301060908440c08100c0540240802800c54200c1d94071013907050081d00c801c5030340b40086070601a010500f5800ba030108200303000e10000401000718110100b10840b201030880070249030b900c0118034017040c4c406200c50700c07403004c40383e0100f40200e01c008101c0c0e000300301000032410081e0a00c50f81c00000d9003c03c18001c134041017008940c0721b24280c0000f80c01404d01540040c058450f4011190342180c011617480e21034611700c08110526643c0e8400e000581c8141102954084c2c8100000f841158070700400001c0b41e800707031201c02d0074030f61100011056000341950350085818080f4038202180342890350120420245102180d440d45000b034282d40c0c5031117030301a0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 175595818 1250 175594568 175594577
    0x7150203160624031424040f021507020901050103020901020706081f150201060f1a0703140c150604021e030c0d020406030b01030b0a030c06140c0a0302030a02060f0405070501 77
    0x4181401000e4104603420450100f190301c949011400d0001d608005110880d458000d0700b00f107850080f000310b907071038080341d00c00882c00d80f4020f034030400f41c51444000d001712000c4e06141c4e00e010240c0c0300d0351080d041340048000fa031507450b09039004201e20513105900c176504050040001702903623640800d5210440702c6600300508992200c1220000080c103184080b042e400360300b60f00148a500380c0405070360024958008026041c0c6988240d03504c0b12250284822108019000000301c41c0c4210040102074024a07080c0c0c2c0c0010b0b4104401040d80c4008540e5041d540036007003200030309034014001c1c0d4102d4002c4038110f103424018034040242904041070710940c502c01000040070320b80450700702c80c005a81800c04550340c544604000d4000e00d4607000c0140020300c0d1012048042c02c00e4500107040e02c2d046110109090b141c00b00c200c40d01c4600c0c2441c2c9003400024460250b1201d000c2002d940071a100703030003960b10340d00f0440009182510060100d640c251a140a00c40401c50100b00481508d07002c0c81c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 175597068 1250 175595818 175595857
    0x21f0b1c030e0409030c0503030f07090b09030706141e0307021005012402031210140618060f0c150103060b031b09180d020a15020f030c0a11060406090507150203 71
    0xe01b5101401d036030703401400d05c3c0000000c0140b481e00c120390046c840d008070348459100c141c454541307150034006d409845800d980000030500106e07004407105000d40f02d52005191401c1480035140303404020f002e01103a0b0119001c4144484550140010002d000f910201040151b24100043d140d0381341c4200300f101c183e0900c40c860040310348207000321a04020690044648e81c00c004100d20b09034244c901c9608501201c01c0c000c2001c62604200302c400e000038504280015490328001c01181d41d00181c0360030210350b8104030114810805000c03060801a11115511141d89941003c2d815540b1706130580e80711b074104214400d8080d40c9501c0140c80b440d029616290742c3d5407071a0745412104d9580200e00118485e4114243d041540001c1e1801140d2103450055107400d00500c0784401d074041c4d0300703422881810900002d06c80d413004034080d01e0a4021391a046082034554040305080100a0b0381c140c0f9482c0c1c4400e0200107010042100314000c0540d1000050314203484440291640600c1185004e203200010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 175598318 1250 175597068 175597073
    0x3030921120e090c12130317091024090e0d0f0504030b010e180d090519030804060203030103050c06030609010605070501061a0a031404050a02010c03021f0b1c030e0409 74
    0x1190480800b8010348000002c2c18000c800031060b40084100703003410000717070000410440c0e031003503403942c483d5054640042c0210a0840e20b41901d40c0103018840910942d48600071600150041c100c082c100e480904450800d008120002032500390401e007640380c00c1203403103035503001c00096a081c19629841c1990380342d80488ea088802e4070031a4000ba29000d24640042204045812418001d0b02c404405a1080d10540411510b891042a0f4a4080760300484c0420050a005c00e000a0b030454031a004e03003010f074036992402c0d03c50f04240c006500503070000c0018400c1200c10840720609403011a41d1604500d05440010900c5805000d0300301000404514807040040940000c0081d20700417900d10701d801c0b060301240c40150000d507614000a428007501c0700784d91801c10b080342e0086030014090401c88941340c00641703e20310208412030442c0300300040190002000e5504500740740030100e02081c0340c80210704005080040030301c6140080c6002012400203900001051034180044da40401c00c192a030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 175599568 1250 175598318 175598327
    0x1d0607051305100e03060703060e0c0a18060c0b13051902060c07090f0f060812091314040605070f0c14030d090803010e0f01030305161e0605010303092112 68
    0x5500040c0c101801c03072000ca800766001209001d130004181e04440c502d54921200301c040c0c0d076480c0700d071040c000b081ca8089542d0b5149900146134076423480c00e040720041d4a464511400d8100c075031103d00000c066407060f4040148d801d01460700101d00b90b90603030200e40a508c4080d00c0c0c1404e00552003038280758400c1d80d400c40d15200155500c0030320000c15540740380d41d1030162401070100f000508a2481c41c003064a00003030403a110b080c082d41d45110003400c220840a000b80301c603501c5035240c298000b89003c4a020107860a01170441c1040c44401c2e80045400c207031401d07a066030405480321083c007000504544000c0e900000000d240d030341001c04100300152000c070541c25841808200c04809003002c15613400e204482c0000c5040f03403003400f152242c42c1e907a01001030500c00203000003000250200f0001c40c00740302d8545840d81f004d003e030005115803500c0c1418540c0e450810002260b0341522140100306061700304006000419220081504030040070314400b8903882c60040c000d000c010245003030011035200307 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 175600818 1250 175599568 175599607
    0x23030708061201020307020f070503120702040c05090907020106080129010f03150b0405130504081c0f1b030e0c06040317121009060807140907020a0819031d060705 72
    0x91800131550f900307203440c0094840000d6140c40d6420711030500c001400d400d0000c3c64030204044000c0d11030501d030b820b07802c10001d401010326440c10840180500c4000d030303442c1c001c1c25024030002e40001840604d001307081401d59094200c42654916904c0d002001145000c032612101d2509203021140041c07201405d80007032a00b01200941001c0c0044042100201d0744024419240125800c41340012002c0e414000d8034003c42d40207140307100c240101140032560007410300002c84181004100800e16139504412640e10b01d010700307140c100760411092081c0e0036101d001c01c0d006160000c1d19850072a4004980305100b0f900c0300519071681c540e45210042411804e440990240500c0c41d4a42c2c00e242d514846404140c0c002d4180452a1600c0000c81d080c2c0010068111a144119100c501d01180200a8402c0c8010b04100943c01801c14060008403904d0040c6102c0f2005903003c510007a05400040443e00585141a0007040c81d484100701c1240008540781c2c040bc09142c410b0307481d80c65000c4241030004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 175602068 1250 175600818 175600849
    0x70906271e06060810080705010c11030a03080f3610090803010f08030a022d06010902040f12050604061d12042103090501050f04030b010b0301062303070806 69
    0x40e8800d10035800c4840e40240c8202c43d0310741d59030308081d16100e04003968030045105002860b40441c0003084294010003220550034018a1000d03240d10004000c0390400c0d14400c0c003203001a0301c000820041104000119410044009014006109906da50141042c500c640e188040007a00700135603249600300912548514090018041444a0700e02201250402e0040705180300e42e103c0701040304080002614028861a4010071100c0e4400408445c13903003000104000e264003005840302a02030400a45000f401303880300040e651403810300407d90f041c0740e43e00107070010b4031074440c00d00c08130b28000342c0141c100d6003141000804515901d10400c0407070425103640300c14058080403000580842c406002100d08004a01e00e101d00034105552400c4410f03440113021658441e010702444d4401c4020781400c5241c01446843c02e9140d48500e21484c0c000d9012076982000003005104044d4015906100640030403036010170915160318142282c04010004002c00181c0e40000c3c80d0340e81c80380d000d4440b560 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 175603318 1250 175602068 175602101
    0x30903063201060e010804050a080304150c0e01021018080f040f030b090d0c02010807180b070c03051504020d1502040512010f0501080303091b060903030406050c07090627 75
    0x500c07400e00d112025000d03c036031000701d2100121098039500818040b1b200c2c941c03103400b800d0443d00f1ba541d000425080908240c40c24150050034070511034161059100d00c41240d1210782e03101000400081c9044106000401c20a090640c201d0481000f0442c6800b800d51101c82c060312001003400b8224240520391000e03a901c0c005550000030311036060302d040e00690101c4291048070b0842c050a44410a0044000340010050800119114441c5546103c0880da541000611980d21719440d92260400d000648119900203810801c2160803c541c4d44003c03034603027100840f403a02c0d8001907010740e0982000341000c00d01001001c1211044e0303040b1005428010708a00540c050300000303030700902010002404603031600c0008035401c000001503a10841d0802d0060540e44030845c40e0211509179600300c2a0404014044034215641c240051702c00b42c003c960326652110009003440b850200d0b1503200304e00280c9800c10030b0200040d14001c075510942c44045080c02c4030742211003200141200804070005c1c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 175604568 1250 175603318 175603391
    0x61d0a150b0a0908011104030b18011a030f0705030c10050d05010906140a18020c010b0a060c030f090b16050309130b040606020c0a090e0a0611032203090306 69
    0x20030001c000c1c0100002c03607980c20781a40c2d11110703410308803051204065a45c01c424042040080c22614105034010941c2c1000407030743c1c00f98407003107081d94030402e50039000c0f44041c1b82000310360608000c6d03c0044072207080244252864500070075211100e5107403c40c00307a08801011605240110101d0f003018900210422039907a65140c180010081401030301080301022540024916181038100c064410026103007125007041c4083c40025400160605aa07548402c0200010342c1c424600d00010300c26a250404e4a10b01851f00800c08230f8149500c80502095150500050070b00300152515078481d16140080d50f0700300d051862642c0180a0340c243c0c001d096910041459101d9008100344400542d02407001907180d0134140c0e05c0300140d0300140d40050f40c81d102080004020781003000040301071002e03903840c10348980714003060f40c40c40002e01d03240c90030000a000801121190187d1110000281507402820130b5030000c04940f40c2c1d20000e040b142d12100080109440c104955000040895805240 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 175605818 1250 175604568 175604579
    0x150c0607020c0f09040b0105092715060109180911120c041503080d091e0305090901060509061227070e0609040b0103290a0b090604061d0a15 62
    0x1c60040380b5680d406411000c65800480c2080039195000c0d43d4890300500039a0f00304014403815140081642180120720000640030001215101d048042500050170882940c3c0000513007011025103c00e0402001c0682045003c1c298200882102d4050b03c01052419240c1808803821407140c1c0d416520402e003602d0f10840c000001100c0c17510210565050190804401c4100000d000034031014007000703c10082245841c40d00d03406201c043d445207443e00303c4503400101a902c88024001e084003c18800a0504454a000311100f4010032061500c00d10744207a00001c13555a0140884070380740c1001d0b800201d10401195803441481100760207050341e10200205545559420318443c80001c0307110600030602504000b11a14495600210801e030b060f461a5222045580312502c1079100026044012103146101280300e40500c00f4000301081071882d01c1f007008402c58010f07001c00d10880c5040c40401210690040e03000d04090b280c120001180c2d2040c5000e80a827205c5035800000c003004140c04283c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 175607068 1250 175605818 175605823
    0xf0201091a12010602010b0a121a0c0706110306060d02070c0e19050105040c0207060f091e060806032802060903030403080309070807030f06050a02160809031b0f150c060702 76
    0x42c0e0300d00208a00e034069983d52016800c90303000800803600440c03070f1481400880c88501011035400c1c0300d05011204449520703c011448030068446000450002412006000a500500d0582010190b480d480c40c1010b10000344580b00380d60b0032000950300401d00f8400e2000c4569600d00400b0010b050480d81d00e000040040c2c2d914100250128180c42d09001040078103240c4108a40c0d50419001440451300704103050ba035440310000068100711b142800410402d1040300024540f05034910711500990409a011b4140c400040055000c1e5208240107001a031040070785060040950078048081d040c2d900214509109202c06982c162100180010400c04407100075441103c010b025126070980f10880143c03600000c3c0300140510020701041e50124450794032081d00114292030041c40d000722802036841d8000d0900040d28814400b1400141c0360909000d103a0030f840d200a6001e401c41c0050b8001140808610032183c05a0a2503403d60b5244850404551107811440704846042c501044003d5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 175608318 1250 175607068 175607077
    0x50d110a0e090d03110904020f0f1305040507050304020d02060a020f0f03031605131e030609050601030203210415020a0b090705010207060807051909090204030c030204060815040f0201091a 83
    0x403401d106603d640c0c06154400d106000d81800d454621a145c1102102004041d41010120984503141000301c2e03484e0303480b11070041c010b24640c3c608510300e40307140c4410002103405c0205803206000e0100708010041e907070a000f48001d181c0c120707042c5407502c40700101245000c0700d00c4018030081c800c42c00041a9180c000010f5071085900e1600e40c500c4144ca80001c44d007e0089511440c401134004406000303080c4c0c1015000181502c00030585d022035601c0e01c499007601c41041c02130302c258210358014001c2d17003410f03c0401a0360f41c060043c40c040200015044009210f18414030310f007440c0c01610100f0341031081c400e07081115000345007601d40f0304141d0241600c902440c450304c0d000d807080100006e1594003910302c0d0303441051540c450504140644000c602c0c51101c01d520310082101020300810301c400c6500c043c201030f501800b04c006040e410f501c1844112403242d00680810b6001e010100e01c4800c001e40000d070f1050348010b018089200720f20040c0e446101c16040345c28003005044a40400c44009c00152 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 175609568 1250 175608318 175608331
    0x7060507020a120b0a0b0d0c06120e0601120b040f080f0406030606080f13110907020106090509030408031e0f0a030203040501380612130201110d020304050d110a0e 72
    0x58024982c0c5641401003c0640a00281202c01500010b10482d03101d0b400f01102581c041c10403031101402e960381850400c0141c1000010521820301c0101d032040520848a01680d203030001c01555042140c840d440d10ba0341d0384018900a9070000090403c0600410000c42d5507004250ba5100d03901d1041080b5260000d000d0540040d160110010352a8071546075140581c0d2402c1c2524620b440d01c1c4460100c03403003140c800351151008400340f04203a03120031203e80e114804a17400021598185001801034440203403205080d54424001404052000700c111401c1200000030302c2042c07881e001105649008510786100032032408a041b581040e0182c0065100358441d000030400211006040b40c0103159040c00c800e4502c1c0014101c600c8082a8180c0c4c0c00a910020246030820604034040e0740c264408586507414941d60075100700440d60842100a03280301e1700d2001e000e07426007810009669010328402e441c45031042c3d02e00c520034895014410328240101074400c0400a403102280003840b041034621 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 175610818 1250 175609568 175609579
    0x705130e07050406030c1a091e030a0506072003270a120f060b0108150105030c1c0b090906090d030f02040305100b0909030903032205090f07090608191d0706050702 72
    0x32800e0031f144a401c8640d0603100800f0b9100880b07603480c50112481240e4050754051107880140d10114504101c43d603c20016603a03100d80030340039081c04964601c032070708900100da84140034014420f400c2d10400c1988070086042d46004216210008601c0c403940d51040c0d50321103c94070030100340040d40c0540c80b00d1034000c880071700030f80803200c1c011524254100c4801c21203540040b00c58030346620440c015a048002810b83d01e0501811103c0980840d400c003407100d494036aa41001c3c0e805003461044075900c101090040c003800c0c548201081d80341c684402c109410035684a0104840c0b4a8aa040c0c0c0c0c061a04070007203880301c48901c1c50b403100070201545c9440c402c80c051000a0484140002221824800039015505200b205848240c20b400e1000d000e1000703445078200400d158441a004600c80c6a00801c451818282088050928902e0303800c020200710a0804008400541c4541178203403402e816000200400c0402a60b8543c180f000100881401111800903000303a0103006801158001c482 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 175612068 1250 175610818 175610849
    0x72d0b010618060e0108040c09020d05041208040203030403030c03090308030a050702120f0702060304382a0d1103010b07030e0d050622022d030705130e07050406030c 73
    0x140446018018450b43c80080e0382c0700340303039043d80d403041ca8243d4001d0301c69191420038545880c80310059070004040b13210490760f07075001c1005000e41d5101001348003801c4d061905e694286600425201e2195010150a0003110180c83d010035201d1a6004000c640040c4501d03101d040602e40e020140105580e401c005129540013090680128800c580c4461408c5e0619480c095555090089981004000351111401003090600168400840c106040203800000070072000154540c01412405045003c01109600921021010303101d0304814409039281416107030140000c484000c0e058544c1401d2000c68040300025900412801030141a4480c5d2142c100000c0b00c04148401001010340181c00d0f0b0f4030030400716180903400041c07409090715000b40b000b560303034050f0049000d8610000e880303240a0301840013200035440130408030380101c81c21000f4082040c9070000050075002c1d0080882c42d00d581c1c80c0c01610601400304000c50062001800c2805013560f00e042980e0300c0440e6200f0400d480613003a0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 175613318 1250 175612068 175612097
    0xc0d020a0c062a0e0105190203040e070c0b0106031820010e04111e070606060e09060d050a03080c040518010608090d02030412020f0d0c1404090305072d0b0106 70
    0xc0c001c1240340307003e04800110f44014901201c500c19052961418090100090390340203e481108a01c5403441d900103551303031458a0b000d940c10300b900400900c05c00494007202400070320070302c0846045035400c1c40c0100700b079981d07002c5d20003d5940c203800c010a2014800f10249100e6095089001114026210341da640f01e5010144025a18115005010380d20200149001404030b070b4002102c0b880c10322010350901e0700135a5544200c640a4000c1004030390487e9004100d481c02903076440e4400ca0558265215140540c5c0700b980c0c50040250060070300101000040081803010151f074018180149220901d00680b814094008803e02403080002d140d00700017141d80c40c0c0012158007409203a80214074262501d003260f10340d0018000300301e900200c40c0801d1052642d510140100c0a80105007003651540361400800032000d8024030036004508008510002c00d8000d4140c1d050107070000503500d803680c5000d0800e03415858003202044115440d0958205021940b9a514140e40590729080000031250 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 175614568 1250 175613318 175613351
    0x503010f0b03061f0f0b18040c08060d0224030a0c05070f3503070f0e030d03020304050a02030a15061a16031e17010e041a0c0d020a0c06 60
    0x400c000364155003c20081107130380b000c010040195240e00320900032010f488404d030304010f80c0321394401001c106001c151441404000c00c9480c1c24220125010044070390304801c040d003490b01c014200b91090500c20352800954a40c605034030040960002011102c8030701c0507024000c1d40041d1051074a0700d1034000c8400181e0f0042c411034107010f80024148522080c0780d5140070001039094016126040c000d00c0080480b402203489000c0301c01001103a40e00c0349001d80c0003c10901800080004010070052805901d0306d010810011280d294640941d0b84d640d90b00700b1078a0311126460081d05071003201e000781c040c400d208413003100c030490300d400038804155200d14600d040f406004644408501c100500c40d01160040c00c4110450700c80d040480c014207d041d07248807404510302c1081c0205010350003001300b111003440d01c54094280313a0507120442c102a15400041d1300714072420b21000d007041c0080b40404018405a13208a0681102076503140071b9898000c103030000500040382c12a007840c2410b00b00c402c45 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 175615818 1250 175614568 175614581
    0xf1b020303090913081201080c0103110d0e0708100203013204090201031b02030a090b04140d03090b0f1b0d0e0402090d0c1e050a08100213050d0506010503010f 70
    0x24001c40c10486100700700324400c0d60180004003c1d000034940b06000a504d00007420300c800b80004120714540c0b401c64038a04060400340d549041610b0022441d4120740c5582c191502c900a01400082c4c506500a00c2403502d000c0360801c22440c4140c00e4a41030b0746542c2d40081d41a10803000c4400d1101c01304a1110070301e0300f1540381e081c1d00340040c01000c031a5030520398046030f00c4500500d07000c2540031404400e6020070428802901c010303000068024403941c1c100041074020464171441c10300d020310300f40c1d540007640040d5010340e105000700c40200c0180f5100d445144058072000d0012641c0c0d041c8801031862940c02603c0c00d111884111071540440c2001003014130071300070240c03079a40d80b400c030303113000c01c002540500d03003c2c1d501c0404102d481e004101188604c5001c0c25065003075048105044d011588903070340b00e5002501c43d060000003840f000310045261884001045030160b251100122204034000c0076410480c0c0200c44540d107002840800540f1030704a8078107900800c410300800c1c2d01c1c20142c900 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 175617068 1250 175615818 175615823
    0x120714030f1c03060617040f0305091306170307020d0b040206040e0109090302011a0913020301110c06041e0f1202070b0c010914011104030b0c0702030a0c0603050601050403020a0b090d02100f1b 85
    0x40580c0007801148d00c0d402801d1556110f40303003c920300495400042c0422041c0440d03d411281d0314002448501c0c40011400c0c1c0303103490440150f061a8095001401c03e031034440d00180301d201002c1c041004c6448000658003e8081840003100540c0c4660b1688000c10113400103400540c202092800d9003400c4103d0b001e00108042d18080103079441850801c7d01000c2d420040347c041d940c0b00b40342802c001e40c60025100402030003020b05402d00345400d081072605100000c1c00d400c00c90604030b2500103a9000ca02840007a449801c112011050301400ea05103949070380100312403200002c6040840d641980451402d074412104910001a0780d03070468200c424000a4042d5070100700070501c0854583e100c180d40c04a209110707545042c5031580070908103000352100f10740402e0400410710045805016050740040b080c41d15a08041c5140c00160078010316101c0c1281104000540b151252284010380682d5600030301000c100860610b401002020780c0320318907002418144051003070300c500460413240c564 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 175618318 1250 175617068 175617107
    0x110402090607031110020a1407150203090d030f11120a0e0714120705090c09040603021c050709051e0a0905060403021605010e030705012109060c0905120714030f1c030606 75
    0x29108500c640c0c40b82d001d400b050b100c80d02400910484ac071540e000a5108810850243c040d259918038040e00741c0d4104492a161305080416111440c090042138034160642015418810b45640f1000b0004060031011b917011401200750105800c10840345841604206071400652036000e403166035161046801490340c010020720205200700200d40c00750040700c400920010b401541ca1b03000038500c88182644900640d0210a05800d00000303009440041c01030a000b4025480c00300c81034420691341702080c00e1201c440002140920100b948801007007903101c0102e5030329090074200a551840300c80150100000750040106213544500d040c0900c020000d0001c211380c5050000666520701d1640c5031540e4410002c4061480500318014501c4041c00780c1d10009034241c7c0d91100422951f5503400130703400303105030694020110030001040801c540c400d5200c1c1800024110000f401d00034400308104042c800d403281c006034490700701c19400d81c490041d1003c01200356143c005031103a8441c00c41049244 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 175619568 1250 175618318 175618337
    0x10207030b0603070b0c06090c01090605072612090609070602031911031b010f23040302030d090303060512060105060a0807090302040f0c0921110402090607031110020a 74
    0x1441e101c102036000302005059610081d00c50820180c0c0e90407000385000690701502c14481191014414000c04060a1802a0b501c50400501510f548200a4020301c5001351801e0f0788200c911580c072040408420312400c65499266a00a0700d0038441030319807007118041c2a01048000c0f00000c0c11a00f110155005181821844000002a00355801e45201800354940340494102070910040482c1480300440769901c1c00c0c030710500350845496808551210345445100c001109000389600816010181c280c0207540c1d407032034101c1c250302454404941171070806602404058042c0c000e5810f0b40c4007696169000700240301c13035564981d000c0c404c0542180041081192007441940341c6035100c0382909150400c11341d41d5010804581c410010801c200c1e5813000010300c80d6074400c00382401000003030098520340c1d8014569030701b08852450010000c5210381506142c0d901c8036015a18902402030403203072692250304010b80f01c540b6031500008180204d0b000b212581485200303441120103a40e54440c000c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 175620818 1250 175619568 175619573
    0x708070c2702070f0c171b0603061002010603080a170609150d11090a091e030f05090414010f0e0f07090302010e0112060b0408011d1209120610050f010e01020703 71
    0x951007050259400071213503842c2c0d40031613074400b1390a00600711442c40f20741e140c24450500b410101c003244600c1c110500c2010b000820b66941c000d40380c001d1001c84203d0711002241030141d0043c20954001400c403500818094011a000380c5288000412040d0800055480d0401c1010382441159220180511000002d81c00d08140504100451081501c1c1088650f040002001c5170021030302050720a0b144c99040d0308101c00301c88084035641190030103c902441c1d0b40e4015100c030701500094020400081004045030741c2d40d400883d1041440c5000e8503003540c554540219600310742c061011101c105001040d01180da01e00c0d0284124030954922034202d056600450388038544042e09410817040b000c54a100508a1140400406000b407405948500c5c0c1030007230f42902c481c0e40c80b50600c6241c0d81180140800d02040102d000480c0022a40e17075a000000025540340884040c6141c41c031807401009170080440209005640003142c035a24031188550044038076100701100c20b40141c0050b80c08000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 175622068 1250 175620818 175620821
    0x1101051e04021c052b0206070305090709050103050a020312032404111908010501021f0216080a090806010911091002100c02010614060c061603060b0708070c27 70
    0x10801c1c0700030f004035054108000e00c202c030000440002d50361030300130000742e0b00b440e0f07081070b40c0b455035000b00210041e111041040107920b8000c000c081c402810380740d80009101160501240000e00035466017000696140c0c10b290340d5801c00c0b1101280240301e501c58101c6000203d4041d81e10407003248030409a664240b0010b011094100c403d02d9400649610707140702c07440807100180c0390340918009442289040f2160042c840c00c810f034070a506541011121589d0136000001101141071a001d015035610108104003e850301560400340c6103c4002c03450410183e40002840708a9116000f16034203641c940318200100d03016050041084002088500c8082c00c255860b0000030300a0b0050b90200f1b00c00c41000310a88409402c4a130050355640001c2c454803004c0f06001d1200c15017a50901e08004c4002ea5003aa038500c064000302c1401015510000c40c01c1c841d40000300a400c000721001e407110f0b03003440d0990b6160400300013207551125013403010942c0c44140c4000004500516240c6103002e9054a4940 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 175623318 1250 175622068 175622071
    0x503120910180b0702032a09070302040b1204021f0503070e0f010c060e011103010b070c081203010e04080403020411120a1a0402070206040f03050303270a03080601032009011101051e 80
    0x1b6014011b0150000c5050240403881940d05900340041400d400c00d6010402418001440d080906105020034410031102d1030644514200105100403151542d00000d160f0010440c082c034540c1107000c400348801e59100c0c01a5000b00c42035266459003081440420411007000c1c0300729070003d00081c541c0c2e8045619508144241c101070f6000140c004c509655801c19507100341c0045240c200001502410003c0c1d00031003500400c0c0000c05444510281214400c2e6407206205800d101000070b00807606011a0354103da0056034000d004200c16186801410180d81105078400507201e100b9001400080c0c980c01400390780d001d00c2c4000300c02c010219041000a420099090760804014000840c03103105000c0904003641c000d400454603468440c0c82044c2420780c6206600600b01500d0703207035815440004a2012603541410314101c55070b03403680103c0051184c0260720b102c0181c41c81d0310742c0da0700864100606440a0a83e181c101030340c2456805400d0b110150780e0030440105040e00c143c0815400c1c0c0006 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 175624568 1250 175623318 175623323
    0xe1905182206021b03130b09060f03190606020607020a081605030d09020f010903120e06090d1a07020a0b0109051e07030c090f0b070f0303060503120910180b07 70
    0x880540480340c50301c0602141c00c0700c1107448a038001549082d60340410300a041c00020302c03004518140f00007034245480c61041c403036000001c43c0860120000d903142d4056030007050008445d03545a15014040d610214a00c5421150a51034100c0c04102d40303102051b0188503064640040084107400e55a100035a8004000801c1c0c000e840c6181000180301072006107502400140c010a01d002d0a00400036004030000840e8180102c10404000041c035884d4031070345029180c18068015009030740450001d224650280b80d02000000c084420010640c4100010540030010404165a4000280c1c0c0e18806200d026200005e290010002c120344c41e00240d41c4820900d078452682000d0050b12002a041a03e171031020a031202000e102e01903000c07a4400040950907098501240707440075020341c0d0b100b4030301c0141511980600c450145800307904004c0080501030304562043c081c04603012065005040100d2080d1051943d0716a8a8801c018051404030780808401c0700a2500c016200c0660044404 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 175625818 1250 175624568 175624591
    0x20f0607080919031a061c030203031506030712051f0e1006050f0d05040f1b06030c021911010e06040906090b03010b1f020a05070603020406030c02060c0a03110d0203070e190518 78
    0x200710880401e0410100c155108e134004503101d0600c010000001122000468001c100074801c201b2038030780c890141c4207428030911000a0a4403407510141284050702d4289405604002000951640c0e08114510070601c1c80c1545c01c0d115200c0304202c84030720902204009030102071044681134081907002d150018450b10203182c1d190050b544507060102d0202c6410390070912003408010407a014042c070706101c0c01c284040c05c0f41041d086450f1301c552801d40d402804052400c14484920b0340100c0b003074103140310024521502e650303031107404102420b094059029001c0c00c162420f007150805008a078070412008101d115910040d200241d500036071b54511208611803c05120003140e000d20456014141540d4050b03550703810110b02905440000324520115071040b030400004001391410303500303510424540422a80740d50324182c2c509019810340c18070800d10000a20000c0c940208440354052403e4030b8050300b101c104070103d410f040703041c03041c581c02850650301c580410744883c000c00e5104800106 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 175627068 1250 175625818 175625839
    0x110409020a150c1208010503070e07020a11030a0204060f06020c0405040b07080c0d0903020106030b010803070b0612010f060b091f0503010302010521040308010f09020a09050409020f0607080919031a06 88
    0x1c2d070900d100d02c44131910011601c0c1c0c00041c01107080501c6020301502c50b81088503600d00708840300a40d02c49400e84003415000030f00b2000002650300740720004540ba001003082c07112070f07140c20096100a03100c2c458a000741c4a00001490941810b01440d03200341c1d0800d410080179551088161090301d401015403a4682d400c0101e00501d4100e0720890f10258001da000280030381c210700d0080030441040e0080190303680184110000581c1988100c1e520920035920441d00c920000c00c201d01400ca0a0b000c800e405051120226101e004040038100b40e181c220382c80f0401d910758280003a00e0301d043e0000d18000600c100300510165005100404d503040c1c1d80042daa02d41e194000c1c100000071030a47d001c40020b00d959004012800158040b0720103880e010b141140340c00351420000e0002e0f400703440f038280115281d144050030341d524180e424210540140440341c0d41c01c89850505595403004a990340302e1945c111245840c0010307904040103a0f42d204581010003280c0201c881b60000d0010669035101d01c0c14007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 175628318 1250 175627068 175627073
    0xf0203010612151802030a021516031716051213080d0f0e031611120613050f06071d040b04241203023003010b0403110409020a150c 58
    0x40d0040082d8003c080c80d196004180360814140e42003000d02c0160280309115503c09681d001c10403a5101d9411110034206001c0c0d061510428041d414981140010442b81c03c8181900000080c81035040038200102c25500c2c014214250b142900500000480c1886101ca190005001c250340041c08154201b01c031711595603481c00c150303001c0c00c020949283c491801880d143c1d0280030f001500c20726180594100040100001e128074041c0f0000b0b00071030f0b80300400d140c0da6120041030301c48500c0c0300c00c1130342c10512341250200c90003603081d4805c80c0e0510450004082003200400d9544c007403003696482c1c4102950b00032010f01400129811a5445a038640d2001555a141c2c807a0107280c49103580b9200c1101e42c880741c211140c100c0e40e4070034440c1407140d0034141c0000e0b502007824041605200c004400040346240e0300f94841480f26410501ca10300040081000140307880038100b100d10aa10a0124441c080c05020a503146284000d40180d0861018007a02d0a202c40980c2c1c1c48074a441c04100c03450407034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 175629568 1250 175628318 175628339
    0xa061e021006060e090717191104060e0907020307210e040507180f030809040c051201030312050a0b0f1c06050f04110d031d01090b0c010c02010f15030f02030106 71
    0x2a40000007280e9140e8488085051104c00390f036021869051000c030070f61341c40c0f07042101011f0081401030b161421003841c20303280c030300b81d0300100c8062070450b80507854603240d10014001310a070341d0803284142040c000240c0454400011103200982c005402c200041105102e05100a840d8804005106040825440544851040380c2c850100350340da400c20b280e140d500d00e0b5140012074100080b100000242400400d948000319034030b07a5001c1c0d40c00603c191a41c04221f4140c081c401d000700c2002d003054000428181d02001040b1848010b030707410070942e240e59004001319000c0c20541600040b0641c2d4481151500044190b410403003900324980c0c41400f6900d00003143c1c01118074003c440620b0040c80140450b12040201141c0251103c50b08030209071405004d000d4410303444014030064080f080b82ca40d00c100c0d041c000074044074411545074518150b049010306041c201500c015840c02d0100e0403001214007a008034a072500166882d80e0381503840300300070304810410a0380c15640720b090004510600 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 175630818 1250 175629568 175629581
    0x304051908210f0a020702150708090d0302030a031118100908191202030307020304210b0f0a0e070b0909091501030c081b090117010b0306090c0405060a061e0210 71
    0x28035103050782d1860640c035850001e90300a0b01d1403082601c10f2001c0030042c3c8450b45004400213941d20300710788906561800c140703103114802542d9046640c10701c5680801d40c0000c05442582840d4806000340004041098007a01800e0a0400c8840b194101500e59040080f44000383c841d16151485006844280003403900d02440e80704d404021007244900300f03000312091a480751214030f1018518506103a84000e54074000d0b4002d05c0b000c06642c66004090070f2880315420611a0311000e00c0c0c01500e0070241600d42e00104a560032185800c10029220000010880034191600048024144030400c2d09020343c8a00007000d495503803054440c14401e180c1940a51030081d4400c01d402d401c100d00b007050182c01c00c2c42c2801074240d900041d00c8411010740d21079030b12506481c00748101013800b12221400f00d000d054a071900307030b4140c0103443c28400300c0f00010403c2c4c1600704056a050100384c5650302845010699031041c0400030b000814100d201e06145841c55003c043d551049030242c84901d9801d03002c4614 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 175632068 1250 175630818 175630867
    0x3010b03010e0a050f1518100906050403080915160504081603050d02060c04090b011e080105101b0b0403020f060c1306020c010212030c040f140a0b0304051908 70
    0x2c900e01c200c2c1044800c0001d048a000c420000e412120044a803041c020100900b00c2000e280d00c801f1040d640c10400c0041030710007010000300380031017070700d80c108400203000030f490a0b0000b43c0e0180c0083d05c01c90300014038510119603214200559505c2041414549203038942044c2001000c000018040104004650b020b031000b016840480781fa5180080c0342907140e000040554001030104900c81e403515064400719507005801103403020340301004881c006807a0341ca40b81b40052588070610419402014181179600c1550501d50041d01c415062714462400c0b12411002c901040b00b0700d00051180d19010707081403190040711a00c0340f40d1202242004c0701180e21104800303000c60b6060b041140c001160000b02139600140180d0001280001e450b80700b14020f80c550000e00001141d1115150320442d401040b14003c40c0802640707515903003002c0381010004510030003406501041c2020103908880c06036600000405c12121009891005401c80d00700076280c01105100e034003054000c40f00085040304 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 175633318 1250 175632068 175632073
    0x90624090a052202030c070503031e0f071e030f0c02010b0109290c07080a0b0405060609040209040f080c030424080c0d051005220e071a0915040305060a060e150f03010b03010e 77
    0x2041803001100c3c620bc0140392010340c2d9060303000e00440681040d0185042100380010700348500688600764080d0048204500c405440c0081c42e810035581980601100e12003640c4042c07030165650384030b20040c568140070140c0788260240b90b01c2d807074246000600d103444000003901c11156131240c0c002d0408c04410030503245402802d04001c208441849003a03403203e801c0b41e49200354181500420040a0000d000801061604026609010f0780c03000740e442f019152000c41e0390720303500c0340f0101c00702881d032401c200b001c400c0824044010601400e440d502c5100042c0410381400180d016060103030030041d100040512200b036010810352624040660080c2c0c03500414030b801c110010061003150008021051650801b40c0144202400e102e4a5503080384165074a507140c4011b00000392143d03012501400c221000050000100100811081d118142680d420840566a620304008e030755030031140f82e1200d01a01c121181d0501c1c045c074403500f1511010b4000507901c290b07040440e003120f0362025043e4566 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 175634568 1250 175633318 175633351
    0xf0e0103030801050306010608060103091b06050405090108010b011b0c080a03030b13050c031302120609060906090319050c190b09010c0c11090624090a052202030c07050303 76
    0x150b0040321281c014103040e07000342141c0d031404200034004040645002c3c100358849410000740940c800000300351410178420050802e5983e00098100d03800b40c4103071402a6030b42000003404c0c80042c4076001e200300040c0c5841c00841410000184e01d410b2072003007141e80107845040480c03074240400440058500c00d0b20000b0341100c40000300182c0d22842302c1c402100b9800e05040202a0b04444107580d041144005d120580d02c4e0207100082c003043d500507071009203110312420030105110000b4514000d0094406072601502e408800c20f8883c0b280c0c044070104680740a07040302d07100d071240c07000b081c429030400140c0d003441c600414010011035604809844404070b00c4103105030f000c801e10414030180c98030709040c407003041765959441c1d0081d0070700e0080d48281c0780500001c00517112030601001c203205c01d0219000c140303401c078404100303078000c602c40c2c03406010340100224550805407480350704000481070b544203241c00420041c02030750000b05100c40c221014003040d0001401000518051140d8142001c00c2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 175635818 1250 175634568 175634573
    0x1b0304060318260c060a020a0e1e01180b0a0914011701030204020c030c030a050d11030105010203071502040b0409050105040c0503060a0306020a171302031006060f0c020a0f0e0103 79
    0x1d8800c08844180070003040720a0000090031540c1410440c041d01c00301c0c9650b90041211000c541c0130703660019009001d00300c20814849100e80c014240d105651701c400508101002c02e003c0180d81501e05100802940c2661a11560240403020480da800b180c82c0c14510313032a200c2d41030385a00890300c0e03803010540041007030040c5142802480140070081c6003200340e5140d041350078080f1050611002e070045030b0000c0d04040303441041c41143d0038125443c0440340d41e008442030092195010b9000184401d141031035001d43c1a05030380450b8121107050307000b0342c01c04626442d200e4549840c1164014051303820000064060201000340c0000d08480c1400100d40d171400040c001a16a280740c0502044420010022182c2d143c0c103c201c1035a8004100503180c0c946c135503041c2c5802d50940000400040050200b03d2140030301400564204d201b42d0555151072400f020300c40540310309006800100300a50303c1407622904c039050f180401d900040c03c8001c050b644054044400714580c0006010a1041006009 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 175637068 1250 175635818 175635821
    0x20030610020f030706090f0503070f06050c09132310060815060a1809050a0506030c030a200109030c090e12040303020319031b110c0909060402060307051b03040603 72
    0x4504a00e400501000c40810101c907407a0320541e43c00400310750b45c03103007070400703002504204001d4a6809400c4a079991954100b554145205810480384c5600304070000d442c0c1d084500680356402c0010703100502d00d10302c1e04440d0010b400c11044003045e545001400605001500c603559010700340208400b0409030030454010071922004080c1d061900582030040c003180c685404076400710071030385403000039035120b0440e15001c801240c4c0801030190520042c0250320300207500550103550102c04946081700560103150715030038a2500581607030011450f0f5511030360307280b8075461051014504081155201d5642c0c0b8031790340c0c1ca038002c80042691064010440e00d000c12000101101d0708034030605003031840c0e070000e5882c421580c83d00e000020112a01e6a1980030380c0140c0320041c0c031244a030007804100705005024503801055400d0034420401021030300c1c200212114027031740448001d08220b58407902800074035403014241404000c001c1160400e00c00b00520820b4000d400c3d40301543d600c6107013100090 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 175638318 1250 175637068 175637089
    0x1407050a030c021207020108220515130c0302040b0f03030c010204090b1f03020a03020403120e090a1404020d030203070c140102060604020f09120309060d06090e0a030f080a200306 79
    0x10341d801030b40703160400103400c0705503007071703168240ba00d031540343c2c1c0360b940901c40c1138580c036a42c0000d242010007000801c8000300d040e52840e0840c4200101d00ea44140c0c0c1c0d929241941f0380b02401403424586c082c0054240741e0400741c05104054420b4140c0c0e80d2640c0400d01d103901c0258034000c07a950118051014070403034014449500c4045526510f203840044401481c0c04100c5401c2c02419400505007502c00e0094059400860300034015071a55080840094443c4840000c82d0303104d5801000001d90380c0e02d4612402901100882d001d034403550ba160701340700d0110300304042507080d48001c4c0101f1700001c12610800018205601851854000b208000780c607240025007105d21482c014031107100c01ca2951020b4440300e410464100c0700c0c0c0e40d03031005903500b50300c6010302c8075400080000e0f052840d044250840012a114000d0800c403000f00b03000030075151840940024005a01440f80711541441440c655801952600300061039081c40702c0c04c054051145044042d92803004030400c0807500d4019101d4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 175639568 1250 175638318 175638341
    0x1602031e19030c02190c0308071a0f15040b04090803190b0f01050d0c0c061104080f010e0d0c1106040906080c0102070f062f06090f0307030905040f1407050a03 70
    0x203110300b81212030301039102d044072800c0780001e8002003a60700c06e00248556480046400040c41d9075110481d08160070b031429800e400d02411591440800c4132512a4081c092240d82c04820302c0e850300342c0c0c00c0100000313403886006090740035440d9021900440e110300d0041d40285e0301d0000403507800712001248070507112580441c510900c0c071030723840d0b1242c1e9800004540e21000b41010000303000d9800042075034840c00c13440000e00700310718142c0c03000844130040006000b03840c212407c80d0880d6049aa030300d400c1e920119025202034002c80c1400ca1481c0c0103801c03a00354103104d10246601c6070151004102c95401641c010500039440d40c00401405074103102ced035514070f1800e1000e40005402c1c883c08821550551190b4820815481000781401c2c0c1548520b800c1681e40e1103c0000e00c56000d643c0340c2e034a5405644100d16070083d0a482145a0400400c82d24400d51545803403115902c0d010401002f803c3d9015000c81058880000060948181407890300c5a483c588507240c4074a21858010100c0d9280f02e0758 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 175640818 1250 175639568 175639571
    0x408070602160b04270c02160503060103050a080a050f0d020301050f06031e09030d0504140706090609050609120604030f031d0a0204091e03050408010c0807081602031e1903 76
    0xf0311140d00000100c2e000d4a0032040c2e0109002d64580010f03490441c0c0c1c1c24800c0204d031800c8084214590f000c120002041d80800c0c000444a0700c440401d51540da0a1100800744d41c080402400020ba43c0700140005801c5030604da030034140122803101c0c999102c0121804c140742c4c0000140910710b8500210414050140da80500f980717006250b41d40011140c251000000d80c0100000d007031034200300201c9044081c41d400138802c504292915103d9200000001e40050050344d03c0440e1503032044058900f200d609503103941e000740ca841d0502c4102e512102130310760048003804200504080c1000007501a51180d03445a860300c11452008044038030b80212000320713081200f19070400d04400901105600d80441d00015081c04600d85040140c00110113484c44659401001051541000c0904100c844400090142a61030703141152500d9044441c00d020a4102002c00c02221a405041c140c031603850048a15200300300300004184ca1400b912401c1c90a80040ca20035880440c1c0c4810505080a080 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 175642068 1250 175640818 175640863
    0x10f050a020315090405070506040306020921031b07050d0506072a063207020c090f011e030501060b0d060506030106020c1219120e01020f0c04020c0c060408070602 72
    0x1c9150002d00d60b1145074404c41041d00803c05001090010300c0041100601840d6610f40c4c03450f009010750441c0e941e81c0d12580c041c0d40c207800e40c003a0301e4403021007203070424010b5445c100e51440f45001150046e81448914881c0b40340c0400c0329190410840c00f40c41c029801403105d458101c030300410f10480d210350f415504d4040104a0134000c91484030b01c2c150b9510400104005000340f0741e60310f01031300c0c40e955400081d42a008012482c03807418040c6005a009609840c0416080e80078400024029034110b161020060010001c452030140d2885e00f10b40d000ba020514542d80362501c9007900c1d031a40242c03a9500001030369600640941c8502d1009110548e10a0b05540c034001d03000c4e44500f55101c480c3d0280c1321001110344003140500c2003020164055146c0440e80b400c909000c52001d90344070009004c00d5141c00804c000350700001e49609034100300380041060b5072030a02440080d40000342c40303100ca40715802d00940c05030354070300c080c0000c1c201c480c0c01008602d02c1d0803402482c14503d2047c1c003005058400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 175643318 1250 175642068 175642081
    0x22503020607031d011112070819021818071815030b060c0607030c0801080c030d030c020a05060f07021212071d0301020d06050405090c09130303060b0408010f050a0203 74
    0xd625034890281c0c10005040c1007005a03000040c10140082074645d4130780f00314041100304981c05003000002030443e0441c1552101d0040e07501490030b031112403141255010f0101000455001000310700348a01c80c3e410000c2450000c99a600c40b9401c02c120414104c0301009040381d0302403000003844108105111286d460840450003400c14001d0000402d80c48038002c2403e0b803500d0003202d208102ca001250b13a5450305410082c02840390b225603c00150a00c800054003650028190304000300042c0a460b45201c054415001000d0540c900001e42c029220a000403d0040c403009100e400c8030344070340c0b0340c0d4a4284402403c2401c8294640340031311050001c0e800c012482946140e021841d4100303aa4031500074500c031000c20780004e200c07503850b42c00020081c42c3d8070500d800c820f08403902554180070503112a42c00715121056807a25a403c03004290014000700c070300100003d085802801c00040342a120101000c03030342d0098210489076074442c140d400300303007581d4400d15520418911045043d0305181 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 175644568 1250 175643318 175643323
    0x908040306150302130b0612090712030306081903020303070807090801020403080909060405012601142a04081b0a030803090f160e04020105030901060e01140a0902162004020d02250302 81
    0x205a54a0480351600061072708181040307428003401803032191807070843c0c4500d40107014003068012080d15005040c40140c0d820209107080d840c055164015500707541d200754044903960401080b0b201000042900007900100a10040001d140074071407465450880000740605000d0281076103020714905001040680c1000c6c0300541c18903500522003417460385c01815540035129020076a14000700b5142407110b07000b04040d100201014002c0c40c0a11804500c2d22180140140d01c1607003c640c0001c103420303640140c2c0c0121140c1d9140020604c1c48600d482c1e03250095560400c4482d107481d41d0208081550b440c204100017401a04514020003655040c03803c030301020b00026000a061080100200300c01d54029045100500b500c0c1c0c0c498001581d40b0b4150301c0d03c3d00642c0843c940176000d4035001060f40c2c44280225601c6d10010303862002d20340780c16a01ca000504920443e42184176501058207040e80d038030b000a0a0300380381c102d00543c4031010102c405009054403120400c0101075480340f0000243c02 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 175645818 1250 175644568 175644577
    0x6080f16080d080703020c0733120f02070b0412120b010c02150c010908040f0803030906071b08030406020417030702010806090a0605060d020304032a02040908040306150302130b06 79
    0x2d460000d60948440302d040d0701074021008075001d035010300d000115070041b075201d10030b48640366000c546800600001c0700e010b00701031140605001030181055840017131491381082203029910000186400101d4840c000c955106490850b101c5549440344c1c0d1041e83c0c002c2d004441c02400c5601000035030440000031304a210300c0f10000780075445510500c0e10b244209070a8076243e00560000340718108803407030002c249070310502030120303291800070010615210001c2a00d100340694801403005844800003610910381c505250901d20741c50359509030010b000c1c100550701551040070056144c03414203011329070001c0740d120115210f62082c07000c01c3c09070fa801390129070044400c2e41c0e0024a41c0343c0c0321020004e0030050300006d410000001d91680020444c2d40218400d074002d99400c0c62600318100107000001941c0461805402c2080c02c003409458540e00130500c892040c1c0780103260660301d0b601c0c0002c0c1d50a440c100000c046940b0701c200150f0815100c404104102d80c0c008100450301c010004200d03014 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 175647068 1250 175645818 175645843
    0x90e01030b06120d0f0f020706140d0e030f090a12020306150a08120304020a0e0103020a03171308030c0d0302031905100e0c0304050123071b0606080f1608 68
    0x81060105070381e910f03840c655110026286003940e1800310046005030000410440c9080010700c2160907441481c40460100195107450350b40c0c408500f85580b544240c2e070804501c02443d41d84c0c0e100740000c42c2408000400d062510050b07040c0e02c1e803104000300801041944e2000310200300b01c1e54400c1c016900440c003a03901400b0a8100441c0818100c0440d101840c16000022644a04050b4042c81c1c14444003031403240d8030840d806229682c541e0b61402080d50284802074000c0c01e45001840040c42d9903c24504070010315245e281044900c1c81524190606540800c0c01600001aa009188024131440c0310000301400d00b035140d41810b190f0118040988000c0a2501d0f030b440c0086111601c0d141400401800343d0301c50f000b60f07030801500c220500d90003070310101e68942c83c04420800c10305070346031203c11520f09a0300104040c0d07a00c500130388640451215418407005250759a500040051217103c002d89880d1000b4000c0107085030b1481d00d00014a4201c100007000c40c1400c01040d1400200c0c4a03a804 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 175648318 1250 175647068 175647083
    0xa0b010501081e041a0c041412120d09060c091806080606060a05040e01090203180a02090a0902011b03090f050114090f0a1d070306090203040309031e0611090f01090e0103 75
    0x2d0751800c00c2402000f4a001e040348094805c014071421108800c064401d540f145078000c204050401c1c00c2003125001c1d0160b02d1903940006e500406040c0c1d80002800c0055190b00c00482c09158a42e640d1049843c07010031980401d011f40d40074081030640c1d111880b180017074000704002d0642004080c13a40c0383e02c02031800d48601d0b0005001c84000c1e21803001e49004200350704100a095031103a00e9600a0741040340c3c08d0350766a000800c1c95808000014644c1d0300c61760058513201c1c19484410781071025201c1c502c4180d05104c034034035040340c0d250010058145e103540269a4020344600b80075200e40038150340d502c400c8c104051080b403007424081d16030894010940803102411a46401c202240401d4402d40c400c04054500148404181d440b1800103482004680d0b402c214142e2640741100490100340c0f406000102458010310010340440391602e182c1c603207010b2901c0303080d0791540c0340425607425030a54075003214086822880c0d03003007044401900300e00909200c0b6200d0b00f05480761000010502c405404034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 175649568 1250 175648318 175648321
    0xe0601050c070f030215130b090406050d0f020108090109020901091a0a0603090204060506070f170405060d06081203040203061605071406040218010506070807050c060c0a0b010501081e 81
    0x5a000d03030211078554003404256016503683c0c48100710300759003600c005d0340500c071181522544071140c10300711005070950810004a4a0174000c044c0000e4202140d001d4006981e0035010035955104c4550507029441601140140e001034400140701d600080c00c4105140c1c14804000016074070103c110341521200c41c80040c00034030304401070032054101482203400000070500880c00a600d034114000301030090f501800080d907a1b0041c020544030700b45000e040408000c034044001004d02c14610051181951030509241c1c944000038003d91003c0b88440900c2c0c0d0b59441008010300a000e42e2072203103504402d080c10f6252a8000c00e40b91359004091403a8a0407642080c0070441c00360083d6079020b900414168610362968038601d40d03541043c0c805900ca40c9040d10040c1c1083d01180383e96050354006400d0324102545030303407102d8458000d94000c5800c0d010f403c8907803420f03031501c00c060104025040010204406103082c510041380040c0c000904109545c2d080040c0030300010a8103541819404020025 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 175650818 1250 175649568 175649581
    0x1f0c170405070909081207080106080c180a090b0a0f061e09120b07110f0c04020a0e0d1208010b0703020c100c0212100b01030905102f120a150e 63
    0x80c45007a403c00d0390b04a1030108420b040c0301c6614007501e400200490f0300803141c0c44110040c0c40c61102480340c000000c802100007044800d08502030601c1148202c00040800d00402c0000c41181c0f858026480e0503a0b144140c400618010941c9402002281182c0222508214000700900c11041150384003102111420b6030942c4990003081c010000c100c05801b01c0c00040c5000c004100f401d55440c40090403c0888040300040403440150380300b9000300900f10707240c459007440f002c0c5d01b0500c0b80d4824403200360a0203c1a844614001246070700c50311402171a4400820013400520040e0450307610001c05006000c0066000503811031707030003000c07a221380034000d007120102d83d8047c45040080d0080d0900080c1c0141540000300e0300483d05502c02c0c02c0c001244108011030480703250350703805800b6600800340c02c0a03840b419401f502000030b400c940c1d40301d00420f200c0e01c140351401c00100411252800151032030204035070440d4980003000402d0501070000e101d408400c4004450080300140701c03a20010404 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 175652068 1250 175650818 175650823
    0x306060a0315090e06060f01030509100e0c041803031506080103080d24030c1a0415020a0f03020d09060309050303040201030e0102130311090106050a080f0606070807051f0c170405 79
    0x1008400d2050104c1054140e040340c5407078041c1c443c1d5018006001d070300300c007640c000d020b8a88640f40c1c0900600c040700300c1e40c00391000b40644400e102203074007505a80d0701d8180c80c3d81c0140b000080004105940c0036825240082c00c40e084080603404040003036205020903079100d0800e1781140e410044194031061b04d10529801002c41c81018200d00c0040080c800c8440a51244107084a008442440300999101002e6030090049258000c295004200030301aa07502c20400d0311106c2c03261302c12110249000d9840000031100b2240640c056404201d00385d0703940d40c1c00001c10001e010149070a01a11400340d844554030f000c0034000031705050f00c4101800c012842541510541c2c45104c45186c1103660740e042c600340100c1040c500e540a520582d0000c55418024021500c0ea8030035607850090903580c0d200c24441c098000b0b0800c80d40032070100524000300728000c001d08903090241e0007070b05404451240001c0702052034800155198181002510740c0d9030410b20340300002d0b0f8291080c02680d47c40746402030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 175653318 1250 175652068 175652111
    0x120b0106020607120b0a150c06060b0405032a0d0503040915060906050304030c08030a0603050c0f03031213050601061d1e0103111201030f1b030c0506090105120106020f0705060306060a03 82
    0x3585640c400d87c200001552060140c060306015520030002e9580b91050043c040c8594000d0303c1d01581701401c107060038401804000303001d901e248201c2d07125403c024001440c2840818061b41c540d40b000c5030a0145c0c0c0c2c484e11a0300e16003040c152040740c1a6103000d00140030907405205410a100b40800081c0905006208602d8007aa00c080016503a280501600008100500064445100c0c40200c0425030501c032903201c0e29002c004004605240c1040100890050300410141c1c2111004241900003041005180d010703004a40b50f42203800ca42800c02c0314118441510b10348209000c3d00140380601c244880502c41010a180104101800e03403c2c00c295841485a40c180f986251000001403103451400c00490612521202c2044102480c0790b0307035183d42d01d000103045003841c1407082046103001c2c00108400741d0181845800d0142d20001e03000142000da20803400340c6c1040c60f800c840440e050220001518040769903d0440c02e20202046c035074011a04d0550900d5911f03004046540e00309205003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 175654568 1250 175653318 175653329
    0x30702030c0703030306170601211505040803041a040b011a0405280b070803010e0a0b04090b060a091e0b0402120901150b03010e040f02010e0a120b0106020607120b0a 73
    0x1d840c415070f00d14000700200308a02c5041e0403030310380d1203202142100c00306529048a400f1400502881954100348462002c0140100d411800d08005801c100006003e217500c954064140e46440f45030500346282d100c101610207416051480d801c0100180d056580303181581c43c05142002807100b5040d0f24040c510681c1c11840e40404c598001c5480c609040101d20800380b503801d01001840e64610840350715000312540181900d5003400140080c0c140c010131203601c80041c0364040703102121007001c2021900303810000d440e075060050070000c2c1030034441c41480061054a00410005005001005111500c0d0902036141c82c0c482100711001e5680784c050b43c2003c0f4280000c040d550038500d4019000b080410441e2240012101000441c0264007050728100da821070b0900c03056a0711941c895241d0f0301d036500124184554003051107120b860300c0b0b1904018201c80d07a203000ca0010744e400d001d0380403c4140c2c4076000710f41c0030300104000c2d10381c048002d403003161405101103112505039001409604094200 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 175655818 1250 175654568 175654573
    0x603011517070f0f03060b151803070611070603050411090f010e070e01090b0d1b1d03030a0c080c0a050d0801180c140702040b060708070210111002030702030c 70
    0x2103081e032414003940c845007500400310380c407059803412812104040380c40b410680d149134140c10800310b050364014001110004050300344011400b0020021030b040348219004103a0400c050101c0b0f41400c01081e4060411800c040d042604d182210b16696405401503a040585074030100d8108131011180324208000100743d00c80624207414091082c5500348a40c2d1050461540800e000c1800b50100603030925041e501c0c41e0b0900e0600400150030703800074806e00411035580302085200004015286c500801c160b5541c801c3c0344110b43c1d050071014200e01031034825042040180c2010750050600740c43d2a5000f01060307200c00c180c0340c805042c1118201d002d8141d005d4801070946440d84641c0c500d050b1307803190f0a5400c1006074907071a0b40481d104200c01001103068096074400544280b0041c1a00ca071000300040b8000689074013084035904400700c00c546500010601400710310f002d80c10000024842d2401407520249280d0041c0d9455602400e206529400000b18190a10074803c44190704100801c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 175657068 1250 175655818 175655861
    0xc0306040f0b0603250f0903230a06060504062124020412020a080d020d0e0402040f150305090610050603060a08060709030c062c040209030706031a0d030215060301 72
    0x111115580110503060b005e01441018113451540698114807030504aa0348100e407050441e540e900c2aa04c00150100d010b5580c8074031441c980404200102c4580d00c520f0010809600e858148002c1d20450b40002d01c1d40b40d015490030020300c1c049070400c0c0c506604015101d000f000d146441462100c1d280d46851f98050001a000c9610340500030141e08851080d1446064144d0b01e13021a62100d11007802940160400d038031a03400140f0400c01a070040c18010b10040c039040da203641d03404910100360301c50b00c02e5882540c403520700260180b05003940141d140d80a41243d00e04101121481c1c1014003410b4811080440422565220058810042c000900466400f0300303240d03402810a81091104680d542612074003c078001e13100316a01099000400145401c03040136000c0091840c440c5600c903074015500f070020b08495a410840440189105d840020312074608100782030744443c0f481d51580c020f0340c1e003100250029038001810300c0d0702040c2ca440b1001980b41c0000081c054448a0075241c8920200744 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 175658318 1250 175657068 175657081
    0x6050f180d050c0a0b0702010c0201030b15072a05030613060603020405090a0605060a08120f07061803021c05091e040c05090120030304080304080408030f09180c0306040f0b0603 78
    0x3c2a5284540444820207001d540320403c0010788070b8420000c3c0041c2e0101c10720001540a50440311041000821030407090340001074900c00c5800400040d1042c03a0a4185011044043e2a1071004c040401c5140300c1c09504001c0481d40d2210b0141c0141070020080e501101400b2555000710b0207151b005006100310d0420041d400d603681d80b803280580b005498140401d10070f16100c0c40701011a450304000e040c166843c441c03001d40b00d400002d00001c60050812038840014120303c1002550905000c3c1d00340c07444642d090091920040d80c014072a201011584182410b030410b068440d01c2c0c2d03013240e1f8400003001d5805d4031034482c1c0134000190b81182c01c1000c240e6645410001400c05007400b0791311140c1943c401c1002e414070091003c00b00c00c054108001140104800324001c5501074044e00c4002e180907500c485061440d0b102410b100c480e01c8000c100c1c0149881c0000c40b151030013030030b0392100c001402d26021480051001624552241d41c0e203440303540900341c40e034002040f2064010041a181d26120 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 175659568 1250 175658318 175658323
    0x801110301050103150f17010e01020c01090c09020a080a020a03090606060f030b040614090402120a03050301050405160207090b0a0509011d010f35030705010608100606050f180d05 79
    0xa000b86400300c0d0604044591004d11464000112401d0140440003035203410000c08118203081030f0080c0300c0d501c40f210910300607001d00041000d20803860000811101a060440c00b00d0f031207070000443d1318010000340070f44075846003645420000ca0b190059455501610035001800c10481c010502400c0c40c1d03000039456048508200c1c036020301e490074041659900200400c6504074004c00030301c01801080f41405040031048070741d10500c091f10480d0300080d0840f0240c0783c89490a011000960000014001c40c10f03d405040d4000d406540072003000c80e14801d02070b403100a10701404030496540c0503180400c0ea00c94896400a00b0098180d080c1540c44200d0b4400780503011080040d4010000c1c00003a0b100410f01c5214120b698151002e07a80312480035403a49400e0719540f8035404060021a8812034000510007482424495000010790320b180040d801c2c00d0403003a880144282d8a0000300700040c980100072a211800c21015040e90754a4141500d41551032808506800c010001e940d0010040c00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 175660818 1250 175659568 175659571
    0x11090d050105070905060c03030406020d060302130c0e0108010806060d05101508070b03041e0503040504020d021801020105061011070b030103050a060e0d090506031803030703020a1d010f08070908011103 89
    0x15588081105440e00140302d11b40c80307100c8a040c403642c030800000d0b020032056405024241e1015101044565480e000243d05640c18038043d4200d40c0e540d42c5211080342c200440c1040703840c080c00c0030b00b6103615025000381c171080000c05840c014940f10920100b0808248400c01e20081d080c00c0400c14000407000180320802d49016501c164818032401266415040301601d200d00c1e403110002c003450791301e001d45064984407604111100e20041c00301090b03543c0c1d02c1c0082c1c040200416030040e102c443c0000300c141c021000d0101141035900d444113020a03925110a25010180c41d41000c04c07816200c00340e00c42c030b400b0059000c2d0381e1031403000c4000710070400d02040300c1070100d000d10028004403080f8141c1945034804ea0b8180008079141940800180c24224059503100b030162248503141a107a10649040d98012a0003c002a41c0016010145c580060f2020100c100328858507022510a81c0084d00301c0c9540c651407018801c2c0034002510b650b2040d481800644088802400004a05143e40d04240c10 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 175662068 1250 175660818 175660831
    0x140706180501050901141e0601110a0c09021206040e060a0e0a0203011d0f01050f060d140109230601031a04140d05070c090e331e01060f02030d11090d050105 69
    0x4000228109000d0032410680b2200380b070111041923100d00b0015110020107401e4000140201d20030f07000401c090f035004c1c800070118201c015980c1c5100544151008a000b441a80701d80e05c2c02807660403c01d400520540d001650304000204c09071181d11040c944403040100a50641c02c001e9107004851078642549c3d403900002c011075006c1a185c5100e24207888046918100c140103010004080749400c801c2c1d0b120f0617000c1c04044c03d1041c0514589170035550031b0301c01030b00c00d50905e1449000d8120071f00c207125100d41e03222014041950556a4030030200e4107002010203551041c00102d02441b05100c00c4494601d030550460383c00304609807000d0203030f400001069824040c182c02c00905c03a041401034110864020000d064002070a022a150020340401045045100d21504007403000c00d01400600580d0f55544501c8100c0540c443c000081130140c101a04105403200740c80119500002070340e20305000100049508000e03a080040c3c240642c400440d40320390001c02410078000d0643c04907010304c2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 175663318 1250 175662068 175662101
    0x6030213061a04060e011404080607020606030d020a033f0506032b0c11031905190b041e060f140f0712020913090308070201050601140706180501050901 67
    0x7a5510b0380d42003402107104610203d80d8100400c17002d90720950a11602c40344280d012030500e40c940707038410728080b0201c40c000c000d680040c09010701e41c45c08014240880110f0300c01818142010b0b50000c1640c0c82c9071b070302884086c001c00020b4004620070b1004100e120400f044002800d41d2500c0b0420207051b00741d034030758028010381400d1190b00c24100b10720031014100003001881c11401d11022121214403203000c0d181800c1e19941c080c0c0c0c507034082c00304a01101c18040e5211901125051290403c42030010141c0741c14203062403100024030103c18030b6481500100d000038007a805001542c0c80c03401054005000320729250b43c1d0790060507203038030460241c400b0400c4032141d07035190815200c040341c1c20344080307001c03070000c1041781401c00c080e0300100a01c0201400c1c00c0c1c1d0340710306100d400058915503e030071000700d09118100b0084541c2407140315840b5000b403804184001114100030214420351901034403160300d500a00050b4a8202a038200310340d8404020443e40c9049102e0b5402006031a58581150 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 175664568 1250 175663318 175663349
    0xa0609020f1b010b0616030201090b01080304030201080c1e0a09030506180f0706120e0708150f07030515040509010207020919060b0c0d08180f0601050109050103200d0603021306 78
    0x400d81481613501603200a0f050b030b0716003800e808070081d0504410301d085045648412501c400580c44584090080c00b01070011030f181e034290b1001500e00880200700032a5005d0030702690f510705094100100703c0d01840c4040c6a656628100c04490b4412260401b40c0765208047c00c4c4100c60a0132068120601403800589041c400303000f400f242c0310315891240d50b00280c29101501c02c2c04140350700018115152070b003114000c1b03070386450f014281a00041402c40001a1508100c0c0fa00048956280d00050301e00d003c00072072821000e031011160348c0c241c07114000c980d0b0f0000103482002c254100c451440e0024422213080c9020f040c4042c41d0b010160350510841e08044000440e26440f0003a550409025406026101108081100c182d40010100c09030b920155000c0c81402005000c0c218411840d480988125814040050b0440c0c22030352000d4109441d2018011078421400c0200341030307000302c0000c940e03500d0b034806480019103c55000a50b01000210a1850032086507000700100d910b52003951810 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 175665818 1250 175664568 175664617
    0x405030d020c07090605010201090b06041509090f050d080403090b070305040806150a060e0a0308070f0b0c0a080c0702100806130c0201021306030506060d051e07030b010e06040810050a0609020f 85
    0x9071070414ae0010110b0303590102242c40341c038040d0484080c40c4c0c03401c10200d0780700c2c0e07a07110441d06480609400340c8010405540a10910100707000a100665103410810074509090f41c005111302d03100e01c13803030301c0c41d40002c5a51300030540b02e0f030102c8000341400070407903409042c186070100308401140040c602c10051403000007a20342c0105000d04a1102c000c00010480e45982c82d0380780c0c40d9105140881e69899203d2915000820094899019490708032595032903810061001e440010043c0c42c214104006000c6080140c0d00c00d075a1041e1780e40540b5221540d603c6008c0803d04401c0401480010203040c6282e04100c0c0d035056019016020025668200350f075031b51402030302192401d503034103500000108001c021044003504255048140142c103554071964054403514039010940349500002c1e101c4d200c1c2c041541e80100310320700022080728111319092811040c0b035a140c5401e10900b00301900e4000260300281503034032110061040d1641075540d40c01a60b494260f070741c0b00c06024010307444401460550b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 175667068 1250 175665818 175665821
    0x11070321120509030403060b2716050414010e03070503060a0905060c03010303090303050717040b07020f0301051504090c05030a060507080c13030b040206070c0b030702010e0a0c0501080405030d020c07090605010201 94
    0xd003a0940213545480d0071603ca40740940b28103a40c8507004004480100100c0001c00c08240e13814900c2c6000405c0c43c06d160580c0740c44d0f0000000304808000c030500060107101d4140828a4800400342003924502c0344181c0428200303140b0341d0105516004450401210784a140c003c40b05c12481041134410654503005004003a000030300000e0000342e482d680074400640104010118075004804a04081d80404500c0140b98013640050b5611200032815000b141000010442050b078101c0091103070f031900030409140e640410144a214503100d011040501040f401013201800018043e1035060980d070034040050901074685c000050f0090002840c401d01c0d540a03989000004d00c4c0314481c2c45e00e0741e112480740c140c003c0c10981e0b201c02e04002010000d8200c803184802403070340044040d00c5e40b500e00d201074210381750080f50404580040c03410500042c1550045001d482c02406c2c1481c0c141c5550408602e180154103050034554070000e0841e5240300005015012100d1824041c0031044d01da000490 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 175668318 1250 175667068 175667071
    0x2009040e0a0803011517011206050c18040c0e03010213030b0f0c0316030e0d0207080c0a030803060405181b030c0109080d0309140a06021201050a05010c03110703211205 74
    0x400040c2d0510041c01001c0500b580c01d02d186140f4502014210800710030020064400e030b001008000302000c12000708869406110340c0110302000c05401d00210000c80c100d626031003100b07144101d03944c001c0c1480090240f0550559010060002c41d2a03080d440c0c8040c180c544d090100761128010300b80000d2140c00005626446100074602c0641140c54200b50000ca12080300700020515468148818014104008400c85218142c1c01401883d02d0811501e040c8221068441d0107400b00000500206603110b040b43e0304101d00340d030700281e1661242084049100000c40010141c02160701100b044511882c0c0024081001c4040d103101e14041c0d00155a0002d4030300c26245c55400c9070b0300604a2502a07403068404902510b4207052210342c2c0014503040a010307000c22105588e02286001d0a1308544150501405094030840300c843d0420001030705000c1d01840060030030a04100040c40d56005018080040d07070310518001d502d00e1011a070604450b900491140054403040c03031070b80b2207d00d038020345 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 175669568 1250 175668318 175668323
    0x50c010f0b181b12070807020f0d12110301030f0b07020a0209011716091413030503010b07140a030306051002010603021e010201090c08010203060307091109132009040e0a 75
    0x100116201d201804416070000380000d4004650700d00d040f103402d00c0e51000b001c02c00b0b5031800311a0035141036074024003110700180900045502280b00c0300e010f07003000251044050814240044400700c2c1a840d00c0280004290007100054048000800c200380d5403502d048151040315240301c90760340c8103003c9942e5030740124041d40c001300c40c500400140385101e07245e4000740070b810107492701c440001e050000f50320403661011265560300e00070910b51101c0a02d0554010390903d42100d0798100e242c134010010f00040c02445009540020b80700b04114a0b40c0122031103040720320540d14015401c3c01c002e40100f04610405000304170703041041c1c204501c18805c20042c0e03035000b45000c4040d448a03204540d058071060126066640c2c68066501064100381000000d05507c00003581c0d92034540306050030030318168403a0000d0b03424202000301f010848019100d0007031042c0e8615082c0c201c02120302c005800341072000c405100d004840000700015030002001c0014044d40c091114000058100c2d0742c440300450003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 175670818 1250 175669568 175669579
    0x90b010804080d020702190602010c020c03031806041e061d0d06020a0513030c06020d0206040c090c05070602031e130b01120201090f0803030403020607050c060a0e0319050c010f0b 79
    0xc0c00142e0580b020b02645070003010014140708695002c1040f81450408011019201010402000d582402000c40300d111600c0500028070411010a0762400b81c1c0300c0e11451800c1c41e00c0303501e52580380c1e10306440080c031300b0710303c841d00e0751402443d60800b0688038015000000e414808020346400840c032010102880a01a0702c07014005464840c000d40050403d042045001c1090100c0d0200044440016600400d4501c40c0c1e64a0004e0180c44e0425400701201550016000c1202140c03c100c0d480003280c0c41c202003c1540c003c0b80700f04582034840c0803001800184044280108400c4103680d110111003250402d54180d04d620143c0c1d00301441c43d41000b000008080300510510100e11042420584181400304aa80d00c822110408031800c5c0c101940e90343c404420882407580c10482a50007030401d0600a141003800060192030381d80081030f0400c03413a00c0e05440d1801c0c51042088426002112502d1740a68071900030003017441d8413030210399001d982009605502c00e12644214400507070300504 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 175672068 1250 175670818 175670821
    0x2071101030218040c20100b03060903041a0d02070b151e0f0406080715120204060c0f05120c03040305012417030c01050f07020f010504081b1c0306050109090b0108 72
    0x1300001317058900c2030181007081c516002c0e01140c04030740c0084050141c0c90301610610303411405500c11104054120345c429400841809484000401214156035810000c00c0081d41c00c445c0090b2244500b940744a1401e1000412078144811103d8240c05071000c0384e80c503102c6840d04ca04100e00c2c40c10075420380c13180000300e6104003018604540c0f45201490080c101068099486801604000540e8000380004803d80700550010368000e1038008044407540007142401d040500062075116241c10003003690b2041703c810b8013400000c111003040c0000e00d0100590700d500406003540c49801a00c170031a8507600b8007401c140b01036040c0c81c000d181201c004402c0070070245048218a001903482901d0b001500041200c10054002805590311405443d01c51a515090003003000b4a0003155120b010410303490300040c04000f946800440310000140040d03000017003c07811403503040035044201056507000080d030700000c1039019000001169802d80342d05e10366680c4e50101000352800810355500080d1840b0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 175673318 1250 175672068 175672117
    0x20607170f3a020c07051e03060a0207111215040309060e0301061401081b0309060118150e0603010609051005030d110316030e0d1401051803070b150306010603020711010302 76
    0x107000c3e003449100c035030450b21179968410100710003090b195005805101c20003617003021401c04200e0150008815102140b4048035901e802d24400f1055120600c41d04842506c1c0da0010010014142c200b00d80305810082d03810b140c074024100038550710910303021401900c8c0106880c903041c82000c00702c4000260342d10740f5101d03903801110741c2d10005000c41204020942045601d00c2c000001e036209225001c0246400c0d410a003070a011032403210310180b1010700f0035101005449000413a81c04440740c0480c0d1805c036440ea075001a000d0403841d0400e01041d8504010840c002080310341e414101c903000e8040d03900d41e04c203044040300d4aa00c07080010205600420140c0741588112800d21441d0340070b49001d08100d8030700c1e00014490308400505842c500e608544041c82c08000780b2840303030070020002841c401c00802c200125203d000316100641641c403200c000424082d00c2c40100503441c20024160781c0d2642c1c4807039000d002500310b040250307040001801e0054a0394081d2007103030122402c00303480703d51003454007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 175674568 1250 175673318 175673321
    0x9080301031e0506090d0e22110c0f0a1101110607080402060f0a12060603020a0f0e18011502070f050a050d150c03020705060a09020607020607170f3a 66
    0x34150342d107404450741d024400310b841400000d00541000b1701070580b400c0c00c00c00081210200c40d49081c414030088400e44110300d0100e105007004c0c0ea40210200f50703060f01c00c0300002c603070080d0b06214041e40180f46211404a0002c500039450341e103e017400d80016003a82c0c1c0111481e40c0f0009a042055200e540480d404a00601607941d00030702c01040c2502d00f01c0003d0444020707400403500e0300b0221b0f01a1011001420a0b4082c07100503020310b140842c280545003800402c811f17444e103000e0080c4505482c0d40d48181e110f000d8000c21035221805110304950b501c00c40c00d100e80c1c4482e48003500501610202098408010a82408403400241001d04682c1050100015860039a00842d840503083c0382c0030315034003418092340542c8880c40e24010b0f2900210308007941056030080c446c800c03561804036285c0041c0d0b210805d80e00c03e5901541c50366150010751401040a100300c0c100c5c0780031a0350105102444100280041016501203502c8101204203801607802d40b12b0300c5481c03000040d48505040074900c509 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 175675818 1250 175674568 175674593
    0x70c0b03090a050a030c03020606090411040c0309020409121403060306060405070c14031e03061509011103070f060e0f0606060a03060f090e1504031b1502121602010908030103 77
    0x608280c1d07001960700da84062800051311070850201d503451100909154062001c00c3d4401c03820381d0805068034003982da008500c0c0c100301055216555411030b49004070f03c030780d220010042d8054020001e801c007904004603540104590440000c0110b0741e40c14134907502200f920b010320005002010315440c0c2004100280500030303e0002040396050b11407000c640081c18292204d618040a141d4820800c960021402003010050800600400501015840e0043d8850300217210303103501625541e1140040302d1030b50b1066902e0b02c06c0d1201040d0030702031110210014501510481d801c12130083c880104a40320800e10840340842d0b000300000402504003080101103802d424940010429150800d2108080a50300001c0e20300b40d0321070382011510340420164000d4031083c1260030035841c055400400c200c071082007182031201407101c00c1c1c0070008010071b60709071070725004801d40d111060a11001c100120031140c4011215202000685450043c454001308641101c10185541e007152145841c83d01c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 175677068 1250 175675818 175675831
    0x9011a120a0219120e011418071e05040b12031209010609140f0106030b2215080114010e01060c080304020d020402031003060c050a0909050907050301020d0f11070c0b03 74
    0x2003c010038881111007002c000c0c91809143c9074405801c0303c880404040340c403070306501c2c0d685d03030300d482845074076800680c3c2603036440b100e09240d8184d034245074500345040800380e500814120309008905c0c20380407101e40491090b030700152001c000354440d8030100a10300c100c40214007030a070010400c07180e81d0035500182550040151001103511a07568540d4011186d03416482d0400e801450148900c4588103458140180142e140074806852801c0c00903d00d4401615000460912014a010340c02d41076088011000c000d101d080382d52650322040b0b1406003402840100c003000c2481c0001c505218011203331811307a8150b41c0c415210360070650769290380394000f810903640510312908000c0107950710300065104090843d6540200d41c0303103107000000d440c5029a03070410704c02c050013a581c120f41d0084840003217941c28040400d841d00c0b98000c1034203010240e0000c0340c1650002491840c0c400080d0002c1c0b4030303100650f80400010881c460001080e014810000300212039040c400c02501303035001c020307582185 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 175678318 1250 175677068 175677071
    0x30d050a1d0907020307060b061305010f03091e05010507031e0903140d2702060d0c1803080307020f0601050a030227090105042a051e06041409011a120a 67
    0x102007400980e041e241251a07400691000440f981007041070b00070000c0e0100103560b00c604000080244502ca44414007889040022803e10000001d1107500490886500040900b4007c01c45003101c611409040d101602c5940c204408647c0315482441010a8008062118009244e075a400c00b405000e60f0b050940c100680b82c40c004003011940e200402c4440c1c210303500040c24031340c0640060001e550312080701a2600411501e0405615804d0454440c0b4241c1c50000408103142001074441101c9030021a80840840201004111160300294050101d41d000c0710000d0303028407445507854209004003608048017807010401400c1c41c00c44c482c4010300e14003203001d6013001d440502804040444031560942c0d103d5003804240607500082850240780c5010b0b80e0321505c1101e1007800b40c007030203200d003d00039162502c1d80c00d21000b0b01d80c5105807046000b800c86030b5071680c40801030121406184014410214000005255081000c110b01c0d4115100785103070800000c9580c0ca0548000100000f0545 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 175679568 1250 175678318 175678367
    0x10806090705031b0c031b06100303081008010f0c0e0f010c320309040609060b030f070e030d11010516080403050313060207060c0801050406050d06020f07080a0206040b06030d050a 79
    0x19070181c001c0c045245c0180002d42e103c112000a502640d07940440e451500c2c0c010509000e40b10042d881d5aa040d260541410f9181d9107920904108201042c1e0001c9a55442c0c94421801c0c0445c0307402080821000d541e503403404070105020010502079808105011078a20780780031000a6001e962008013000002c1e201c1303d00f04650055004070300d44000e000060b900001032100c0703949010300c0307410003801808004001c0c05041c021255000c0c440508140ca160b0072035000603000d0741c4980b4181c0b00181003d815126a00da05210150400240f011280c080d5401d000c0080c00360000009120302d13060b029034846c81c0307a803910703201644c00703500c090400000703041d1020300c0360007250b010b000902040b885000005503120039548028940e010603000a4070442c00d18500304a556101e40d00208c1d565080f01d0b0042e03484089001d41580b51041007001000e210020405041103034021078206d20a5000e00040c60503a0744920400d0303241c2d0406070404012540502c4844040b52280f10410842d001c51000700080 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 175680818 1250 175679568 175679611
    0x1106090c01030e0c150301080f15130f02060a3203040209090705090403080118060f17010f0609050103051b0d29090c01020c0a030506010501050906070f030206041101080609070503 79
    0xc0300f8221120071700d0071030000010810403008010128425040b6000740403034400c1203410b26010f80016010a030b0005c0c4519140c418801492501c00e401c6038002c8c00386543d10f44804000d0800c4d1146400c0950782514084042844900c0030002c0da070320900402e5446c41d5175926820866101c001a10040c01840351503404183d9464140c2864011800b90b141d812b169803416581d001c1e000c105030784001eaa1030600808015246001041c982522025034141c040c00c0035003804070380140781120800740d41d14105600082d03281120752009060320b0055080c4c880811042c03900d25000c001c40403415400092101c800e4010466541e5111505514000f214203901c540c81260501d020044d900580301d41c1040c80e01003003e680420212034104800d965040c00503165441d07039130710b8010500c40c2d01c4c140440002c9411007603072050100c60285510803401c45201c2818100203607903a8089600b100c0e401d000c40300c0c0c00d50f19030080c0c078454850b103002041d0218617a00c40e0401ca940b40c1026203105031103901581c0002d01d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 175682068 1250 175680818 175680829
    0x1b030406030516021c0f0509090c070204050714030f0a02090306040311011b0518030c060a02010b01080a021611040b2e03020310060804050c09010602010b011106090c01030e0c 77
    0x10465035a01154904041d80f220088607811412003080d94400c0c101814031001d02c207214034070b40e801d070704010007004902c3c0d106940a00c940c1c0320650b4080551400c0054040000020307040c054001c1d1020410369507201025102148908601c1840101c103000144180420b00c411940c031444210025080802d1400413038a840000d440460114002040706d02004c1d80911443c1051881c03000c500044541002c8003070281d00c07915090a40082c880c680100c1252420010316a0350500604195500d00411720300a009281c00503950340050714400104020319850700980d4400080454031a00405950781d4070070b00d0249000c3c801d0b400585070b4181100a50f9400c3d803008203107000340002a4000e42c0c03205a41f10140341c40f50502c080c1481070003403001112030106900c0a03181503003020f144030b4440e8204917107000500700c95968844054400032a1181d070641001d090310800380c032400350701c040000d1003d88400d0115280d0540e5401800502907030361103a00403418455400707041d6040c841d01d5001065 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 175683318 1250 175682068 175682077
    0x9020907030203090c0a0b070f060603080408030406030e0a1e020a230a051e1e0d030906020c040b01050f070305040819150204030302120c030c010516030b06070f0204021b03 76
    0x82680802008082042840101d030907900c22144c1d000c800e4202a80c1f144103001302c44015040103426034180e002c12900d540a4806140c102c034040e81c4a642d900c0520303590307a0290180b83c00213420803412004840b0002807178100c50350b11411941d540c1350002102c0c003104082e202c2c2640d105089210000d103c4600982500e007030b854020b5003000000a40040c400300da00190700c4a4022101406158607040010881802c21a001c0b2071214019440320080c00c0008800c80707005903c58000d1404104154100319410202c3e08150203450290300140108403c0703940d000003d40c003140003000303100e042a0199000b0300ca4240300341171090401b600d076001103207402c6103600e1443e05030a1102c072080c1070244d100180010083c045105618081c11542e0081d02c846060b8180088104042050100a4424012703a20104002e0008201c41e24144444070a2a072421b584200400d11f0601542271f04e0501004643d00142c0104910480b4507080d0309010084d80f05070000e4409070503002000150820510050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 175684568 1250 175683318 175683331
    0xd050c1005190207051507080d1404032706050c0703050a0b041a011206020307050d0f05150a0620070e130c21140f010e0a050d080c1903090209 63
    0x6500e4825100500b0400b00c0b10808240542d40b00340d4040040da6074032103020200300e091045440e190402450118810b005810200c5013041c1045401d035400c02c20302e42a81e02c241e020345d90701480d40c90300c0036128004012540c0c0310300c14104642820300c00a40070750001c000303507030141c400c5840326030703407074544034185964208102c1e18071500300240414011080c1c0402c200300c8a415410b1865403421048010110042100410345c0b6000b0002403c4580202e081d5000d20340d0f502400d104217400e9800e2107005003022035202064410021411403542080d4241c1c006880482e120300d24010080c50713002c0320311652000b803d0078034802d20901003a00f01901000c1401110184585034102a1170701c1c01040c520859000102d60000355554550300da00041e058174003058000d00301c1950010048645820002c2900c0e40e0912582401c001503d40300c40041c0d00c0c0b030840e010b2010f0f6001c540044e9421240320b03030142e4400d0742c19041031080741d12084007285013100e159518180010b00590907404070319120000c5500 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 175685818 1250 175684568 175684577
    0x110a0305030301261b01030207170a0206010b2d0405040e0d08070315050d0606080316020415080a15090b1003150b090118140c130905060f0d050c10 65
    0x4000c1040301a500c03420007139100981103c803200500c00b803035a03001c02e09286488942c1100320503a003039000740d0464100b0350300540d01d0032000404840e824010f6001c20381d140300510071100000303043d44e03d01c8240c41d28070007100085441c2d4102e4094010101d010308100154030402000002615959481200940100d140183c4813008103001d02500380c075402812402410b04120540c541c2c0c2d11241c5520b81596030886024814948504101d4020a0f01d500007400500c030018400c0c0d0f074000720355914680203100311400d02654480e40c140140c0706000784207128281c0d000d00107410000d11000703201d0a088078000c00009000c0c4094840c026403038401e568a030341c40b1160100901c00d10219071841101440140700a10043e101e00340891030000051040907000001405d0308007a006540c2c00440142900c1249018582417a21451b01030368003034840b40e0a22401078100190050003400f031103101d81c00003401c220704c0d040e80e01c05028040010040880d814012a00b0003c22685d820118141111081d40c8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 175687068 1250 175685818 175685821
    0x20f0a020d0809060f0a020a030902040e06091002070b06040e0a061b08010b13060503090c0402070501050f0f012702091008070201060b0f03061509030604080903060106030c0503070c110a03050303 86
    0x501405111024000c030340f0076007000c000c200c401761101085a03001818030030016955808040114002d00c13804100035442402c0c110b8448a21070002061805010007006a5490000a1039490120b10034000c00030111501d8100054541c03030258170103204050500181c481609030790703803480101d40034000b5295013202112805410710307600c038150a000d041c07280c412503d0414084002c80ba108000d00c1150208100000002c036410310604c442d03140c00700c3c00f0b07200303540300d500d1460164068101150b50400b4242000000f0340c1d071442e03081c03155040f545820501030352020010b00c0407108410301490644483d80800014980d0303211300c00d0380001001580d44803051818200002800d5800b5640410107118060095200c510321030030840782c00c0241121484030f59180e100c000c280700d00074099510350500842c1c08010500403004018140b0540440584200303a0702ca284c00d404642c6441d0400c4001402440054002c501510f0485030407801222580810310f03455000840b83d00d0b9940049805802c00710 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 175688318 1250 175687068 175687093
    0x804030302060c03040302031219060801050a051003020a030b0726040302060a0c0f08060a1d0403090f0e0708060307050901150e0f06030c07170d0603021c02091801020f0a02 76
    0x2080d590481c0c940003e41c0d25505190f20b000303541c0d01400b05a80302c2c01061b903010508042c051042c4411034007070f480301800320750b6075503040038001d0030100c40c00c032010340c1004005414900d2850464050b264014200000641140c03640301445000404010611503c048031100e240c2001950300410380140d50321300070501e0603240003802d100001c0c01c1000c19a09004240442e0b6401888005188a061404c1e402c01d036500700c00100191082d500242f0b080110100882c10038800310500c600c03c5000780c690250450303803042400400c4541c1d205a0307507020703880030204200e14031460000d5080f810003000c440c2e40546810014812100070303408844030301035100805080d141c0001024100e04802c87d04841d42041210100d80c82e0310004020300e96801c4d000414108100e0884044103100108007062503c40740d1901400c4014603440c001a4800e0134441e00e041d03200f80ca00071030ba242d465400713005901c046c0c0392503000c45545004180e407400e542d5020310001601e1007000c405046491321035070080101c0d00710407 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 175689568 1250 175688318 175688323
    0xf1f1b080702032a13020f03040501060f060c0b01090e03070212010c031505060d091e050a0201030e010e0c060a03140408071208090d051318050f2404050705070f0804030302 76
    0x80541c8260a40100381501c00200000000a24100243c940040305016105c8040c0284500d840c207031580b02c0b02200744404d0000540c0000300b902d2313141d1001c2441c90b0f01e4490954681c030001170001c0403540e040005010801c00c40e00110b10004480c1d04507401c001c100d41c001800401c2103c600c0c401c076952504c00d440c480794140100742d0500c607164030140901d801c101c045030151085004018006485030b980408120440a44440c40202c2e400988002101e6281a80c1c41f5149040e099000078180362400740d04900c10700c01c7c020901c5401000340b82c98042d2000384181c580100c05030006050750b82c452030011425046605100740e1044116594994661403d101c003985c1c07007010081004480810440c41c99800196044044007070f00f0480e40310f8010180c1410000b5264200043e406030811101080d40e901d6088280210b00d29105003401d0794520300b5043c40841101b01d1a814004842740101982c11321b80d1181b500a6800d10b0054a002490f813101901c0b50348940e0201c8400d200064204140b6605 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 175690818 1250 175689568 175689583
    0xf0615090207020901050910030f06060321230f0f0702041a060406031a040c02010b0901090c0f050714010c0f08090a0305030c0a0c051209030c0f1f1b08070203 70
    0x140030046052102d03c3c3c01140c550b1005005e4180915000000704414910071664440203544c0302080982e94480c030718125000d400d00c3c1c80115075125200400c6850000c040103105502480b6a0b500300781070351031419038641039040b402e2010b01090208140d6900c103000d0001414203081364501180e5540041c810300c400c444c0d000008540c01e44a035410f0003c40e42daa101103074112080d038a800725450003020b04a030461708103506810b6000b407800161408858064120800001080320072100711303030340c4207041025511844501000202600d082c218828003030406025994040c0384140440a00e1a02050031103c2042890000c52603612240354400d6202a0f483e5201c0140b00141113107040641c1d015080340009000380620450101e81c02c0c040a1203100045011500b00c0119409403240d80380c95107840e4010090140a8041c4071010b4500d42800400407815034406048240e4080280c030704107802e032203c01a085c0411100101402e41d03514404c504507001809101d01c0e0f551000c0314410585010007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 175692068 1250 175690818 175690829
    0x7050301020a021c18030609020906030c0a05061804050103050703140304050306040f0203100906050105030724030506011b150b09040c05010305091e07061b0521070f0615 75
    0x4120101100d580416078008000003440c5500740c0e075050000c01d803010405614002c24622805c440007040c442c1942245079040c0c002daa105c045501c0300810304d62074585254050781c20450700d02c01040705007040d000a10075003502d0000070b1025508180058140d4000303074030980b15640a05002d00500400104600740c190100c8000e51415103444046504d030300b00200043c0070000c4012803101503480c02d010f900c51a00d10318904111203095441c1c607c4c002c5c8801c3c0a103900a02c80e41c2c4010404004404042050710380b4028184c00000f44054100c000e002c00424050400100e00c440781d507944920709170348450034071628294142080c0800010100c0d40c2081c000340c40380d0490410b010100d0090b47c850360503290286000b00c0c01e6500e0b004503515000d807101c201a00d44d000010200d03408000401c1110030340c6c00715a1414201810618030507004004064050841d410140e15881080000440e607001d884941c6486c505000ca42d0316600881c0707000110545403d80c07510158500400340c100c15001408 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 175693318 1250 175692068 175692071
    0x50a05061f020607210c0c030f02070b07060504050a0818090f040f0201120e0d02030c010605060319090c1802030a1419020f04050a0f08010605060313110d050709090507050301 77
    0x55501e2000790741d104044c2c025400e1004103903003480344a103417010506540c0c075140d405208000380c061005080f00d150350001c0c0d001540a0b103220344003d10108454040f2141c50500e541044020344a440081c54003500455680c41402c410000180f000006452642150040300c144991201c040c0022028020004001c0c0c10f20101000001003200b8100b01d0140d4082c0781110381c0314100902038004000146450b40345116041d40942030590010040090030004d90090208903629001d02c413440c002511180a0034502d02840d5566410355400100c0741401294807000d019039559100e50368104481c3e48400f0582c0003c2081050b48290046840c0100b007000074425916081400354030100c40880a036810079000108144070030082815203010301001080c029406903502c0d40046a0100c5205a0700a542441e40014003803619800740e0b0b101d20a88003859245104990f82c8040a00c0503141041d8070030740c018168800f08a080107900d015040e03d0000089444883c2009450002c50703600c603c1c41f03a03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 175694568 1250 175693318 175693369
    0xb0402120a02090a050a0b0d0f060609060f02011509060e06011e030b2103190f020309090601120f0506012d2010050709231012050a0506 60
    0x1108605103580d44003804120040c1c40c1d84100380014240c5101d80c2c00350303600c030341c40310408241880110000c0ca040c11452004000300d0f52540010015a1464441e40000c1245444104041c6000d0851031020031000d100000e4640030f0040c1d6100741d217041e81c200030091580d4510500a946110006540218090804c40191461483d204841d50100c3d050300c400c26459080c119462b4071403500d500340c05130a01c00c3c0f281105400414442c1e480c1c101c00821008180700c491b1004801e80952210720035a40d25034051413500c4181024885a040060102410421640308980a51a03a4400c041041e00d403041d0214881c1002000100720103100e9001085402003244201e501106004198001c0d00290400188051891401450b880f00c040b10400842c007862040c00d000700070580c0801c1c418180e07501c40c140c1c2c0e0354a5018025440d200c100710100c0d04542412458482d02c1d02c2c071070002c182040c0b85490030322010710360301440c29148280c0304c4141e51921002800081d1901404c03045900000c01c4026109 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 175695818 1250 175694568 175694587
    0x1090f110316030b04110403051018030203070206030c04090222050406050618010905092d060915031009030801080c091e04030c06060e15101202090303040306050103150b0402 77
    0x5050b4201240028542c3d210450a0580c40e907030007602c10b810060000350b480d03554030305055499485c80855149164034007030320303c03071940c4102d8071416040c0d426500071170903c0e1a5a00f4031207a80e0028124a20780d6805000c0090030001034001460080200c5850941d4a024505003218030103440c0c00c080e02c03890030301d00288170766100c220a540d200d40b4a603200d06203c480c6400141d0381c0001907040b641c1c02c210140104881f140d40b5030702082c500044400e0940d030f004101d40540c400341105643d07280e8418680c10100b0009941c0404e0083c0072480203058408080414a036601241d03900c810460101d50307031600401c6250014490300d94170220540e012403140c0703000941d0180c1c8100100885054120440100b0141440b40070001500c60340300344104100c544501802d13000f030604551806580703010300d03503e02c036078201b0351100c803c50f8813562640c110301c40c01021302c50007a410003802290944011b1100002152103405824020b50082c1005c0c01e0350313801840c5074000d130b85003903141e0360103540100102840d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 175697068 1250 175695818 175695841
    0x60e012c061e150a0c0c08060f1303030b1f0e03030705030f03040303020403082701020c010f030b01020a020a0905010609080a0b270a08091801050a0302060f07080301090f1103 77
    0x44010899400b60b204101040010705144545240c0d46118800403c1d080042a0001102a0701c14019120a100c06903501d0302c8a5640750104c81c070b0311015003080003140015848850f039410f46482818080360720300000010814a1000ca04400340d000e0b070049005144a030060303006020076406901840c40c0101075290591780340708241800b050400000009000d00d442541030360095035101d40403e5a520040603211004040441c0c4644c40741d1318074261144942c000129402d1000f0180c580205200d40524154010141d00702400c0c1503010f1050780740b0044e80d42c1d20800c2e01800d4000d00024003075051a00007800e0483e581c005d008035030f2243e00104003203014400300c3c41c3c3c0130050982e00e0800d41402d055401080030744001d080c00303a100c4d000c50341c410440840c002d02140300084c2c6900340860ba94200c036284266083c0320f885d4011101ca2028409411710400905107011001c6446142030202c1d0b54034042980240d100e00400390b6a1011010040258000d04004404880b40b09040d0f0402049485 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 175698318 1250 175697068 175697089
    0x9040c021e0f0d21050c0403020108070810030204020d02120f04061b02060f130f0b01061b081603051c15050a031a0603120703050301170609060c0d060e012c06 70
    0x2e0500c9010030324201180b0102070045880c4a481c04e040c0414144584d60312111f40060000700d0200740e44000107640584034610244c410b145462483c20a289150203002c001d610030f150410119408100403103000810b0465036009942e8030b00010f9107413405003048070449540c1c1c444070543c2d10007a0105044c855000a00d280c001d4043c0c01a44481d48030044400001e41e0104001045c0000141131002803014481e1060304072941611005030320103507240d41100c001d00d00c80000b0300420090010081c04000a5126a041440390034001d25101148601a22080c001e4032200780b4541c40d4884078890b810b1401021f00102010354012402d03e007182e035050f0418440002c22021340060500107401c940d402c00042104000b544521952640303a07040c000c0c0380d58424080c202407a03900c50803030500c1000c00950b05100d01202c2010700038035100e8050aa11070b17400b003008030301701c161140c001045105810502134000e19513070142159102e4546450380e04407c032506040d02103000e641c104246900c41e2072419 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 175699568 1250 175698318 175698343
    0xa0302060f0c0717010f0e1204090902181311040504020d02010e03330903130e0a0b0316060f09030b1302010309060218030f0d1209020609040c021e0f 66
    0x90740b5140040d2101c0d281c8985644441000003c02c2a88410b40740c041d40003034042400007030103110300907001400c29902c400c582d9a80d585c0350740400003002000e110740d02482a251004000d80308000c0d0326400101481800e4694004500341d504400c0104120601c50b820420b106480922851800390006804004c561102a050014100c00ea00d07140d6000d0128420b0100e800400d0f0f03548640240c40c00e030300070307480003c1d040c810200c003808138035400000010303101894070056601c0703d028146a12541500c1c405009090076586a41107101d0f5560305106103500c88184400390030605e444d2002c014080034000b407070ba80070700203604d03018804140052090f031303480091035800d0003e60820b40300403001008a24409414a48049036401c0c50394000c001e0204081d030304500b19401d44010712040c54548800707007011004240a180d1225150099030000c81c10240001c0540741480607282c0410190350840b20304a00503040a080e041c500e0341c600d50400001c0800c40010b040a150b8035000e0fa9a88041134900c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 175700818 1250 175699568 175699597
    0xb190e06041203022d0c0307030c15180e04230c0114120f0403110714010f0908061302090a060b090402090a15090e0a180201031a040c1d0a030206 64
    0x26142454000c00c02c082640340e90342c4040480342d02c258642c5c401c0100800c050384641c020f20b03040c034030a40f030005000e03000d07240c0040310110078525207010300b01c401200c044540140175a81e1303600307200746001201a03c014615040030000500d03240c50110211072042d4441241c41c0d110322408000c910000400021405080c00c0c0b0b80000744004000c42c0c0c0c0c6006030300c030010103a03044008200c01c140003c0c80183c0542d20135150082d070030300406a0592680c005000b8450754540010b199030312580f24002e510f00035a81e5007800540b6946030180e0a09090f41140d180c820b4400d010a503c0841c1800e292450344110369540c1040400d003000c4104c0424411200483d02c00c64020454020680e1344101010042031000d0702c66a1141030000b020b060a0f669100c0c0c0302e100118a800160081c00c00e00404500da0076150490303605803041c0d80150300900c18100c6180c5100411719031601951140d00c58154600e1407511114a90364140400c00d088241118040d4052001e401e0100010307143c200c191642044010b00c03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 175702068 1250 175700818 175700849
    0x22107060506041811030d0f050a0807050d090b16050405031504020f090f0a0b1020011d0313152001090203032106010e0108011206020c01060b190e0604 67
    0x1034080d000404e14280f01042c1c0484103410000d440503c0780340c1d848140c054442c0d50402d81000d844902010250740003154082107000d640c144690092070b400743c41410100d041200180a030000c03290a0315040b1008540e44040c0552025034039018100c0880341d00d8928030341410b10b03010a868009010442c010520a180881c003195a6081020401d1001515541072894080e0f1804549481030b14403260143c03400305a10814100002d0a110302031035500c0310345001e001059040010803116002d05601d550f1a000d412110300c0d161081441184007800440c0c90b0b114100584580c41081c0d4886103408980800c1c440f0004d8011525000b52021a4a00c41c84405980c11442c00b410020b00002d515001c001100400442501d0009500d0084c1d480d10325900d50783c0400650b00318034140d080303c0c003243c078a10041000c400e042800f00303032a9104101c058240003034001e2850a5440d80e411086100b00c0c007081c07502020003a82055400d210003490084410364040d80458420311460150700c041c00e0720f090f03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 175703318 1250 175702068 175702081
    0x4090b030a02040c0804120503040206070807060216141e1009030212070506010e010e0601080103060203090f0613030f050415030b22150b0406080c090325060221070605 74
    0x7100303525a00640f0510408042450090522000710f13800c840740b03228400a03011030303841603094034403403940030340380e0391078280141c54200390391304600c404669568007000110010203142c040340b141e0a10405000f940d881c14106154140314903007090016585052031094010000040c4820685c0e00d82000002c084040741800c03410581280500480c0c032400160300400c0100c0000c05034102d945040c000d195903600c5108846414505594042c00221940014400f14441d9802560040340c0d090499807a61a01110141441e030220b40c0c4981d10040c18620b4814103400c444502000d60300b91800a18150420366018882452a00050304169031880305014a84034074041190302d1296060484c10303503a8181c00c040143c03401143c48401d04440000010350041c00509590035104561950040f46e901c0700015015170304274801141d4144260344414501702c0c2c904c11034024031400751151a28090404402034174101c013010807050841d24100400403844500c0084d200e070300b07501600205541d01c03000b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 175704568 1250 175703318 175703323
    0x14030a022a0c011103180a031a160f0c0b1f08031806040807030f0321051b040501020d030513080304050d0e031c080702160b0d05090304050108010b0f04030503160614070504090b03 79
    0x8c1c2c10003021000c20b0130002c00b00c00d00285031380d07200b00314413020100048140c900496041c0d10b040458008103490704003040c001010120350035417008203030000460100d60544407030001050f80d4005880c54000181c02c4500d12036000150100500940f000c03440d180c40c003c0d58540d0f9031098030000d030540144d50709050801d4400c0b4001c81302d058000030b0790140000704e040c0070f000078902603491120842200c03101e000000c40e000e0a0b07030100c0c1e90503000741c003040b80d40603015005040000d0612819203209070448000440043c065401140a00005c3c0040702d00c0510107042114210300c607500c603a02c05c1c0b1285942c2545a82042c402603401c2c50138144075158481c0582c07800c54410303001203110120382c5002c514a14142d0240031007180c805c0b400e008075201c0205440d107910480c0111400a20484018080f904400009054540d10b85015034a820f03035903110301d820368000701500102100004403036410320009008218201c00094007000060500c04000341a52160344a160152501e44000d030341c3c0b030741d400d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 175705818 1250 175704568 175704589
    0x7030f0501020c0102030a0c0810150e030102040503101d03030c0301060e0f180714090f240a09030b0a0b03060402130905060c0a090e0714030a022a0c01110318 70
    0x80340029521b03810100c91407070250680030350460020720f070308001179241010311241001310b4402c81c42d10b1011802d1000d045a014503c1c1121580541d001c10002407241c400308400c2044a06081d40003550305014400325030700e041500c130907031041c7d80b05000b80502001028103c3e0704485083c24050b1200101c0c40200781c0d07103804004119445000c905203001200389218040344904159541d000025819001c1c4c649180141d441003078000c141e400c03814810703040c800e40006440707900900c82031120b1002880c5800f00d0b031241d00c0c4000040d0040404204019005000d6904500040400d01514046c1404640c0e29034000b0000380c49010100008851490154003003000e498001060b5100740c9000c5414070b80c990300151040c000621035003000500142c004a42501507140d540e54200000713100703001e00300d4580003c0c11040102d6420454071070300c049813a90002001020032400c1640c83d520b02e190608100c208049541030040c1402c000c0c0e8000c202008884514420180803040c0071401c10108584100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 175707068 1250 175705818 175705837
    0xa03060213080606030a0b011403030c0d02010c0216050d0204050a060801061d0f1b030403170103061508060c0f39060105100f0e12070b040501170103020307030f050102 74
    0x10024a00d0010768004a009090740d80d00030031034045846440c181952940c0d4984007070500050030b00144040010304028401562004007101c6c107004600003480d0414100c0d480000140c2e550710070401815805028400e050074004030720313202140c81c00e400300d4010005800700078800e558800c002559200340e503000714041d1009400802c0400d4840445105080015824206c01d181a0300000c07903c20305038441a200e4007401c0b80c070001a415640740e2600d607801c0900120144405001c0101880c404840000d0003180100c8000c03800d183c101051030645260b86d0030000c07a40d000034040002c51101c080c102c0d485c2280109485580e03841309890659803110b000c00003694003501c04005484922891050505007513400d00f0740b20340d030341d03a4820001158400300503000403440405d20003803040c0c01420008080c1a005d000801c0c4030821501c028100b103ca50403910706850040b805004550740140998444ca0f58800b00c2d0095504640000740e032030643c1e00c0001c0440e980a10344a042200a4069610052 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 175708318 1250 175707068 175707071
    0x26070b190c06050c0d0f0e070302060a03020c060f0a0e061611010e0703140f010606021207030c050601090516080405030d0c020327012a03031802030f0705010801052407020a0306 78
    0xf0400700080b0300394020654108240e01b0010307015512221841664000e4060700014043c15140d0360900180341c1150032084141a401e0040703821244d01802a544620300901807113101d032400c00524000c5481a10515200d81d1151040100801d002c1440712682c40403420035182903031043d010180500080010b1240038081d0034000000c02a40e4601104005010001d40d9200c12801c010350342282c2807803190100592011502c0c14103078841100603c4014020310f07041000f241561101454403600ba80002001640d0300d0800070785210391190b00304005410b00d00200c540c04c160b00c2d826a03038000c03010406a602e0751000c1004006008000b00c500790001010710b24280422030380110728400e1480722803408240c21681c40060400c0720000c807c0040d18030751145c04070403040e4400720001c020515014055400c00c410b04000360341e04004004c0201c0c500001880e2860074107000404984040e4042c0703010b802051031070001c81950090300114180007030101902d502280c000100e003090654809403086 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 175709568 1250 175708318 175708321
    0x60c0106180207030f081501051c1a0f0a05010917010216060b0103060504050c1e160501050417030601020d080a020f070803040b01171e01020c03030126070b190c0605 73
    0x20341d19038000e8000a4040c0d124440701c00c496400607203003404120b88403c24158110755016140d07000d00090989803620418400800b50308050110031104000000c035239041031019044864505840c10303017411301056400c41090792411002800c045990b004c0c0d8543c6404103135011003d085c007581a04d00c442075082d405655055141000300c02404040c1c40b0a0000e400c0000114050070300340034281c05006c510702403074988607440c0d110381c80c1c2a44104188500d100100301e15000801c08401420005000b9400068281401d1820f080e2144600884100b0904140b041126681c2c001c142001c036070681e41031049007035a544200c8402031161440c800009880802c404040c00307041c0002d1032080e07208110740c01d01662600744c50300440400402c6202c959100c0e070201c0d940c04401103984207001108400150410b42e04007030940c103540098200ca07408200c540d0000b040c000034100c013051500e045c01c010782051401c1c0800c4900a1182c2c10200500141003001200b10602c50304050403c2e0b60440b034100003e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 175710818 1250 175709568 175709609
    0x609040603210219060b010320120f010303020d0c03020a0b0a09260d020a0909240b03090712030c0b2a090a03030309020604080307150507110705060c0106 68
    0x2a03110345900302064903200b601440b0a540006901075100c4000800c01c0c411a1003075662001400c28601014105521211101d03622414803c8981c022103403860007035140c418070341d03241e070102d100140985400c03001d1400400110781c010815142d06c04085c134184070040b51605061346007101c0100c0c020309080e5254104a440003041e806070034541d214404202150b8002403403d0304040d000c40340100396000400900d03144614581c010801c0151078280300500320b988040c07004c2102c3c019004000c4110500218484102d20315024a01a14010400d581142481d2164a607100102d01031540c0ca8440090098180740c0601441e558407984100d070020076282c0340382e201a0800d60085e42401130342c0340000b08480e05c0101001d4440d220701c064808400280740d620110007030011000c00780d0304201c00300400b00e0508014801000b030540140049903001c180503011008541c0020703d0304c020400c80e007036140034166010805500322001190581d850380c2c85c0003038050052400740d104811100861220285 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 175712068 1250 175710818 175710833
    0x70303030b090f070905121005040501060806060117040f110303070c0e160c0b06010e06040603091101050f1801110f0f10020c0601090c0212071b0503070b07020603060609040603 78
    0x200a820b0780e4000c880d440e400302d111a014002e890ba00041900c64100344158103044120f226104010f00481d10614401c2440710111501600c040d544e0b6510307036030305000740001000380d40e4000d2004e00e4007410303809640c1c1c0c800d0780400b0041d000414914020038070340c00f03201040d0b8100f07009200c02401c0c0e950b07a8030240b03086004008030344205001c21661500150041c45103040f25100219107484900c080700c2107a0f5074141325a8000d041c1818003400e03c050b820162a07100140024241c03a80300001d181409003000d81c8003d00310034105040210170801100a1040c40301590301040c11150200001003204006071441c844041c080000d6100d201038600140b0400518004004817041c00c0d1085c00750b04000d45001c5c9d22806042030840c4d8804401006001103581c028810150705205490040020000c03210080e40b2099090701c0c00440402d81c1907000340601052401818110010910705141c0201010302e4016400041d00c2048080300142c66600c9007400c503120448014004c1041c90348a182180 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 175713318 1250 175712068 175712081
    0x606051803030a050f071b18051f050111100203090309181e070903080f030609070306030512070c090c090303170601020c1c14060a0c030603080a0503090f07030303 72
    0x1541503001010544050401104545140400340d40e018645562800b21001c90340c030001c1c040316209080810700c21817078498140c550180c4000030400c11050080c512503000e80320b02a00d411152620203043d80642c01c21009100200c0d40c080c01e01e006000c0324509494241036441d018040007074000000c200e02140044020310504c0c0b002c440208031603124080140381403004889454271510391414000691011080710740d48814185046c1c0125a01c1e136903807248a410680d100c2107003110200a10038145040340d00158171540e1450100403c070714503190280e46a0300c11000407150800050008144440c504005001c0d00c40c40d4010b00110f00030003001408641144015000650810031800c4440d401098181c0a02416401020180d032240208038072083c05000001603003528040080014001c040341d8004450303035501031301040c40c4c40f05150b429120310000a05c10549054000d1000407050010361340949000c1c0340040d2282d03598919035203056000f0a4050302c0303214080c0300004240c0d054002c503 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 175714568 1250 175713318 175713337
    0xb1f12150807060c0803040803060a08160f14030a1b17030a08061503270f010b0112060803160201030603020604030c03031806080a050603031b0c04061505030103140a0204060605 78
    0x45000c00e9540c10b080f80c10381380b80d46009260103001c0000c5008100030b50007854215200410b0201c10a5407100c1c41031800d803403a42480c0c0c0d0340c0c4a80d1010040640002c015600030716a80707010051700c1d0700320000a500e03541c20180080c058458000162400102582e508000d02112090501e1200307044541540c0c98000c00300c484009015080020715504010950501c214001c121300743c11915000c00c8001c64020000c04c8004001100098252a0f9010000008000c1e201400001c0c1040800d00041c070080c0c8440c5001865410000300704031a1a00004031101525059400c0c04080769610049014010132380c0042d40c482d0707000c64040148403034120081c0c01c8a21a40328021042503c1020142c0c540e42131244a01240d0300c3c8000844c100400d41109900c050000e043e40d182040041200c1d84400283c1e60010309030f4404e9140510740e0402d0b1003120043c21000c1444c481c1e440024000900742d1005010080040d0144003611242c2030f003c2110044d0b26174018403d100c441d4035890020450b0b000074180 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 175715818 1250 175714568 175714573
    0xf0b0a080f0c0609210102070609080304051b0f010e06040312020f010b100c03050d0f0507030e19020d140709020a0f1803020a0506090a09020703110f010b1f121508 72
    0x80900314540a012030741d003a14007030710020302d822130040c1005e17000a08640350700c295502040130000064031072091240040c0305070300450b180d04050612a20340f641a03a0fa017550800e20f484051f070700340e132960319440b8420323000d1030450751800c3e500300824201d008a0780300802d400841120710321201c0c4c01084121400310030400030480c410084040145c0301c100c01c1d02c1d4038003140c404100074001c00d10440061258640c4005c0100e1180321404540017103130b07012245180040d81c1c954580310880401d005100b040e800d00c0744030882c1c0c10400c1e00040c0e11540032110040c030340703200984041000c09003403000c0d0004041368142103440d10388109004d00005a140038440c00140400f03090303840e065101018009130307500a04500201c13403c090601091b80d01c00348406910412514002405080b87e000a0401503c2a0b036105880b81071030100c2407030140192071240140c1d0400882c0215500c840d42c0071400604200d03034080c1d100003004030684002c1c004619002009080901e000b24a14202e1007002c00c50742c01404 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 175717068 1250 175715818 175715833
    0xb0a17010b15030709030308060f0d06050a0b040e15090f0609160602030309060a0e10020d02041d0705030402010f0c120f09060504080c0f010e1008060f040203010b07060f0b0a080f 79
    0x2c0111440c80304a03000320100345059014000f02e80304111645e13001002900428014401d50002443c12410310400c4070701548030010800800102c1c02180100a001d9600740150009040c8990f00d40031078080e8038041c03810405c0015003c40040040003d00781d4010181c501c141840407000f0b07151400d2042400d03a02120840004541d440001101d101d0072042024047c0d6840d4048402c0c0070309070300c201c403000900c56120301c40d90621031480100b44803441c080340141e403280741c40302024000607002e41e070300322582d409010000c845030014100d03036000d942403801a148098218094500060030362000d010840e402031048922a088216528803400c1522a810307120780d11032044946100328054a605604403c03803090460400800b40c4040420506054a03403001c240d0210742168000c540000010300c2c20401d10074a410815501040071005550551840d8182400e44215101d0840020003d07903031026181c3da241e000703078054814100020045059150755480b042d036190030105146015000e40e19 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 175718318 1250 175717068 175717099
    0x9060405130207110d2a05100905040f110313080d1107031106100b0f0706020f0406030e0a02180405010608060a09020405100e01060818030a20070b04090b0a17010b 72
    0x3410080101c0c1d1001c802d4044010249a24106d00802000322000440c100004075007075580b100c00482c01d544a0b0354070301e055440c00040000b9610303901d10300e12555180403038048903c0211070459030301c010341700e02e03ba05a41d002d141000b44da00c180101500c04c545400d0140c02c2c0400e0000043c2246c50095a640300081d4000910a4413254196507414050501110400c500e0443c94080c046142d6030090681c01d00c0d100c2e40301d00d0705030782c021460400764400024060125036011722454110401c2c4000a040c235920960101d11076030241140c150400028000081c20040b09403c5000502074031030079140281030418034100a032442d0707201244182d042000150340442071030b11032812100c08a81e10030080c0d280a0041c0e62070100581245141c284100646a28060810050a00d0316080d521040c22100c21400341d511000c0c40078445006030000300080000c242c6241c20703101507030f000010001e02d00c4000c6002810205c1c840c0e1015604002e90704091035102d90650003c44858802d50300a001c180003038 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 175719424 1106 175718318 175718329
    0xc02060d0603030e1f090504020927011805040b010b07051c0503042009060f0a032003011103090a030509040b030618010c02210906040513020711 64
    0x6000c1500b03410100f0070120f858480600c880405c401001c4000e00644140c410b15101c3c6030080b0350310160baa5880d800c079450320400040d25255200239142411206000d00c0384a8916554040f0603511111600416219951055200307034581c0c2441c00c910a036401c640710030b4a040c4141c01075070540f1080009104151390240c2c80355a12460f040c98011080d1844c0c800480c0b92540c9800d0040964540044041d044041110320491200c5258086403040c601b50740050030b0516180e0118401c0c040300121144014015802442410401864981c030380c44155035541c425485604004042403195026100c0c1e2071009202040805480c4d001919004059606060000300d002d40f812042c07800344103459400029001030140700c0c0650304c142c040b181854828424003000020047c600d5502c0d03108550103410000c0c01004036000c401c1c2c60030000d402144007159038643c01c0c0c4110b542403900 = true := by decide +kernel

theorem cover : BRFrame.Cov 175539568 175719424 := by
  have h0 := BRFrame.cov_init 175539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 175539568 ≤ n) (h2 : n < 175719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
