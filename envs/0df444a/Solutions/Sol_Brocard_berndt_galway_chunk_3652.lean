-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3652
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:17:33.758631+00:00
-- url     : https://prove2.me/submissions/32bab97b-1e30-4e71-9d4f-b0f606c1f4c0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 656654676 ≤ n < 656834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 656655926 1250 656654676 656654689
    0xf02180102060c07030903140703140319090e070e041112061504080d12183e06030402060c0d02030d0b090613150e010f0e090105271504030e 62
    0x14014108024244554000179511000c1001034903800300710390011189540c0303181e00e080143c1e00028440341c900d08060500c030b60000701904000c0701d1074030300c00e00d559410b2000f5180d6101074010200c21401ca800081d00160107000c00c8c13224003c0152002504c0034002c60508141d81007003081610402d020814070000e8900b900175104440c4c60280200d2a240c9400b0380c49960340c0e456a10748050100101f0a0080f20311150b00c0500801c044a40c008007070083e5141070b42ca07009c40070b00c810350317851a001e001d0111103c40c600341e495549580c843c400e440c006a0400c00420740c10007081203a05c144100003603036241c4070a22070333007951401a40040d502e8200b4001e15900356203411072800c1c004c00400301080720968400418812080c0d4141d4000364446149040b0941404980c010300700724103013a030000030020f42d08e007031510031a03004155113403094540800c44d6080e035805403504c3d030011080401414400b942442c90410a1032000d0841e029162050314060310b420046506601140038160180c0302814140b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 656657176 1250 656655926 656655931
    0x6030b15030a02091e1b07140c040204120302010509060702061812120121080d1d01090c0503010c0c0203071401110f0307060608030c07090b04150803031f24030f0218010206 76
    0x246d030b000c1e103a40d43c80d505000e2500441c5006400d030360300000c880d02ca68405100030a00b0131000340095544503201c401c0841c0c02140c00b80302310015031034900024040e107004a8030900404140d4080c4c447c81c0c8803007081504e003041016084070a03019801500c00c5000c0700d0001401e0821070004e081240d9858081002c0c92000e0700590b0328188a0b180d07505c07500051201d000c4030042c8441c064005605080302c0f2019101e40c001410501075580380c05064814004000e00060031994110020310401c5040c00084403020840c140c02034056100101c140038540040301c0900240c2010305d4a2036851010030004c524107200641c40c0042900b00003004410702a4900546000d804658011403501c16811170704c40d5520102d202c0c0b841c10075520f40e0703c0c20346035940350400807000421809079218079032606002a207079407081d5154510607503190b02c200d413840d05181d00c43c400c0314072000072440300c100b104021140302c49914100700100760340c41e82080c020b2070681c800f82c0903072480b1002000500c10b000e00068507180c8007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 656658426 1250 656657176 656657191
    0x90c02120c0f150f0103230102160b0730020f0703030606020d05030903091e060a0e0a09111204020414090319050301051c020a0305012d06030b15030a02091e 69
    0xc0c00422942c1905034480745d04680e4088804140071400c070b00c1c0f00e5054400307aa01ca005550001610070803040244203117408160140c200c2c0b0b2200d4440880503941c08411807880b44022420240c3d4041c594000c210703103070084090500c00b500d0110310f00092851a1311038001140865540c0c0c5003070001a904024100b0302c000390b8200076103107084c41100300c3c2d40c0380254a09144a040311003100d03004804200810030141e400500066115001c140000d07190040102e107503400340242d00c50024113164a40104401c07400000d94a80c9844441005030f441c0c254001c000b03a030015144d1520000038920503441e00d2045031002c0240d603c038030020007107403510302407001c15104100090006010990f1207180562030f01d0801d0300c0012640d6070358404907040d00599403001d88954648010740c0701c01000c074840713014000f020000380860b08544000303590031640e060001038a52081080014410020743c02901c144070401000c035400c0d120329500143e2030030422551b85001e80600400301020603401d2400c503401000307 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 656659676 1250 656658426 656658463
    0xf13090f0b0d062d0209040b0d03050f130f090c020c04050103120c062003101508060f0316080f0d03230c1e0418020a09090c02120c0f 59
    0xa00500040110b001110b001c0c2211382e4450301c84c01d450b0121000313078a4003268481c1501c1c41d0f6101ca560540250080300145020340e08040c081440e42c0348c81952a045650b040c0c682c3e600300700344007040c0440740e008078103070030442d000d1405d001c115207445911040051102e440003040c1b06008060003400c15044a0045000701e040100620008428a890340c07115074141c90031100034103440c01d040e0050542c0d481c07022041c004400d0a050f0702c0c800c0d03c0003148100c00d0818490b1300d00e80d40e40a0403101200031910f41c0c000543c0c01001c14107614040d6404800000010300b1100031a040d6021081b11000c164819001d40c0d00c1810941d200142c24042020304c55401d0a04004041003040103030300213401f0480c41c101145401000074042001c10041d50003065801c3d1000c07401d40c0301c0780100b6100d41c0c00303801142c0b402014028491200c450300d008694080c0c0c11590303113481e0740d072900307451a0140c00484210020341c0180c4101084860a000c090b00c1e96001c130000400b1489000302c111803c10a40d0b00e11119802d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 656660926 1250 656659676 656659691
    0x30b0303041e180912121113080607020f030301090203040305190f090f05130203070302040e33130902010921020a240c050c06030f09120c1009080f13090f 68
    0x11070300300d49a01c0314840c4d420640c0000e030780380b401b03680104001000700000240100f48081345176001c4903040e05803103000e82140d8058803100000c1c0d955420150840a455108000502542640d6006550094440d003809814083ca08a92203c8010041004400110355030f0800640c0340e44188020001e207840201c400902d410700003c52200c504100480040f0340e00013011402161081c0d040b10000d0208075240c03c40e905201003032a048076103200381e0100e50360020384020074403600b4841001c0c48140091015101d44240f050500141c907001000340d05000c8115000515640304140d044240c10500c03101d00001c034101e1042100c02181074210140d841e0702076058141c20307104031002855580c000d0914a40c034001621b04140f0300225069441d0700404044240600a44c175403590381d028a58880503038109045c2c45110304201d014100c0540c8083d400360b2502d46850900b41d01082c407a030b00402c6d5461605180340002c100070f5008404000304040e04d0242000803076050310039042d00f031082250602919 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 656662176 1250 656660926 656660933
    0x30f0a050c0a050414060c010c110d021605130603140a0512040f05152b0b09331f0206090c010804140109020306240d0506010303030b0303041e1809 65
    0x44c021801082c03c50355800301d0004070380c0d82d0384095038192035026009110403c04d2000003002401c181c0031082c414070818030440521800410b010300301d68429606074a0081c6024100030f641e03283c1d101c2c2c071045513a82e0302d13010020413408055100304212080051003001c1c07480c944a403038464480440e2303562102c20710040c00303d0300d0040741d40340440300f08503820020f000c031401000b4058807c8502d840e10005024540e9503c10000c455503885e0840f0215082100e60705c41c20902860540c111150814104c0100c5040849203000700000444005a00c80100c03201c4410041100192000b80403038104244003109203495604001d040d0f88041144c024128005480c00003800306200544000c0c40e5020019404040d000301350f0042d0000fa8009003155807a042900030b90008020300442102c12075108211890359040940442403420b078420020030a40c0c0c0386850480041c001c13680c5040e4903004c100400641410b4000b0900b0f403a02c041c3c00c42581580c6482444a000066000041d00140c20301d071001010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 656663426 1250 656662176 656662187
    0x1061d03070e010b21091e010b0901050112060504060e010e01080d0c11010507200f0a12022b03110c0a06020307020108070306120501050103020909161a0708030f0a050c0a 75
    0x4590603034600540b1003c5e01c44200301e410751301007407405030800300008000890000042e840c1301660740d14a419026406c032003100742603070301d682070094210103040010801035101e40212a41440c081400280c103d881d000001d090b03070600e42c0640e0044d01c08400602c00801c1c01102c207801000000c009092003242003e02411070320f90103d01401e000280300d60304600342d004404450321a41e115112a03580d5280011784d15804100185d0340b07000c0c2c94102c800d06480c0c01d000c8054400c1c1c234031905602d00c03021125030070040211210301855190a1110744442000c8508141130b0540341d11039144d160720180380c8221540303002e003005002ea11809207440e00b0802c2940210455080c070b602880c05210a0340e0301c42043e80a80802e038400c032000c84000b00310384240041944024140d03842183d01c05025210200307469902c200030800c42c21902807418042158003d9500c0321100710b00c40041d0300b03041100c9038442c03982903082100c0740d1110303402003001c2112114440c0b140c07550005110005c0346c18401032590040c10b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 656664676 1250 656663426 656663429
    0x9070804051209180a0c0f02192003030309100f1505130e060108031210050603010e09070302100f080f0720010207080d02070c0902090319021801061d03070e01 70
    0xd50b40000f03122940381e00c4440c0008003110b6541e40501860821001038001803544400940c006500e0708880f0a80601c041150300035000720211490032403040303440d100c03041d403c3c81401c40b18402400d00c0e030310003a4400b4005148201e195102520540c09012034074010b03030b840b0740007402d4003500d44280e200b4409049241c04054074016203070240d460402ca49001d0062a0b803a400d0f100381d200d08000052441c0001005101c194207600c200b40d000d45407000001495506030007003c1d40f19006100600945203a14249c0b82d01c104a80e0803551400c2c0e1301e4010424400c0f011414038009407042200811340d40d00446a90b0b048000c5400300600781c500480d000303103580304140401e244181c00000e15041144250151140c42d1742000010399a2400ea0803403e00075480b10307a00700c030403410704003000900164620a40e032007010060040c01c403c1a1044040c100400311800499003d201000d810f020004104a0300d800382c0003a0301c4191640000c030b0348110005c1c0403d4041482070340040028050319121a00e110f0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 656665926 1250 656664676 656664703
    0x5030f06030a1719090f05040b010c080301060503061005031b0c0a150f0b01020601080705150f1602041d030d0e07030803070f08010f06020c011d03010e0106050907080405 75
    0x15480300c500107070800304075180140501401100a48801d24044010a4000881420180d01c1c101c0260203503401c00607841440b0080b0b054030420007403030030140c1240b40c212105240500180c102e40c5d9030400c02d0340080e00402c00040d800700410a13241000d43c101100030782c2504250f4118600f42030710041070f66074403554016910002c50b040c1c2141c0800c0142d040c42c19401075546010f244c5d08440000100500b4950701c0440d4203019085045e5400403400030b040e00d1601c8041c1c08100d0a18052007400000040d108078800000c004064859140c10054000f890031070044005400f51070041009641100340201800c406080d00400d0750140001122182080040c000c11801031030201a4140700d29540f000d801322500004000340d056110b40c0340c3d81001c0075502c591031643d0700c1c1c44450f0311101c1c2c0c50196201580c0202111703206503016100015444000c1c0d00e0303a00d8220801d0300402e0039120035016102c00360303444030010302c140e15200d1481940600145480209854542c0340d841c0d0351440c035000c01 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 656667176 1250 656665926 656665951
    0x20f160203010e0106060809070e060d121403070e030609120909040c09110421080a05160507090903121a1201150608040b1305030a0302130f03030306170105070503 72
    0x481191829041031031044050f000030020b0a68401000d404808116504d04141c01a120003041040880201501956001e0090401a1440e5a030303200501e00b2030320300b1024050315003d4500d801d128800114032407003075030fa600c0a070300e5040d10a052411801501545480d040a428590721745002025540d8010044504045540f124140842d580d56280c01c0728101600b003d44040310310a6840080046818510700a800304443c00e803621094604804000c1680f50b04024004002c1e1003040503181030140c00f80140350300c002d07030759846142c04410342c055010191501c0c004d81c14903800104c00f040158400406000da4004030110440b0950f80e01c0a2070702c1500d08100c0c103200041c096100c5000343c4404050b6824098591101030907030102120700300c43e0b5402d44400142103600842c2c100d00450390150040d42041440d01041e000f079005051406600b6080c00400646440d000c4581c00045009480010b40c55003810303103d0461a1000180882c185c1c104000d01c07420b60792181c11664000c4007100c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 656668426 1250 656667176 656667217
    0x101503060e0a02160204061d070c03080703020a020f07090c0e0402070c090e031b010614180a05130206030a0b010905100f0f2d120c0206010b0703030908030c04030213020f 75
    0x1000c0f60b801131210f001e5002864100c0100342d2151020100002100b00c824138a4555070b001003c0301d05403002000200060f0442010510260194014000c9200640142c90100c079520304002c1c68803025500010070b20b601c800e22504039540000c0820030103401500d09615000c0300d5150140c03040c0842c401c820a0503910500229205001e01c107076403480c03842c00b1700c08078842455140240030340300c64040c1e0001c1600400581209180c6100c0c9942c2800f480440c154150340c1c0c0112039401041d004203848055410103100c4001603607950700862040400100015071010b542d0001020881c0f140c10180c00b40d4900813444540b01d401c800500301c4039540d45801c82c0240f500341000c03501c00c018141c2501303030103401c244200a19800e141c410440d410056603003880d4150001d41d40000c0d560350b00c0c05c03d809a08444014000280b0034002070490380d0007400c0100e451910b540c1c8051059000b100c640c4640341b4045000d204500d01384004214880700d41c1819820101100c90240b2a44104504458007070600b805 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 656669676 1250 656668426 656668447
    0x14150d17040b041203080a09020d020d05030c01020c060a141e0901020f07060c020d03060b1b0a02062d0f03010909170a020c15070305031b12101503060e0a02 69
    0x1c4401600c90040d10030388955031a08440303010a07000e60201e021828620000700000350905c03a510720180c0090a011000a082c0c0a10088840b13000013660a800108015800c4103404d00060001c00542001040c0074601000780b00100c2e584c24501544e0420360106000140100316040382d06e505141030fa62856484400c8141e0080c0310740004515215404903070703002400200d40c8104141c1460f42c0a880042d4990704007201210310320b006001c2e0038441800424402c0100f000f240f00416111002c81d042510103800180143e0002c43c407074001c3c00b96280d244010410803140724001481d6205c2d83d142000401102d01c9081d0205001d0303006c000c1da03600c02001c2401600c240b03050400190000d040e9490740c1010009407540c01c240100313409425070b0101c60000c0380103001240c02507501a074501e811600c450900d07005c0311f03101402c1c10392450410700c068240b020801042d2809400c2e170241080311940f0300000c22603181c1c05101a1820b06241070300400c1100d01410f4001d91150003050010b03030720001c068 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 656670926 1250 656669676 656669723
    0x20906060c010605181509101202040f09060203160503040f020f03030d0e0607180302090f060a0b0a120c020f06040209090a0b0f06030c09070212130e0403020114150d 73
    0x4d02c03043c1d01903110f400e840c2400600d01003440c0945103031881c1c100121008400d02441900540c1c5031580784480403001c201c002045050860584e10040003c21200300c01d00c40d41081d144885810fa030220744c00030030302c40c030100341c2d002c501500700e814100181180703007a13154640020752100010b07000d140711540f04036040d5010b20840b410051203860400c120f445211940780d070b813001101c2040206000d050005840c3c0006800340c02140d43c000c00c0805640c0d1110408200040d001d0019070708140f0720721011071440600006400407500c40c1c2c7d24840700e800c00703c60890981c4c08041c1800c2c203641101003032017060702b0003140e429402901500c01c16156100c09801c9031400c110120050042030580c01400394140c2940d0040b4040c8101302e003141e5003100f0382000c00290202c15103c000141c0e01552041140d8803210740034104020701c1c1641c01100b16602c41c80e168440000f1070741107005035503600d86440d003140c100024540010a02428040004242c8c011803c007900c6094042c1124994081001c880c81505 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 656672176 1250 656670926 656670929
    0x11010221091527040c020a021f140d0b27130503091009080f03030c0d0b04020d050705071a090c04090f0203070305030d0e12071b030821010e04020906060c0106 70
    0x201a81100350f08544502102e010f80d80401510880c1003040d072084082c4009a81e05807940c0040620388141c081006880140341840004800d12010304440f50201c21410040e19014814110200d41003460800304011541d0341440085840708002007144025000d10025500ca0701910811341440c001d03081040c41d40c0540c0664070380c44100a00f90300c0760598040000002c49400310200e901204696881c0b0392280030440303610b954128240401d514034007158103e40d40d90030016000504e00030044104e90192401120110081800021240c0c100b010107030352218081c00501943c012170a2a440c45600c880140310300324071031a2105901d03c04d009081101800c29030b8001e040300d444a0703503803600b0b6889030404103c0c4115a4038100003441c00c2c1d04085826a038100400e101304c0c0c0342100c2a599081c4150f850b0900300c80c00801354034040f0000c2e40c8840184a419441820352004801c00e8003000c01700074050b00000441c0c600001440010b86442050f01d400420407200c203500c490482c1081401400035 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 656673426 1250 656672176 656672197
    0x160308070c09020d0609110703020c0918010507030e0d03060825050d05062202103506030f010e0703110d0501020703080a0f14010312110604110102210915 68
    0x55134840080c145d4001d900301c696102e03040c0401e1699410411550188510180240c1c0140d40781c14900e24100c410181e100d4180c00c02c1502c042e00540e811402c6920894410340407039980c0b0031600a15800304940d5060008900d4107120316410f0103040c5440340210b4010000344036020715542d800446072405038000e40380141900c08219454104250b03513040681e900150b40520505401d142405614020341d0180c0203071041d8488000320408441d107000040724400036440300300840307a504124558416141d240c041c546203250800320200b50501826020104160385000c0c2e4117280900041110411641c004003510034030300120300800c061100c4204020001e510002d240d408040d0840e1180d401000070031030801801c1c40c00300901040307030801c9083c40c5082081c180100002244451451900f40f05880c11104d002450342481d032505030251003c80384480030401703030345041d64100881c40f441c01504102201030800f81d6010480c520502130000e0083d10020442d00ca08207594040f205a05034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 656674676 1250 656673426 656673431
    0x50c0111070b100605070c050112020918041506141e0d06062402150402130c08091b0604090b041b0c0501060b03070215360609160308070c09 62
    0x41807a002c1036a80701200d00c0c41c840d450005020602c981302d2004c5c0d0b070f9603907442150300c251241400c005503a10100070b0044400d1940801001070161190044c80101c5080070884841350704062625010010444080c03031021803401c50b0401040381c0e0041010301d50038064031000690b001602600031420900e09a81e6009410403565004021143c1e2200d42207807a03010740034a1031090682c158a040440100e4400140d0180609000d00082c41d00142c0d00315200a040c91004090002c048090344c19000070240440c1e540400c004511307d052044002c14454581d4801e200072503000062100d00440c0501c01c47c0740d070341d042016059120b6902a0542074010150201c180c4280400100b4142144804031103650a20300b0006032410702d07406a034050340498014201c03044d501403042c2404080202101c43c0000c0740300c40814801468003120640441c1c2d1301400c00c0000641140318a0300c4005405006103501c07040300410030121188405007580c2c0e20909855a500d03450174100c0e910310080d004400c0c0e4a1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 656675926 1250 656674676 656674687
    0xe06070c060504080409060303180f05010e040f090210090302010e03010c0807120e030d050403110706050915041a071e021c05030d0c02011b0801180c09030f0302010209150a020a03050c0111 83
    0x50b004ad401203550710f00b481040c0c0c003058640c0c903007000116140c0b05075400704281102052040c036054028840c410103a010010300502c2503000502c48500c0b040000010412444007441996403100c4001c0e0030460990082c0100c1030040c4004001c0c04000740071200f0400c54444240ba01e4031a9001107040030b0542c4222a00d401d103d05007540248416075080f404201c2004108004d000085407550880c4c050fa240d442c1401e54032028010301c0c181907411114086000c0001040d89445c1020000484000003142a1600010714204a01c3c400000402e12600d0344c1180341c1c001640c07201e132034918001080200e00c90f001d0403450f1580c0385005040c4400c2000d400c3c04040303012168158018908140500c2c100e040e410044030041da0810700a0054881c40b41c42d89200200c800c40320303004031007902418500a14155580e8036050740501c00c40c402200140d4000484e010700345000c8048060030440c5103010751404d002e04802039920600944000c0500c40d0100e02d80400c0320303084d4400145a180010069502d2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 656677176 1250 656675926 656675933
    0x1511070501150608070c0302060c0310090608010203040201091a030601051c05090a0308010915151e0903050615030d0e04060b0403150606020d090b180a0803030702010e06070c0605040804090603 85
    0x25102c07801400005982d0400250060384240810480150150007400345511f8a82d2480400c0d800148004ac3c4045e8150b00040c0ca81e403c0d00ca40001000c1d041d00051b1241032510005103130328105d60000c40c190504a0003501904121411aa040300003420460707942c00840c4071050340c2d2007459507500221858031003007040720034001c242c904004d84a940ea41e06540c4c0ca07100c40400300c842540d000e0000c00389260381030007074040c9418401844811410503e8002c100810500045605109031000088210008100f044002c10000350041d04045215500c005940d000c82da450000d100b2000801c441c1c00e4882d42d05481d242d11031400b1b89003403420b4542e0755450f41429010060b041c014113a0131854840e0020300c0700d201080c40c0007004200d9541401c120725206141400c1c1d089815400382c40e00544011612683c3c07181250740050000102840e00c9240021020382101e40807403180c41c0300d4110600700084258850201c5280a90103a00043d0644507401c00c404103000c0c0741c000c1e400b42890040b012061 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 656678426 1250 656677176 656677211
    0x31009060311040e0d020a0f2d03020c0906060d02030a1401140f0306090c010807090b032410140a020118080417150f0604021324050301031511070501 66
    0x2c0042910705200756030f00e074003480e591004071407482c0005030000c2181c2c100280c0190000c601180c0603000c446940300c03032060741498600080e10a60301464500f400a81095010702411803903c00071a1401042c1c80e181e07002c60081d20a0564000d07245a000002a000c0310566000b544003d40b040410b20082d0f03100d08524140115103c40c0c03920901031259040380c01c0ca000142c5512494100d0098066a00c9035001581d65240151070390080c011102d13000306450180d04003a42c418584003160801034000398800d8054080c151094a0107268802010201c554004078801c269200c1d1040342c1d6600d403c1d40d0000c0b8018a86002d10380454904940355a081c40a440b0282050318044409103061108401c83c039651804880d0340c00900511500000b0084186140ca959002102402c050311340303204103004034a110b420360004c4521140011000c402000003c0e42e0410070032450400c2c0b49154156161200a0b1b0440c200d1944101d444a112141c4404940d0070364650740c0c0d004000b072106400c0c45254849 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 656679676 1250 656678426 656678453
    0x29090d12120f0203091b011115180105060a0515090910151e0f26180106050f0d170d020d0f0c050304120908150603070611120310090603 60
    0x1038050402d802c1140039070301031013100d018620ba540140f90041c003803039000354074419213010365043c0503003010f911500f1001405040e511900c8000440c0061900701c607076514140007041c602c60b044c2c0c540745c20000c0365115030380c451040d00d4045446100d05415a540c6400c0c40c810030a0294102545c0c03000d1080b4403013041c0955065030000f66100000545152044900032441d05903081d9403451a440345841d10300804070103542c40d10a00d4103c2e40600e1141c42c4c040352648003407025102098000030440c441100b000c0220b1804201802032000601c1c01c0700040030504200c03100c2e481080607401e004200a13118061480d640380a0041540311000c18164000130f4003c52002003005040c404454485003603485a007410304c2c0d480e00c555095461300c7d145d816095010150310820312403102004200c07a1410020403200c46903040d00701055107010b50900d414284954032080030303c028100034482191011654000c0081c041c0c296075140d03030b600006401105200d500204600d440c0001c00b00c02d102c84c1e81c40303c10703 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 656680926 1250 656679676 656679707
    0x5101110021c0e0a0302120702030c0a0b070b281a041503050105090c060f0c0a050102030c18030708031b07050406090509010b090f01141306060e0a29090d12 69
    0x1000d0303d41c0e68842c5220701c0014010781219208151401c2900e0140048500140031074524180c0c040104510700500d0300450f5041001142200401044802c090750156100c2c49060062807800400c800070808404044141030b00c07aa40303d2028600080c0c80000d1050091043c44400d2690b075a02030094042d0106681d02d50030400000d0105100044045041d00041d080e00c1c54090304110003071894000c0c2c802d94200d07000381c100040110b00b090001d180541c0a400e502503403144444072820314800c551074000c0c000d4001d580d0800c072030080401501c1302006540908501e84028800b8182403601c070350003d640c050b10300100800c078211389900041c0b068956030000c004801c502c204109602e04103c0e00812621003036401800711005210750154008000783c070b03144107504003280b40c1060702c41e550081800604104c0240c0100c1c94810754800041400c14030300301140d010908404101c0c1403c580205a40d200010b024980e03485100110103155040755480c44010f0030344100410340b090314034008 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 656682176 1250 656680926 656680931
    0x32c040504030c170c03030c0d0e01060311031b061603020a080c0114060105090d15060b0315031c020c0f01050409090605090c01211d070b2205101110021c 68
    0x1402203400144c03c5800c4180c00c000118207582d84c42d0700c00541d646c4500d664400c0710741c550b00c020b01a03440034010100038520441211900e4060398042c1450000c01218503000e1403004038050310941c40c0c020032904144401000340d40d05041a050a070718010962b00c00401d00c09001944101125040d40074540200c140301d900c10086d169200111458000c0e00c82942d030100d0449105000981400c41491203102c2c100c0000c251a66159040075071904100c40c4400c040b0084800c001c46441c1c144000054400000ba0b4010b16403c400002076451070300c02d5038070780074449405021049178001c000780d50050110742c00c24801c80c106c3d40b501902805007510054864824810950300b1907016101074540c800422040f03010310b6680380401c0300a41204880400d540285032081ca02c81d81e010300060000e41516205540d46030a41c880a8000043c10401c0a03402c21903e00188495900d501140005021620300000e0740c0f0003941d600c40c241228204000e4050740f001440d418040c0712803803000710a15804508 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 656683426 1250 656682176 656682203
    0xb09010306061403060108040c12030e03010c0201090b010909170d0912111011040b04060503040b0121030807030b120c09060d030e100309051009140a032c040504030c 73
    0x380c69004211007401c456160620024017654464140703581d10900070f0b028408010365400c441041448030650540c0083c04621140303030103003024000d008100741984000c0121209648405080950600404000a843e80b13003080a100c40b01c8000c0071206035005455984440e01c4200000814618004945407030075202c1c0c80203214017541e0540b511540090107400c48030f4004006000401803924070b049030400c04c0c40b0210b280040e0401800c040d10340e940301d56559090500b041400103105a12042040c81d8080c9014050600307444d0b101d85075549820550025101d644080c7c02611907a0012600003451a01c01000150001000f41c100c90081d03c4242140d2034400c1802960320201d54003074003007003840b610050b20307051418820180110a00c1c000075602c0e8140d499906001040d09000c000c2070302d60055600340130304001c04011161200c00100f0b41c0301c0e800c0e60003604400c402d1210408801c1c0760034038214508442c048042c00d40380c0c024001c10540c6400d2070050000c0c4110f45e4140d84401d2100031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 656684676 1250 656683426 656683439
    0x41404050610050a0e0109120506070206012702031911030a182a03150f050105031b0112110d1b0207270608010c09090b0a0506030415090c0b09010306 66
    0x150446003441d9680c031346070252150080d15001039185c1d8140c10882d1710321000420302c140708400404980300d400074001c141002d4400918204040c0c0040580c420034010511400d0f4919003c601605c5000c0000b40e140da0300e8202c08044059403038a010416800c20900c228840c001c1e0f8000d41c45030414030000c010319462903545405090207000000c00c00700300401140c0d10b00c01d448000030b0030f62442042064400c0c0c1c50b6995421441d4105d06000e81c51912510321001800716401101e01512050f07006040c1074446603007800b8482c3e59550300d241484080c0614803201103d540141c460072400c149070a5441d080c3c1c4000d28000c1c900d068429484825441042e030680d84042020421200d41c103102c80c1e0000100b94030185400c020807841d040340d6548030703000a00b14100b0b005005030f10070180c036100704140c40c0801c4c1605480001d501c030792217124000030078451542c0d54010f594009410680029100c00380c0c81d0300000804542d8409040314240c0d00c00041c58030048030051003052800e98051002c00d0381e801 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 656685926 1250 656684676 656684689
    0x201091403040f14041b02070e0106050702060d0b012a201e0607021f1205090d0e030307020d120311091323150414100b070303020c030414040506 64
    0x510403403c444880400601c080c1c03048002ea02c03003008000103902e01c2030148559602c5103811150b000342e00704440c1003103801c60f5038055a004000900b0450700d000c11681c000b507841e10607000c6540c8015554110700388143d1007a0005006451007890005182144444030340700501ca00104854900c0c04d1080034941c00d00031b0b4801c241c000c4015004005201d001072400c03092034042201650051814041440507a94204883c1c0c210010034140307101e9240c8002008065600564008100a00342018409401c1c000626130405040d80c0c5402c0303c000d04e0120001e81540300d21080694080b0304509884c0502c040b5210711002e00c20551000c200505004290200a000700b003042036008914200b841071810340e9030403042ea0b548440d1002c56a05a0800b0099a1010103940415030528050f80811190400f0701c5a55441003240f07050080c10f1400305038150b0300410b40c0c000c41e4000880401d14a08060080c1c050392880c140103002d99444607112444808440c014070108c6c2d11480c20003000c100d4604021 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 656687176 1250 656685926 656685929
    0x30f06050a1508090a0602190f0e03250e0c09210c060702040207060509100f051620031c0b06030601020c090c0c0105090a0309051906032a020109140304 67
    0xa101c14540841600c01e41d00300302c0c024402d04c0c942c024000841d000484500c010594510300c0c05000d000e008241500501e0450180c4d414000d2180c440d90180c46941c0008500b01520b80d4520008081001028a0764500d0380a500040b8203114140a1044820000d40a0f00c0c2c46c03001900c86021081c000404050003990000da40c20468000b844011441c6c241000200f0116002034005890302000342c3e50a8101e5900b121070780c1440c0c0006003468011112805244015044440b0a01150400382141c0c238031170410323204180a0005154840b011120700381d51030038000b10704a042e20340346d16008000000348040e40c0e440411180c41c0c40c064030076038a00841541d006000c181d008055000700241400344102c0080c080c400d82c5841030100002d002424002c5038880d80c1c626000c0e000803800e03440c4c090015807040d0800d5104840400c20010100790100b01c030f00c201d50760341c500450101507520029a0001c1003400c2c85422440418504003299015007000400300d20501c951402f00c40f103842040d440703000d039 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 656688426 1250 656687176 656687189
    0x414030a080a0b060c160303120b15091f0c02010f0c0b061e030a060209090c0301050907030209040b120f07080106050d03030e030c03270a0506030a020705011506030f06050a 76
    0x11030020990312140ba90118020b01d01c0074121902c1c0407000d030003041c5040210326809622014500050040551000703205024281c0c1c1a0140301c5020a800055191480501704104100c80030450800c199142d401455218585000304808001c05900041c08050401801e074046484402890003880c0b10f001c02c41c00c0ba60300070106c40401c1c0c4950742040400a6a070b584221008030550640300319981c1480301d0400039108a100583d25100c0c0424484024001800d00703090180600c0100042d4407031468103a440308842c600140d8400d00303100000c0080000e00103858001521140c42104000c000501d03820604640c0111141ca43c0c0c0e5002c407600b41c510500569400000449400000034025080b0b602071121280542e410081040541032440d0080e64030308649030501103a41c400d9070320040c0700c2c540c0000252505180542050045055440301400800c4043d034002448400c1c00f40a6111317024502c0c2c04540c03540e05503030b82c10b00140505621212030b80b40900d0f1800019041c0751003141e80e4101c516 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 656689676 1250 656688426 656688437
    0x9022205090609390a110109050304050d080409141f150c0c1a090a1d01170c09040605060109050904020d020607080c0715030609020913050705041208030414030a 71
    0x6400b00c500040c1c40c06446a2140404a107401e03640c420342c010081380300440f01c462066100c0003a140000d01a003c201030040c03050345000840c0e008a40084111019518140c03030950b98600300e8600700c07207d4807496009025461038403070810b6440c0700d8000ca185c000c140d00b8403101d044486580ca50089100c06104020f9410403440c0a210076500039285096001c0c0240380d030051160740e03103441c4602c0060072905000c440034002a46071440c9003150046000d4107a1510107108031185058001c810401030141c0100f42e20003040303005d000c000402510341a05006032a81d000c03402c1c103140c1440130700700c19600e15002c289100800704103400d008d030495200c3d0350001d015410801140d02440842c2e0312007807003a118040e08104032114400300300544401080400201942c01220314801000c43d6404d81120131130710b004120b0a042503552550031404041c1e002d50004007030321008401c3d9014031859004003071114140303055400340509500a18030035402003544030300400a01138000e0f100e00c2a669103802261 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 656690926 1250 656689676 656689681
    0x30a020f1801030b0f0709060e0105070f020d0c0f0918110f030d350411130c05030907151e020a08040b0a0e03010203160302070c09022205090609 64
    0x2405814000c04080054601200300d041d4030407841004500340c10a881c603551950521500c0c40000c4c01560b07002c500c40c0341459115080410040c0300380b10f003542031810031101140300c0c020b10908091a407400c503801000c401c3c51417003a01e40741c81c500c3c049116031884030703080c81e00c00a03942101d0300610249206c01600a481d02d40c41d0307905d403001c4601c107040840d00040d9104601a15841c2008660048400c079141d81c01100059504480c2c0803104685180500c08011100414040300c01000c540241d84241c42c03c0f4103114403004240c005280310210405a410640c0c07086c40701d41c122000b10700409404042d15001a11800c0c450880d080da00785100c00030309644c0d0f5540c1350b40f101c40160300441c0e41c94070580f1600803c0b9164401203406c25000042c03584030000305400d41e95040b070b1103500c9994040e80250b043d881d14800080ca010000803940040c5900020400300f08038418900304040d0115000840d02d5102e032508940031845030141c0345030f00042c81d080100d4946000150b99101d514028140e24196 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 656692176 1250 656690926 656690929
    0x6020d05030a02120f0a0e07050a120f05070603020418060311060c0106090f020c0c0301271a01080d0f020105012106020702100810050a0b0301090507121b0806040506030a02 76
    0x561000703003100c041c6542400004c4180390000701c00c0d8002d10729030070440c04038101108010101c8509441692955001c21010401525002980021030311100b8150740341c1d0040f0700340101d480f208110010000d0040f44004500c1e00d41603800351040d10000840102088100040c803070482c2d1880c000035102c2c3d440301c45111402d10b4284c009060748100500040b0341107a40f042c2500680c1c0c2140f695290705a008251004940ca04100e03902d0004011030007800b040e00d060703140702d4010703400c82001100c84e00e9204e02d40c02403040708203011403100075003441001c4940c0c0d0360b1029034a440d50366407480b00082e00d10450610061050090318142e9510400306500440540071407008441a11001c45880703070244012005a0b0780d00070f0212801107a916417440501c0d18000d2450407940a0300308500c5540984018803981d4810030507203040d10740d41140001c60b51110350040d134900f141019002da415040c8000d08050b0400700c0d99821032910107880d21807241d00e40c0e400f040255030007141e01c541c140e40b100070b803100035 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 656693426 1250 656692176 656692187
    0x616020a0809040507090801091104051312030b0307081e06180d030915022a12030406020c010b090109020c06010501050918060105130305150106020606030613050c041a030105060a06020d 82
    0x805203d042c031b100c0080d604c200b05800d4440c5d40c48281c0e40346103542301c00b003c507081a000321a030104404011302c4105085a440c48000105040d21404042d40c07008504402d480c104694005041e804d412591146070000364035512040e0748e82da0700403501038607003c81e800c00000052614403401d08009064400c0000e0b004400810503a24180d8043c41015100902c0c0101c1348010010000440303041069000c88071814060400340e040001000d0b44000b00c1242040462421b81e138025600170f00240ea1420014801409000b480550079400300e44140001a02e00981d030051108007070300415103016a0362600196128090860110f0308030500310b40114140030700c40c1c8443d6010005043c4136042010f140305001800000740c20488290b408032112282200025075114010300c2c1c170b80b008115a02e010800310303803600b0018010994880704114004204407003400110050480500100307c0104901c41010105480e44d000c6402540303884003083c004e0a003015400c0c165a00f9170001d0954200b202801c554 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 656694676 1250 656693426 656693431
    0x606040b0409231c0c140613110604050612041b060806010507061401060908120301050d020d03020a0f1127010b16140307030212070b0106030903030f060303020616020a08090405 78
    0x1964080c1e5004c52205241e58240710100a60302d903201e001411141c40c02d40030750780744d528061010784c0c0170b01c08000c2c0c20702032609041d1126a2100200c103682440c040070450741e0080e5045240d000705c0c085502550301c07582000107031140b401820705031960390411082403002c804a00a06000030b920600080d2103500400003403407154482d00000803148907001007403113a242c00ba040800001e00c1002c08014420f010440140303141c1c00c81b034003149103504d030500082980c000c440780240076165805050b01450700a0005000842d08003600d02041e20340b40c50b052141909560038140b184000c0c2d582445040d00c0900015107041d290888007080da401e1020320f03e540e400400100d5010342d24a50303c2c00004084980302c0503400d031540b000b103417980001d240c007a0901c41c500c5190780700303480f01707100b071402143c11480058115001c070700700090181030504046000c1e049805000c6855401d082c80001010341c0001c00d80c1c81031080c1c0c2d0f07108000d00c2d261101280c6070b02c144c00700542100400d0281150f00e1805601c45038 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 656695926 1250 656694676 656694743
    0x3290a141216051206010f1e0b070c03020a0e04020f091f03080a1106070e10052701030605010311300106050a0f090513090c170606040b0409 62
    0x22029001c601624038000c40e18495201800d4592020402c0c0d0914141d050004600d84028268660410b003003246c0e40842403003031989040f4410307403043d80300304030006600c09001017104842e0388801604282d24500c4145c0f000b2030281d402400000703020a0840c0103140580e074010319044440000908025100c007003d40710344190440c00341d5014000c0c240603484801148158141a00e8000c078040c0603209118a40307a088098001e00104122150b03c034030300c155610022a9140070480001c41c0071030349402054082100e000f4a0304280392a2820044441c0180109a805003c000d403208011001e03a1461841e036624401c0074001903220500c03a400300611045121b00f5180100d94031402c1107031b06c030400ea003c803001c56000295940259400070442c98041e840c0d041c000c2000786400c011400050307a5000d00000240e5902e044420401e480e00114020191080660a04092010544d072102001d0341c080d4440d03480c21503100ca950a00f4000d5061084d00000305401d014284048000a0802d0843c0304 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 656697176 1250 656695926 656695939
    0x60909190b1e0a06031803030905070b03040515010503010c05040b1804140f0f070f2001020d0c12050c040b0a020f030301090914120301180e0d03290a14 67
    0x901154503403640062441c1a40d0030080d1041c44000b06000031860150464020541021140d0050700301c1201c2210082e0390501c2c0c00228001c4600302241031009580180402410010501c0148100001c0702410320340006516442d90340d94608043c200c6908100d40300100d9400d10040240c09114000381c071035441aa01c112011280080015046580c0c00c01e4405544084005205c0b12505403403c0691101c8441da8465040c2420308001d004440580c60442c100040e1000b99050342d00103030004188503015030004d41d00c80900388400806489800381c100d001800c1c3c030802000e96035440c010107001c4c10314000050b20b49810041040101e41c0704941c40e809500c9000c0715014010801c200441c0280810640012a02424074041100904200c0c1c9200c26600c03039040e485400c0311250880c2d0455070403040c0b40107c800b41004d400040d0402c010b10b03205a00a201c013005a180d01600442c2c1c1a601c41c11121121062000d02c140b00020b200b204075070000c640d0582448084100c140d01010248014440c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 656698426 1250 656697176 656697191
    0x1b150c0d05100f06142a0609070602030708160b01080106061b0807030e0a0b0c0313060305060a090c090506070c05010224010302010507031b030e0306061215070c1a01050f06090919 79
    0x11044c00c0c0181c10081c2d04041e4003891b800d4000701c2403020580000f648000703404610f140c40c600943da8001e00c4005003904000294a4802491082c0880c5180354040072085041da03541070007500a00452003108082007400c501c0410548000c0c03003801c80540e000841c1801e00c40180ca04403040a1500c26040e00242e00c0c002c040355400809001d4100144048011035a660799540c03901e0764440035074085001d140c00c0c0f500340005c0350f84101113001078688010001071449401d00d4111909d544541c001d50f0069000140b00301070041087e520402c0d180d00b0f03000c480c010a00001416a80c80150b0215200d00d5103403001400158032640050000601918140e440281090284400f55503e41310440c0480c41442c003041e56402e080c44481e80c4508120f4480040c44890016151100044910398180c0f00c10f0400181c001800f5000410f2140d07000600301d0f0501140e02280d610b40c0400f03025961007a021001601c00c646055422203081d420090707c05000c64980c032880d2009120700142c2180c496842e00407 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 656699676 1250 656698426 656698447
    0xc0601030c03110405040b0a0e032b06080604030f111e0115170a030302160b0702060f01081c030504150c050d0605040e031b150c0d05100f0614 63
    0x14040e40c090000c25040d40d00d1443e080812000d110301c0e580c003443c201000c010203d08042d0741c6d2540410b4a640100b4102c499401250841c416181c8860f18104c20000700c080c01801c040c169000441804010080720307884007038071980e5a6048800800240d0400c1007160800c0c804e00e94001c0c101c1c3c4901c2211000e4100309400211145000f03c40e5031169510f06a1040344003407000942d004142c180400e5121180315400c06440b08040e84001c0c0c245500060031501100c0100c00d16071845070800813030b084909000310029103410702074603610109a1210000301d140c9502007851020340d921034132440d92821403540301354060600100191a15103e1810490240d0040c1c090341141012507a00c881c0d0712114030440001300c50050300a240900d140c42410500d8110000455601103032080100c0502102c4110071450300d1280004081048445028003103a049500c024106165507a072040c0a40d83e60350b80c20382d107820100e100b14a03581c19500c504204080c002d60580201001080c0340900d050814113 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 656700926 1250 656699676 656699683
    0xc0302030a030c030215010b09040e15010803030106020f0606180c07060f0f0c050f0f0717120a0e01150e0601050408012405181f2402071e0b070501020c 67
    0x180c2c00f20701070300124000c140c2d05001030083e0718103c0ca4034070340550400300b00f10301e140100c5c0415400743d5550320301c5c06a200b40401c0b0100140070008102c180035a1141c0985d034407a0000e01c02c000c00341c8103504a11058880c085002481481e014000280c2c5030303030344200d541500001908001c0d0b5100700700030920201d1054081d044541000744800f0a02904100c040d0003141e922841e00c40c1040403c0c4030520070340b205041119403005082d00c600b500c0c3d0b58141071141c4444178840c01c26480744000281300406040401040380300710f111000c100100916411380314280c03441660305080864211405010780c801c41d140f42900500f040c902a0306080d210030005086600580c826030400140040b58540c0100d5a000c02c0c02800c2c080e2107907070080406040c9440b80305400342c003a240e14800043c1c101d0030101c0c4103c8460080c40450000554190707003800250b0030803840039060005005415003c202d5100c0b104042190001e640c10342481603103043e1840750a508520412a500e5400700b00e00942c5d4030040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 656702176 1250 656700926 656700943
    0x140d020f060601051c0b03010b0604080a1104063f03020105040b01170607050306060d090f0605011401090e0411100906031b0e10020c040f0b15070203190c030203 71
    0x150018201022001031040c075120004204a0402c4020408115000c907240441c6008031241d4901046250380c40d00020701400d01250800d4000c40c01141c001644240083c1c940d40d807034001d10b1180c0d0440d40480600055032001d01900080b4004003002c905d900040a011a500103890f055030502c2d1a40c0b05201011006840701c02c0d001030303440f4018001845200c40040d4014a007000300711010f0040d2100d800c2d20350000800c03020030301070003000003401c6890301800c55050b00342c2a00200030030589450980d9a000300c40c441900c5a0340f62800102d0050989a54500c95090584409007201d262400b06105010003c204603042c07a0f00ea41c1401050b150380b0320309100040d090b162104083e08240c0000e00300c82a89080b80190a02264400303100ea4011600300c0c4005025240c1440b06614124282d00d0604000c106541283c9400080e8101d40362603405145414402c03038054448525042076403a6030300030480040c2d03054010605020403150900c0d0784600300c5104129206140d0f6603a00001e080030070b034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 656703426 1250 656702176 656702203
    0xe0a0801060302090a02030f270d0914010e0a12140706030504030f02072403021201181118010c0f0506070c02040f2d0e01151a0307081314 61
    0x10354606008614001203641d5001c5c800400c02c6080d032510b0381c0c03c80c0302c181028081c1c84c40500c1100300c03405441010f45101404442d000200c4028599021001f4034210705445003120240c0f540380c00550039845491126501c0400400d0032000c141004040c501e804c1c03860504441340150440c51310203040f0700f800450024816030701d0010700c0b4542410090900e009441405046402168007440f4040d00c00e200e1401081d913051040342e1102a20005600174443c41c2060031510740f00500020380480006076280501c80024400e0100700708100240a503800b0b0030981d1143d43d0108105040e182d48240c85030402c0c50301032805801610341580741d107400d1a40503180107001860500b41c860035801e003070041c0da1408408003820400c03d08810b03a4081c683c01c0306801c0f60302e04900b80000d42e45203022508624400c00c6044004c001c441c80302c240c0351184008521901425142d038445007108181e00c0f13815207200d110180c84a07015a5034030b825203504104141000c48503240c0c45803141191040801108120951 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 656704676 1250 656703426 656703431
    0x1b100905011112040b0a09020306040501240b09060a140403080a0e0a030302060a050c04091a1503010e0705390705040b01051803120304030f0f020102041d04030e0a0801 74
    0x15a03092641c207607510101182400714042062404010700d1200150b4001e8100c40c40756101d13100d4401050107001c500c48040c1d41841030380140010300506600940202d0342c4070a281603c0301c0004010301481e0362501c0340780341240041c0025212418508001d0850082074039023400c030401040150340749034102e80c00a90b01c00d0000f003540542981c0114035081e0240c01261350301c0b085440e59600a55500b402080790701115101c0004c00c05281004c800d84024003004031040c8514000349910003048036583c11954883c40803403803038012410640d000c59041e140d040846821030398400d05d09468942c40702c1440050060a040c48500f0a944071001010060030704400c42080c01810525916000741504a58800c40c909107001100d6a0450102ca0b080c103107800201300c04600c01400039040c09490f01140303c0e03401c0000108000c02d03034095180d044201040d22900c21014084104900b00e0049010b41100e440008521519401c4100b0005031f0041c0b0070f01e070540601f10000c02040c01d0042030344c0036003066034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 656705926 1250 656704676 656704691
    0x315090603150e1209042a0e010e0402160b040503040902160201030f0b0609040b030106030503040b1210080601090e01020c12040f0e0c070b040201020a050105070e0a170703081b10 79
    0x218207020308040f840e610750081c407005040001050700c40c071036191000d228655034428005c08115110600641c0e41d6100c45c0c4150440c40c11501429201c1e601c50300a00051011101603003500d014402d690785080705080310824218190b8034042400d0b400b0704260b82c0d03031000b030000140440c0305000038000300040810b81c010a504901c005026210398140f5851643e0802403c802d11340c490070143e07801d85e01c088074007003501d10300040400c3c0142107070b41000c0d0041c0000074000c1b860b141c04034001c0840000344850800c441d80c0d800c52600c030b903504c0e60164020f1600030200400403039003c4d400c00032100039418001450400580000c070328101c10080c4046828001040c10000c00b035015800d0f1008101040c1048214500f20300d4840c43d601c41c01c0d1004044120705c20209082d139200700b01c1f01a6030b40d0702c00001c002c01c0c10204400b404803941001580e00c0744100400104441c090860009680a154001041d40e14210f40d1011800c0d00856010007a6070394401e0400c2d80c40314104110b0540e2403820a0005214 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 656707176 1250 656705926 656705963
    0x10918140705150c1c05040801060f1d01080a030e04060e040c0303090815041403040e04060204091a030309130b060706090b090a02130507030212090f0f06060a060315090603 76
    0x2150070040f0410300500902c02c0c0c180300480030842c04408003107054141c5c120280d00506071180c1c0100d420a00980d032806074089400c0c6100f5003800140c980740e092140711280038806010030080c0034090a85c4030b4000715450b2000a00030341c9038001c20440208080340c0c041e01c90701510a00182120207030b525050003102041415003040a0b4000382110a02801404180460101920101a0009203d9031507440740000410061098801600d101340e038404032801d0505001d030203500140512035803540b52540c42c69030181401c4069200141c003601840c2000d00d100300b0050b8052030b102042110b00d8a071180c5545994800c4004d040482c8031700d00009810300743d400e100395210001040820a0340c003150703511002d43c0d00c200b8078201d0540e600394041600d682c0c80f442100a40104612011041840c0e42802404140468041c4030300c5070f4130007210441004014200d555550640e501c1e5080008a0801c1c4403140c4250080071302e5003d042e95a1800301d03541e00c0010f0171190b01e680240c420511040040590 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 656708426 1250 656707176 656707189
    0xd020307110705030726030309060a0e03090f09150a0b0a0314010506270307031a0714030c0903030f07050c090907030b01090e0a12030f0b04050906010918140705 71
    0x798440041000a00340781c08a5900c90850282c0301c03009561201480b42c03617180c21900d05514a821041e2610303030800c101d41950721003003030382d8100007a0b0070000d028285c0d034400816201e0601001304400003850300e44040c04591075016101e0300110450a6544c3e11540301c83c20003000600200034800d80c0d42e210b20a00508a0f554030401c0d2010305010300c0100710f10b58954040d035140d100c000c1001c2d140f02041488450540031900601da425010f0f201c0700009220305211011a0000c030381c5540c0320745940302079084552901e2071514145c02030003400400c0e500c4100380040d02c071040000d81203c0c50203030030704094081500031020803103056122140303915883c01e0445030140c100b81d040000b00046c50031540e543d8903000d4140180c2c00c04507035681c5440080e400c20004107252a820900f800303151503102e05e001b4060084a00c090845504104400b0310301e0134140701c0c4c140720300172410291a0590900d4032081c09000c41002d10a540003084081c04049103030510004070303e18003a0006e142d40751815091010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 656709676 1250 656708426 656708447
    0x11d1011070c1716060915080f0a15050d060204081c020a08030a0b130509010b030307020d0b0c0403080f120a0b0105090d1509080409061a0706200d020307 68
    0x500381400d200240010304480b001c038041d00c51221600c904440205506031605013540001d2012001800740002c1154000f1428810f540c1102c505200807a12004d0550350024181c40ea10100c5802e000011041da146030722122020307203004d4030400c0c101d81d280e001a00e0840c9007282520744680c0000e08002c0d0402c100704000c50302e06004400c1d00380c107244400107526980e0300c0380060480c3c20000000742010429a01080d2600030043c1724083d200c01075030500d8002c00c000c0700c8440b003640ca8104044900e00d030000640703c1a0768002d09401c0c040c80203545100c0c0300c0b04c01504111048509002c0480000c0c010000750104402c0c100550f80c45881c62128003843c1e040107080003229034a0b00002043c180d0b0310104840c940402510500081d44407031424020101100a03019015450308424034100541d1174014030072a45001400e208064803800c242d078032103a2005441d801d002c01040480001101c640003041220300e0b00481c800c40040c5100150740c161b00812144c00020342c00010070410641191a105 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 656710926 1250 656709676 656709701
    0x70e04020f0a090f060905031902150304050c0901080616050d15030f0b01050109181d0f01140906063003070c0e070e100320070f0201020706080906070e03011d10 71
    0x2d44c0765241c000441d45030509c0c14044078130721940b06850410340d201d207075110000040c00c1c4000742d507070324050614a448081a4840500c10400d0000000340d01ca000100140a4400684c450442d5491030b4000d4079030303910000c0442c054a1300e468402140710701400000000754000e402040720004a81307400c042d402016040f842c18007403005410303c203010540001a114282014001409400c1d40e0514202c0704201030b82010148900c00804031140b106402418154103c0b91100c8550b4984036070b03c54541d181128410b801840c411009000404601d00b00c4210301540d892502e00203400400e00e905591003448143d9620005040400c15400d00d014070a500a07004d02c0c000002d061074400244110306410705220400d41c40740d5464000080c00140c460300070510950040c2e48039000d21300044c01b4490301c6420703805405030791000252540a020742d548542c0c5460042c10b816564018280e03020750641e044150107640e40c1c4800c40c0004180342484004020200003000400c000e501c419064400107107184 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 656712176 1250 656710926 656710937
    0x13020a0603021e09010309020301050a021e1602060901110706080403140307090b03330a2c180a0c0f0807120f1b09020d0b010302030f070e04020f0a090f06 68
    0x70401011042da0042d0703c000300701c24142d6407000400102d000d00407510000e903255107070005000c03010b4120f41c0141004861042810b803400418000b03044503001e40410750f54400f080d0f584600040c40c10314000c054900050400003501c1c0c0d520144030340707007a406420680200300040203000c03c0c5034003c0005d03c841c001c60165203103580b0f85500000d00140c000d22035a1098100400030508040e100440540710b0401e5030031841c1c03802800c0180c0070444003100035460086d9040302c40441c0d01c24240040019221180004c620385001000304000000402014400550800b00400750240e01c00d000454a1a0042c07900442490401134800400d61a81c0e1020185500004041259000d440b60301c40344640c0204c6100c80b050030604184401e03181a14080c4c0e95030740300c0500072a200050354090020b10042c070500700102d4040400540c1240b200356101c0507882d40b60b03400110303194440c1030340148000000c0c0005d820701510091420031038000c1d01201010440d00107041c4000b00305c41c0001802091140f410 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 656713426 1250 656712176 656712187
    0x3030c090f0d022202160321060302090c0310240306171e0705120a110d08030105060d1407023307080a1e0c180b03060d0203100513020a060302 63
    0x200f141084d0064a0b03207240d81e07081c02c4032100b5425415074404101407030b954483c0d244245001030500c15003244550308001d8640c81c0074078002076807140030240c0340d028101c81da560711004c1c1006410f0b0001840c0b48e03100001d602000c40c003030084131000a190029400c00754100c1c00b080501900355107440d005005480d40d528004400200001040200004100c0c1510541070b144c0002c80e040041c150030035034100350b0b00300c0b0040c1d010200082d045041402441040c02d402d05003010441c4144031940050641c410a000500540c03070150001d0001c2d000190000601481000d61601c070414215110009600040035821001068001100c00d00420070540d48014600c1d101a4104440140101d02013003203109c0016218003c50344841040d0360001481e640701051600804050f0400c1341d00200004e8050030b0600205440c1c99000c0140d0341c01d0800d05065540c0c50090007003280c00c0d42000c2c5e07418070130329882809c5841144203a0b0b0181884c1c4000801101075030040c0b0522881d107074404000c05104005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 656714676 1250 656713426 656713429
    0x414040503190c0b0c071b0617070c060e0601060e010318060c0c05030301150905030f07150e1801050f060a021506040905100c030c0f171803030c090f0d02 68
    0x1c4510340e1a49404202c05440350101c203c95080c01d41400516964081d001c2c03200c0d82045a001d030089034071507103112460701d400e811036500e254141e11441010030009600c8070258010041619403001c128508000f4a00c001e880d5141501d4800c0038403901a0001d90040c040b2075440740071040c001d242800c0511156560100d00c400400c8020406041555205aa4040c3d18030035101035101a821404a903203a507164020000d5a00054181c1e801244140c00002030504000c610284003807200070181c004680781003040050030070917000d44010011151000141582c580071950000e50038101d4a021a60501d000d200702c5080c002c140038400d139030510801404a81c0010800d81c21160214801750b16240c140201c2c01525480900605600030051403e800d0344090340800d40124850ba414424141084070039524840c40198800c00502611055805206c0409840b0b4009000c491042440c41726080090f08540054400140c4117100056200d01407070058400c1e0483d0f00c0483d201d004441c1142d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 656715926 1250 656714676 656714683
    0x423011e020d06030b2409090a11060906070302010e010f0204050307171e0114070302041406031803030906070908160608090c0405070203040609350c06070803010504140405 76
    0x14202611500003a07440c80b0140c40d90011802145e20110b0310000d410180d9600b150005509011282041c0b1807a020101c5e00d010100e0a000c1d04068000c1c180038440d64440c0b40c2402400d0340c441d500704004121034110f640b240030040000a000354000501d00c03445a400e00c4c25290302d403903194070143c0103100911240d03030007181d00e504480c2b12140810411255040751030820142080405c01d0164070050540349a8064103c085009038415100c4c20325590070b0030990032402980100101842d602c0e0810450b400c1403c0210340010700040c48141440315000000e2955001700c5140c1840d402100602070010340000c58030015011020150000c44c03101d04869076842030a1007000200600c0c4404114240070a008210b042c090152040c08146010f01d80171f547e0340e04c903220310303070004459007030002d80d0804199801940a03040c0c2d02186101180c440e0007200c19070700d020f004940d07029161b0000d10036600e0000a0807040c3c45031071303090703100c0d0702d440300308400c5415424890104002c0381040000085010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 656717176 1250 656715926 656715971
    0x120408070b1c060905011412060a090f0503030130081602010e190810050f040b06121c031805100e0a020901080312160905060a17042301 60
    0x1100712a22040c1a0110500d90840d00c001444650320b000c001142084940e000541030758418158026581040c02c1801000c1e40c4082000d400d80c1c200401007900c0d504160402640c0b1070003400d50f102d80c40107680701c903811544281e000782d0320407150343c2d0001c034000506650b4030503460b5100c40382694503080c2e071105c1259200d4040302030b58144420038114216030003a20300302e1900b040509400318203004801c518200c07046034058168207100b1560300d80404055070085e107100b003c0c01d0400700c0030f5403295964901081d0010f019140d010000204158030f035102007145003401c1104411060b408607410002504944c2c0c1c00c00e200150004603003021300480d0380003138000640040c0c0440040c4a002186144e801e01341d454100a42c0018984000980b1040c000040c100c00845403402c107106803a400410303400c0d241c01e220b402d000b00c2d01182d001c200a107025805048200441e0804007000409041454007410302200d00726002c1c85044601c0c0d468100301d031040007680260ba8002c021102c0811030180c05103c50 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 656718426 1250 656717176 656717189
    0x403050a0e150c06041104062714100303080106080f06010e030c120a06060e1e0601091a0a0f03050c0d0209121504060c02060c091207032312040807 65
    0x1041403008290302c84009003960160800282a12140b074020440d480e4102039a041d5240300c1d0010003c1c21510341407040100b29032405565035002c0410742c2c00701e0310b80c030200d1030b80034080795031009182c2a40340034100c51480303404c0902a040e202030851030081c00c1480180c10850070061220200500990000d2040303800c8142401c000790321040789030009242100392007415800c4000b0283d0101c031208001614040b8a00c00c843c20b0200580300e030f8101301c860307a00f00c8006105c1c4aa441c004440c00581c043d520b0340004e4185043c2d11a00d03110f07000d01d10781c043e800590100b1304100281d11103800d40d02c942500d0a01402c0c0c5414803850130840002c043da40210480d020210740c1c00039540c0c180b40c0e502801b12001990346401d48400c0d000501111155410407201500c1c0c2c1d41c181140070085600c0421510302c25070f290740d116410f005c03010702440741a41d50f007001e02c00213200340320021001c20600544801007901c40d500a400e0455100f54050030860714040b81d8019007824041485440c5000c611071003070311403 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 656719676 1250 656718426 656718437
    0x307090b070b0f13060e030a021c09060c0807050307080301030218010501080606461e0804050c0a0b0309010c170c0f13060e0a12230a05011404020405010b030403050a 73
    0x10b4101862880f42000c104c020021843c100d00c83c000e6000100140049910503000e480c403442d4128054101c00b1425407018000405002003031000c5c0d402240798104090150741214204801c81e51907514541c40344205403804000480108111b00d030020102c11500d841004880c0c40394580b00011b400f191000d480140710705004140d00c407001c1020b1308c4001450f041c003100070745107684031000000c0c880c001b05005048601e0810f1000c503400e00038030050404141407050720360b10350b15000040310750031400b61003242c0740e01840044404c00c2c0d950244800c00b409007900d0095a0341001c5d0300040c2121680000141409510612086000c01b10440319611464403a912507039618040c45115461090141d0010f036951520310110b80305501194501c03121200b0303200140d1680d1503082048849001d084001c0c50301050000d0f6a402c460440343d03c2021700d480700308607030000c102c5e0340d901401c1d80c600d4101d1148140c1d00300100002d41c40c20313008180c01040e080c03510a2841c249510300030164403420300080705001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 656720926 1250 656719676 656719681
    0xc070b040b0916030606031a011a070201031820100903080d1506080603060c0301230604050d0b09070f180504031701091409070b0703030b180103080307090b070b0f 72
    0x10b414008040c0f0803190359034003150181c6a01c0c020f001082d950000340c0380e44040c0041801c00b10448880740c5c1c1a10943d4051004100902406000641c05a0802c9041644408100c410b8032450a0300d0041e0034450000302c907a18811140c4a107002a11010451080c041e4000a02440f60060481404e4170342100c5055614005059440c02a140d61a0203280d1020039a100152140c3d1011400b07000b080c00301c1c280d900c252a03882d01c0b04003d0100303024149241d034140c07900070080b80d01810325142245025000500b003d51300d5001071082000d080080d120b00c08030f1407c1003400801480759030003401403440c4026166040c41c4a1150040c00c400c40f090040741c3e200c0100d01410701441601e4005800410007004540c1c40e01c4840020713110012284003581520000300d14651400704454007658400d2204c01e040241e50744081f07015064140c2c0d000c1d0040d00d0401c122a80d10000d42c8c0082c0130718020101d01d640c030b06103401c0013001e02c1c0f40e0342e0080320000d2090200400040400914070340141c210980d181e020b4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 656722176 1250 656720926 656720941
    0xd0f17040f05030a09080c240c01062711031324020f120f16030c121505011103090f0d051e0c0a0501050c070308030903071e02090c070b040b 62
    0x1102084400b8110b80b1000c6502c0e220b040c0e000603400e05030b5065805841c1da4454940030710019001c051b5202001499414168400030300100103088121401c900101e070980e030b6003036084050305040080c00b4100c01d018201040a4205000b0000203403403270000145585480301d0074a0b80d0f20f00f1400000d0000000141c100100c5100030441c0e003507501800c01c110f40c0c07110752030b2103003d03c5e5020892000640e038410002a10304800b0010081c80307075034400641e410380503240c44128000d0801841d01c60601101c032485d20030744102481203420720b82810b080c0c0a142420a80050605098a00d5006883e407042151001b00c0d201d608014010103019660100c5144982c0750050805a024903243c83c007030a4406601c070028000240b07214000300c00c1e100c0b2a0b0164813000115124890520a1100f95120b130b802000020140b80040d41c0c408040d1090303a0030200c2d590340f014140400141d00405550208101106610300403c403990411900062203140181c02d0361840803200d4000c1000c1d00c40102c2400241e1030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 656723426 1250 656722176 656722193
    0x2030a06020408010f050a020a020d0f111b030f2a0f101701211b030b01090507030f0c1b020f060403080d05010e0705070b0c070210030e0d0f1704 64
    0x1003035004406546454580c07403580d00030690070010601c03a41c1840045409482c03503200b05c1d40c601200b940549140050742070300352260038280c0c10f180104a07410385042401401449060002c140410b040d040c02e0110204051400e41080c42d8500079801c01c04ca2502480a20718685120101a800c040300401d400780c00503529803400d11003250000b00c413141e540030840d03102101e001c0c001c1300c05040c0211641c82d00c4000c40e980044060340501103c000c0b40000100e6581030114000b001d0b02c200c0c18a200b9103c3c0c4c2c4a90071904203030300c40803840741c40b8400c0c4035005815008203000c0d000c5014081290303480c0c80c9001032401d2454840408007841e084400c034107540750101c501118480c040d04195440750b491074222440d9000c0203034041d0081c0380c1000070601d035010b4040c45002c0c0c00150b8605052003030035103d600f00411701508803c002c8904100c23030001038468010880d0307421ba50382c07800101401c6620b80c050801c20768031803a8081055241041120603002044000c6001d10a1100c008540d514a000e051 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 656724676 1250 656723426 656723443
    0x403120219080703060b0f0405040b0a08070b0a0206010e13023007030314070b0c0d0b0306040605180d080106030e0109170915040806010b070f1202011d070b090d0203 73
    0x700014004004505810040d03460203901c042e5010405640c1c1c0340c4414a0368003900c1801100c00c4810441000390b071070190020000500010711001d03005a031001090320b403400e03d0b80321403110b55000c1011140240c061020038010030342d8155034200c84c640302c00c5503882400b41050091042160540d9a07102603954100004050210100c01c0d201c82a520b1070542e8a0540748022000110404142c5a00501200075a00c5080e400f031031000176522400140d14880d04080d86a124440d40c4906490155a080002d10300540c0030340c2c4001031605141403100d01d14022201c2564880d031000190742c0301e1a41c85024541110740a04d40090001450150940900018403000c0e03c002d2500c000140150160b4005140114049421406030124031200300c045001d10b1250781400d80003007004210b443c0c140030040441c140f2079000c00f5403080c00c1e9130707034108a208041602e00c0141c0d07541001b66541c01d600c116061031040e00e103004019031454282ca442c13051042216040c00f03410b5000421003191001c004219 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 656725926 1250 656724676 656724697
    0x3110f07033005030105040c02010e10230708010e011d04080a0c171201050118120237120b06150f03041a07050702030a061505130b12010e0604031202 66
    0x1e00701c2c502002c010503e070828001c42d84a64078046114501e03034014841c0f070740f29109031400307000000184040a40108201c01480b400c03e62485a42d2189103001d080007072188003130b42c0301c904155060040c1203c0002058001c840d82a0599a0303c103451008222074940c040d901040803aa100c035101021039900e940f928005210014100d1007032118581c101c0034081181036103c00100e140c0c2d0700ea00464407c000852070b242d40200e05d1105000d18050004203032050f40c0080e0a60301014044104915041e00444003945911501818400a410044400802088044810115039075aa05c2e06982e00002400311131080740b2142507445001800010703100740c1d04100c06419100c0c58035080c100082c0ca000f012140704032424400007100c42e030207102992042c076000381c018040007600303641d03400c01001d07022403507203e014071218005460b0740c42052103880071446a102064060081040c401c2e120043c0f07034450002c3e4101401c2e000009000203c82c3d80c09a09032420000c4400001480d0300284111040d04 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 656727176 1250 656725926 656726003
    0x21050916060c0203010c03151a131401320c0709090302030a181a0a031d0705090a09080913020c0d0e03100516050903010b060a0c03110f0703 62
    0x141d098011040b61030550081d00207124241c000e130350490484945031b400d58507800c0c10010074031142ca80402d8600910741490140c0f450412046a240007070b106590140070002e405103c0c0c11440c0d40d00c00c0d0040e4030104c01041c40080841220390301419090402040320081c0c6000c10b41110b00b1000700301020092622500400940c244c50400a403643e00c03000c8090007040680104204000303004403032504544184030847c0d04000e4403140d00c03480390b11002241c400c040e1139880c04040310800b090f6400c4080e201500030218649040f0074013003200d04c014042d801c07280c501015800800c7c82c0c10112140700008413540c0c0c1c1450b803803c080e80024014081c00000a00c50414545100c94002881503c074550484c00c441e0421200b01042d003e07903400700c881c0015101085005051180210003802014000500200c0e1602c4403c021400b036403c00405003000911540f00e80040c180c0200708115148240b802402d0707800b80719060555186524072005000131300a40140b1150884040700c44070111128010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 656728426 1250 656727176 656727179
    0x6090a020d02160c05090c090102030d0b01030902030f0d021e07050409030c0c1d0a0213050f01050904020309030a090b041223030d0b1302070b040b04170a0c0c0621050916 75
    0x5041c0e511355602030680291300d00310220b204464580280d81c4074003016402540380045040d05000a010820301903414152500d9140d40144da06010040013103d01e64000c00c0d60003884803000b03260803824891601401410041243d035031a010986030246c0b0801d81e0041001c0e4500c0c90700300c030a104282e10182c00b504011a01086280400b00300481d05400c00c450f02030103032100003400d0221721561905002d60324840b04200800e0070040d51000070010141040d6091036600360104007a03901c111030f800c189810024000301440d030040c401d500075004010386d030760510742007024004202c1c54000300540280e010000703101c0d0146400c12540c9014040000b80c0340c4401000341444e010301541c6460a204000e102602900c848052003920500749e081040f814a54840c0d40b25000900c002910988403001880e080000b4001200c0c001d01c0b88240707641e00d0035040180c9080000b11000c003900400200b040300703645800c1c0307064000649441d80c0904940014552100855540741084050b000039404030700200 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 656729676 1250 656728426 656728433
    0x705030f0a030e0105031905180115090606111e0a14030a08060108091905030c0a12080105060f0d151509170c0109031b1212120506090a020d0216 64
    0x8080501c5032294841c2d50741080d036030006513003a000807074500b0700c1c44801101e15100280c0c95001980c10840c1c03000d01141e101c8940c032045003503400012091214440d0446d0030400302e4107d02c00c0c00d00900181c82d0040360f40794102d20a503169001c82c0600c8a9111000000d81c40070034082c04044100d961110b8044802802d00441686a81140012070042542d800000e00d40e54000d620007881a40d4801c007070400e4946e500c080c0e042450301a0001e4030548418801c01d241c00358100a032645081c0102284010911513110003000300b0b42c16004030340190024007000d941e030a01a030079030300c3c2e00101c80d00c0401c45101103205059286050390200e400802010241600240c0100070141030f54241f003140c00c80c0e040005500c0c2d5490086501160028005600c100081025502c4800c02c00f05904020021726079510f50500103010800b0040d034490442c50104e0400a8000c00001400c2483c03038030a10452900000143c04460020718280d402034001038103c8229155034122480703030800103000a1900450305 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 656730926 1250 656729676 656729683
    0x11011d180403020c0a0b0a05070c1a0306101b021c0b010b04140105310807080105180c010816031e05011d010e010306090606030602070501050a15050d0f050705030f 72
    0x81d01039000d402500441d40d0241004086130b4103135001e80d078085141c42c0100c401244c02e680a02c105a40c03404034400040b42800310410030820364085030182940340c0c24078408000400500042881c00d01800c04600100550684d4007a5412078044030210110541079403e0a05a00380c800001d0099443c8400424408c440c1c10280c42500d0024040c0105080c94030010350f054442d044801d003940c00c901c1000c0d1814910140e183c03038075520314085d5a690565a920080c17412559801100030f90b5120b00c1080403480032624110845001403000300500c80c0752070000781405001070720400010b010545140303807050283e004411407904038040c2c0e60040070140e51203001050207016146000070300c50000c442d402000c03004941607d40b071201c0300305240d00e16555076000304a60725080b140703907440f035400002040d01440500304030340c007520010429282051030f450456440c00303080d041c59407501d441400307103840c0c884003004840d40c407a9140302c0c40e080c01e0402c149052250340c805589480b548421352140140403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 656732176 1250 656730926 656730931
    0x3090203100903030b0d0206120a18150c0503061809030c24010801020c0601060c050106120305180a080c1302130f031a16121e0608150411011d18 64
    0x70794003000b40d981740e8401c001040d55400c0b40039610400178010074646241c4101e4440c0c01c249198000940000b001d0105142d02803001c1d800d41e00900d9004c030f0310314200118010491800c00c00c1c5443c41c503524081001807801d50b40a041c07101c103000080300180709940c04004440038a640710040341c15003c1440ba90324a404100003802c101050404000181c954050003130b640d0301001c9001a00300381e03082c14070440d090f20240300140c51641d00c1c0c144c00a5a00540300c04c002c8828013903560950b82d02c10701d2020b5198100c0046501e4000e040b0203004210b109008200d80e115800c0844000c1c03d551000e000000203130048130b108007240c28001c0c2c000181e0b4a072101c0d9000171284507481030550641446031a60060608a6803030440078a4400c0d8004034622481d944400d000c27802c5ca0008460756143e030001c00300540c0c0944842071660395038080c4891441007101c28600002e0700075074203083c2b405554007200c0c00c3c3e0608045042c0808120348480d2412000e985600b50b22005d0b103999080e10b06c004165084410030b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 656733426 1250 656732176 656732183
    0x504090c09170d200c1c0213020c06060a0f0b0708040816170102040f120311120904060e0105030c121509060703050601180b0a170a02221d0403030902031009 69
    0x100304912101c041d070f0102000c1451483d005005c40311070901c00d10660280704450002454001041180180e031280880301e15100c0c4a00c1c01a11400c45904403413900c480504547d2060054010810950881c22001415240454841c2da210310113480d01e101c4a01940d0441e8080e8014441c84a8000240c8555442140d0a0302810f41202440701242401c0f440b9901880c04240150102800100100e540c2ca01c0554800c1c6002c50043c01d16980c9541800b00074003544064100024043d00640344c503000703003400b80507840c82d41c1c10b0f19454180025a651711a0082c0740c090400088401d0500d1400d101c1030b0710a00c0c103016040c0162810301c84160316134504840d4100881c1c40c2a000c1007440d403203821341652010780030499000d4a810300301140701c0d0341c01082c44841007180d200c0f030341c0082c40190f4030f00c07038080c140840f1b0241c1c80710499030001c600c0c250850703440c0c02c80d0949103208105c0792050803035003121202c014400c818152180d0401b140a041c015401940512506840d030091035841c0d40200c8401c0e00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 656734676 1250 656733426 656733437
    0x1205010b090f13020d05010c02011b02030424020a020306090c011205010305100b0613030b0906010b0c030414030703060203070c15060b0d050a090b100f0501050304030504090c09170d 80
    0x11650200449201c00b940c1e40704244000e400041d54500000c501407010a000904000b0349004a603201400c6d2440c01c800880180d44070401250b9000180c00b8007000d038415070029609190402c0c0c075011008000610401c0301c0c0b0072200c1e4203001c05000707100c04440d564015050700d0031807401c410096a0340340030782001400036908110109418590744501c6c3d05990780400608202112030080b000903141401005501c80820048041100c072a805d841c40210711400030900300b864141c81075420300030143c3c0720529151040004e031070010780201c00c403010740d042031175070712040828540804d1902e0587e802c0141424400070a1020003600f140d40010b0b80c52056060f101701c0e0f04056482070546905105400740044107202c000703120b1429800a541c0308032085400035103004152604105283c01303444010300f0101c400d0062003066444a4600041c00081c2000351450820342da0082891003103106143d012a40c42c6800c11040703208a101000401200c2c842c0c050b0075a2080354540c07250521089000440c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 656735926 1250 656734676 656734691
    0x19230d020c04020f070b0a0e01020a0c0b0c03160503090f19060b030706020303070c051f0c17060102070b03070513150207090902130509150f060901080a0f062004120501 74
    0x60b140c004c541c00c00644868a074100001a5208594003d0161590200366101c0b1800840320b10b0074030103401c0d500d04503955181901200c2c00c02940001028142103104041001040b8603001a000304600311a203618046540355286400641090304034600c6c0c10302e50040444a441400d4481488010a40a81010447c6104810405030740300d03141e10900001d81c10901c0011038050140307010111190150007951406082408641000340c0c0403088211102d64030f41001003400d9200d038645000c8000c425444805050000010b50b0302c036102c0c800c465054038000300044085100310181e030183d4039440c1e40034940e03c2d190210400d2030199400702400521441c40d0009542c1c880b0b01489610540141c451200000401107141c09010f00800083d0a0711903034050015400d1540d020901c11040c4982044c028282441088145c50060b0701c2007100780c0c004178401d00801d62070704031101c000b540260002561403c2c1d02841004d424401d5088002c2c40c008600050740d02c03102d0b028144110300c0f82000700501d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 656737176 1250 656735926 656735929
    0x30506010f090509101503021302030a110a08160c0b091f0605280b031503100507050d090303150e0901060902070816020616050a030306090b0319230d020c 68
    0x310f40c01c0703401403407503071141000301c140a04941c484a0440c8404074144243c640b40d80100c1d010241d520000d58030303d0b5001040000a10345032140d1189101c111403564681050344000400148000e0100c0c0d1740c01d0710041080d1a0103001d907600072030050740a900ca11007854032070079407511100200c03460b000039444c1c40340d8010300c4031080c40b440064403001407c2454001c0850b08100350740000c416075500c03c01e441c500200c0d00490420156101d00b000c203d207004124020705c181410540080c0307031420064240002d0100180d0420269081240b0102000920150508048000d040c0c2d0444410b03040c954045c0202d1400303804050305e0311842a0708020b00480e99140b041c441244600d542c080c001100c2404010350003c810f070350303901e186400145214180454049021004100010308403604d500640c1020101a01401031800038421114100801403941d0042915100703800b14070340a2034038030f0400c10100846104c2508400742d40c1c558824025600d600b80a82e691685016840503104000f0340540b503 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 656738426 1250 656737176 656737181
    0x30806040b10090b03061206130311010903140304170c030705010617070b0703181502010e060f0c090307031b0503070b1e0a020a0f11010f14070b07120204030506010f09 74
    0x210340d00790f91040c104525100169001d5000503003000c0d032020003400e001c000b0080c2080682c5c020900c6600c103c00090407440c01034030f81542072500849a90400c141030020070341019003524554401140d00e80d0700e40c0c0d00e01e410820704480c0003044044420118440004a1000001e811040d01c607000810010352981c8014000c65050220440b060f4056070092200b426044003400b10320340f0a0400c01c0118240002c3e01c91080c0413608000407035000880300810711642401000e02e0382100b800513000d079041c40320300381e0404140200000b1041d000001e0305085a01d040007039000440e041000c9161403a802c215416120b01c0303501c00e8910a120f078800c0441c81c50340400489003d03401d00741490540b41c04010f01200750b500150816400e40c024580c2e20000320700c40d41411120144140440c009030310381600003400f400b5110020108001c21408012041400b940440b4032981d0800c581c01c2c0310b80d450343e40c100c681d02c0d90301c9506a00f680c000f00300082000000668181070b80c5495440321f0318203465002c10f030704 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 656739676 1250 656738426 656738449
    0x804051215130503070512070b011e05150702060d020304060605220515091e1f170703080c0a0308070f02030904090c0f0308030f06010201230c040504050103030806040b 74
    0x40e07828840000c9101102181191003115106405070b908100d005e45806040203034252101e00d81c20310000d481005c104403a0340356400b42030203004610481a198086824a8660b4040c090080100f600d0301c42d03102c05400b040d03403582c641c0102402d84d552400c07415100030703410554007129024100603002c079051030301e6000c895045040d04090b5015520700c2458801410000c1d204624000c2c482d250001145c440c44034152145d00f502840140400000c01c4280d0b07000d100409524005080360304900311700c41101d0f110130403200240c501d0400d101c11300e04054100600742c1d00050141d440000c4501c00c4100202c3d040030407a0107500c801c0f52903030351600c080c0e44c668082811000141c104000700221850541d010200850280304080c0c8480c1d26021091944a182d4005442860011041041c0c8041400c1c006920a0007840207120100007850f04081c8240c2c031482e031030290f4900a0005480791140d500f0744005107801401030080303581d01c1c180580386580980340940507030b0600f2416801c40c1040042000e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 656740926 1250 656739676 656739703
    0x6060c12180a062a0b0c030907050a081f15060215070f0c1509060e160b070302061b0d060e060118030203120d1812020f2b020a0506010308040512 64
    0xf0044c140c100060100c121500d02500c1314200c190350b280208010902d4188076202240080da603a003021501c017480c1460aa009a02c41c031181707074040c48913640c04115244084030110b00e001c243d10a2900c0c1d04064080034a0103e201060000700152082d40020151403a40c4503c0411529403078880046681820506080d070224413170703200c0e410014100d40c82420a049484070300169801c2d269480109450000c00004103d521681510b2154484c5c01ca0100003000d840e9505450030712a664046d40700c840003400f201c0622400c6450707a0002445004803901a5500d00040000b07540320040030a0680040c0c5e05640040d89102c00c4075400c07011020481c06481c1c00600500c0344481403160004180d101e09046590740d51568030b02a42924102ca15110b030f00e110303480e41c3c0381c81e10091000902c1d0400f100c01340b0310a40c3c00310780c4492803240760b829480410f0007540040005c05100d60b070282d28041030075400070054421180000b0a001503540600190b40003143c2c44c4010034030703c05905641d03a9140ac45007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 656742176 1250 656740926 656740937
    0x30203010b041a09030d03051b160f031b03180b161101020c040f050a0b150930070504110403030504052b080c1204030506040b06060c12180a06 63
    0x24003e039026100c11500840b4035251a6107006140c0740403c1c10010341c45268400303c2c2d02c4005005101807001d030051114a840e820b0302d401e10034610801c43c005040e80c203000d00561000807600c0145407141690042d104100c1e46100c04010300e5107002090800d0710201d0003c1244ea00401040c2529150211114041c0148800640082c1d545445100b25804442581540f0800c00498141e0b00d8070702580a0040030340200056910309051301c0e009803000b010246110300140e101c3e249005040c1802d4850300007040d1440b81c0201e10242e140311041c02c0c8400f446010301f90034042c006c0310050014000080e20000d480030312490558081c5001a400b40380401000315038140005d00c07103400c04100c0001c494a50031019641c0c5d8171600300a4a850b03404d83c1c0c064882043c0060410411401000301502e11103440a00d2441d082c55900e600f501d0b40c84c09040203113010340d86801b1807030395503a00040d2103807121480180c3d59142d0700005135a22030707445241d040404100140100302c6038542101c00200700c0700e00b034480 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 656743426 1250 656742176 656742179
    0x10e011e120209151804050601050d0c03020912061503030405030a0b09070b1303050106060c23100c030b0102060a050c040b03220609140a1205090a08060f0105010f030203010b04 78
    0x381c40c0000001030012581e41d00b80124121541c50fa00c00c0e0801e9803410302043d989080411540c4040c20007005564040c074203001c20b02146980c0a01215400100d00400040005201c50304a0280c03040340c140560021811809200000010458074040c041d441940000a174440d0b0615403640124443c1a91681002c039071100410440707810b16034040203a6080d00e242c182c0710401d00030540c018500f10103000700b0a02080c01001004d2182c80b015044604009050b41541c6d034a00d800420301e40f010f010180d80602c80d0f072002c0d0030100141c1d80c1401d0a08020300104ca90b0103801001807540010741d60051241030081002c03800288180d40c001d42204c03aa403032a081c10036070120390b00d0b44003801c600207426841d108440115032484032a40194800c0001150500641c01e0a98490f00300300c50004003a00218a14800581c0026045c068440d81d401c0072a16903c41400040600420354007240140c050107040040442d0302c81d071440c0c141c8000b602d40541900340c9000460890009004030301028004120 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 656744676 1250 656743426 656743487
    0x50603060a1a01030f061502011401060c0206180f220f02070210140f070c23090621060901050403021903230f0a020a023102030c0403080a050702010e01 67
    0x1c545100b010f17450000c901c440d5592006120513255020b0000141d5507403140745d40300d160b400c001d6401040d640c0741828201d82c0c2c076000070785188680000005001000300007c1d0039034071042040c14503802c0040080e00201301e90002d460210500c50704171080e6900e402c002410802d007520903122495005400d01c40b04060003042a600000c400000e504d040d2002c5c428200c14000c1c002c010662988501c02405005207400303152140100c00c07203d4020244403d04849003036484148250381d002904407081d100b0501502080880f0080540c0c3d55070b030b68081c031001c010100d54150401c81c0124825404c55006e2045c4a50304012501e52090040000d0907400102d00a111503664000b02c0c8050f01604a1402000040341030b16540821a2480560000520481989404107803210860303034808040c01010200144409480d00110602905503800300200380c0c0f00d890401a0350255030b01111583c3d44c0d034140c00c0f01400f16001201d04a0000303600047c50301e60b952248014070030711a042000d80c20401c89196 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 656745926 1250 656744676 656744681
    0x5090a150c050f030705040602010c050301080a110f0d110a0b04050a090b0616140c030601062705040204030b0f013003121e0e0610030f15050a050603060a1a0103 71
    0x4600790100300302840001e483c3e600c1e80009600904079602c8043d074442c90190080d00b510300a400341e03c00d005003070004225011022504900d000c1d400162108981482c000284402c1c0001004680009540860f0000c00c84d0000d4207005c5450103c55800d00d5a584002d154454403e600406400001c014010404080190005051071a00900040c206030514801400102e0070480650703424a180341d60400259007031003a0540c241c000e902074007803513060101c0585100c042d6229410207480c006404056403a0103508000500f0000744195584c50352800c281c10048420782d5101c01c42089030000295800340010701d1084441a00b0340f103814042186409480c0c19030724281034050104006d45a43e03503091901c980c3c42d19888015802c41c910802d2405503046609c3e45001c20820b511030f03024016450680c41c440011a94002140340381e2075214a0302c00c20700280903241410540c242014070645145681007584110300940840300681d8a0300002c0c82541c0e40081070051004c581d0501e0f90b01c55100c0e4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 656747176 1250 656745926 656745941
    0xa080309010f0207051503071b0203030306100c0c0f0e090d0c03050f0d14071803052e021305040f091a0903040f03060b01020d020706020d05030a060e04060f05090a15 73
    0xe00540300d130181c0c0c4001240d4480c054443e0820001400010001000d800194a2039056a008402940d07407401e5808030b5030341d03c400fa000500ca03410404081c815107200c0c1c060500055482030424003c0d503525052402d9184c503a00582d0300c908008030000300050310010740149415081d50303501c0600002600d0580341079001c1141c1104d821000c00c18041600780d903001d00b105101c5412040d03003403441e01c0b0b40010000e0510302c01003000503244143c1000894000550480841d070100c0082d51140d40f08140b00801c02c034031054a4044900125003080c0b8111911103210807203400340d900380324403200e02090400300c2c1d4030000020001030f40b0307020522074409640e104661052440003160700d0039458040c80440c0804c02d510489482c1d1b2200050b000550307043c0020006900507000078003119050039000781d01c440c1100980c0b803c100000c00050390b6804150040700c014001c90741c1d8a081ea0505d803d0030300c00350400308841b86105042a02090b820100040c0440c903d917000344800102949101c100400f40030320 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 656748426 1250 656747176 656747207
    0x2030f0319060902190f110a08030601031e0b03060106090b0a0e012003090424060302070f06060b0c07080f1e0c10050c010c020a0812042301020d06050a08030901 71
    0x542e20040340018140c80241401d241c0c003034005243c40c00c175550040012004454030310030000144460148030400040002d02d6540c441816922540c600340100c0c020440100c00442d1144004d00489880685030700020610506070300307a0f0041e0b0780b140707400c0c0d44107026072241c0d40d00031000700702d44284140b04030312521013000c05244c03c041e144200920180c00f42441120420550000600c00740d2500d0103200c0d03d5071075602055070440b4400c03443e0141003584c00c80d2048105041d00001c0c0c5c0341c01c00c5401406202c145074031103004c100ca40c0c1c4620204100e038000310b07142c0c2c00381e11841c0310100c0d0f51240000c3c8082c0c503010400c0102105c841d440560441883e28010103101c80c4920500d1950b2a942c4805100340544166949501c03440075407011800d503041c9086c81c3c0d041d0740142d042e80010894601c12920804d1000c0d00051207030315246864080202d90364040011b113070103c050882390300e00c190005c0c80c0f0010f80180c24080f040c0c42d00e040080000c050710549000d41d104000300360039035024503501c42a0500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 656749676 1250 656748426 656748431
    0x13140109060309030e09360703030507060905060705040602060f063f160b0a020a030305090c091503010b0306012d08010c030b011707090b0c03210103060c02030f0319 73
    0x1045400304900c10001d03075000b038040d10103d00d50118680d11990b080180b81f0305050400e0410744000103903889070302d103010240c01c00c000000e491041c806160480612194000c081312503901e481c240090494000f80181c600600400b00490b28501032000704c00c0c00349500610001031142004400100f80074072600e0325480745240c41c0d1400c200740c5140c008040a200c0000a03000a141c0361030f071103001030540d412581601078184400079000b0b0380021201d60141e4142000200368031280c1c0c04601c2c1c58068042e55601034502001c00200d480c2003441c40c111640c6c284e0003848030b403210038101a21090309010b02c01174145012440141107400200f00d46010750000c01041002d83c0b1615030b1420340c0c90045900011036181e5228030b0340b80d644020202e4001428004903602420000b40040003038100e486500ea07400380210708088d0552081c030455154080148203140c8143c100d04000f0035190f800d10040c1c1e0002e24103050040200d0001c01102e030000c503a12880b919650b104680360008440041d410b850195 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 656750926 1250 656749676 656749697
    0x20306010c14010902010e010f0203160f0605070c140703030e090402061e07021e0d020f04150f090f05040b0a09050705180a0b0f0d030525081314010906030903 70
    0x498802c00e8400d82c100c0c00002040d0700149000240401044400d424104581c0c000e05800036903000c0180c0b0250800711111b000c150800b42030044824044c410003a003c0e5182a040c842c01c5600200b170356100034403400112074501c1170300c07074041d486511601c405800301d00b40040007030140c64006c0e01d1030b03441032004100d9410442e84811000c8aa010390705408515400081d420003545030425226020b03ca90101c110118504000402c00702210404002e0242c0032107503040303280c4c0d641c94120300c264040c40000038403415030301d011001010140c0c0c030541d04245d151109262405419004040c45607410104540c22502c44130b01610040804600c142c819020f040c4010034155905d81b01045200410030040c002401c20820040c01c40b0080d480041c030580518010307080c06d898841010440542605105480740b003968510316000980e901040c040240d90a43c80d000c1229250143c034038031510a001c0d520098440008202c141829082503010411701c80080200c284613802082507188030b480d100b9801d1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 656752176 1250 656750926 656750933
    0x10e0a030615030605250503040c090f1d070b0405011b05030d09050606010926030f0d0e06070e0a05090414060f1e061807090f06031505090613020306010c 68
    0x1515012100b0400c016415400c0050003054000e8541105091101034010250170000000b0b40f000c0031800400c5c058003000003018801581540c0008018485042c1718a010420114004140d2642030156403581d040b40c1c40184800056000e0594410704201f910701070424005488034100a80742145545d5105142400540c00b400601810460f00c0b0011500b032850f80742a0b428100d00420240c10090155001c0140703505502c0050811030954030007416519200781094214403680c4800f0010223000100d0603c44803950344201d00103c00c840c25541c540c0c882174030807199100234070040c03540410000400c1c411440c0032042d0345e4106209403000f2032014a91980141400000c903002d40581980b0383c10042032400820100328007050841100310b40340342c0580005c00300070066072546070b0f44188000044240e406407000388050316440211848941d9a400001c020b040a84031820415980f8000069541400c61540b4005d52006082d440101c0d110a02e070402504002d00c0541003011015449010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 656753426 1250 656752176 656752181
    0xf07030203040303030506180a0f0b0d0b060a0815040305161a040b09011e091b030506070215010311041a0607060203060a0b03070504031101090f060e030d03020c0c010e0a0306 77
    0x1842a000765072907624605000d8201d500041c0700600400222001800b490440b200711a131000d501e20001444c0c08200084500034000364a0703254004010380705182c18464414090b9101c1e541c12100074521903140d40043d80c403001c2d6019480c000120382e07404900000e0142d03000d0706903200d11510072020344510341c80e40e03841c8124802121343c91924030400c0c031007440b0b800151554411480c200a10181c002c517070405400c0c0750f02400e9a50308940d20180901084941c4000d201c0070301008c08860a410313101d0501640359074054135004054481c2c07000a036448614452494101c80d0803407402c0303504003008000d0001030502c04041c1c0100c0d0f02d404090110942e00c2c0c402a09686024600060301c034600351050008a0685811541c0d80281c18401c000005074408101d509076680030251800e0000c4847c0181c8a0115035005084540404034002c9034442d4010a140302c901c50407411510500d40c440c005500700d20030514413075450b81110132007807010350249484e51400310018000e0100302c2d50300c2e1941001c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 656754676 1250 656753426 656753437
    0x30a080313020a0f080a0b040602040f060503090c0a0302011e110106080703030e18061903080d23040819110706020102030108070608090604060e010b0301150503070b030405061b0f 79
    0x100c0d20081c0800c6019420940c030480082c10b0303101c1080100b5420404030030b9481c80c4410b0000c0039010714000040401010350151001401c807428070184654603242c000d81150001c5442901902c03c07000c048a0b545008070002044a070181c4600280f0b0351940742002c1000f100c421074400384808954684041c8009209030303070080c1000405005850b04600c3d00502c0424003400180c801c141300d9120b070700715107586c0080a0b040b0104071941040504c007420503000c01104d581c0017606c444004035200d0700402d2107400c41045a007883e501007040b074040e1680c1051410081c0c0c2c001e00107580070302c400076400c2100401c80050010906080e0300030030794a00d14030301d000c1540d085500142d401000400030040100003003030180a03070b41804600d5181004000350b0b1014010409011a503d40071020030031042076020300c0d02040040d00030700c2948002401c000c5c0340082485500c0c028407400da400500c01107442c0580307004070340c0311f009401b15441d04500103c44000c004074400260030300b00030310f001d910b603820700038403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 656755926 1250 656754676 656754691
    0x5071b08100c0201020301180c1b081e0313080c010b19080606010c030e01210e010b0a050409050c120c0a030b090d050910080709050301020d020415030c0f0806030a0803 74
    0x703004203808010340969203254010400e41e801480148082e40801742c0c414031000c42c58400080e9428010300c01c5468a02c0c492100501e030603540f1800e001d1000f8030009008014880000d041e80201d10320300400c40e44011206001c8410b5103143c3d24000540c22001892400c06003400419040100710008d0152004600d54102c0c07213010450801003e5014416294010b4003400c190900020a443c00b0300080302501c440d07810480c1c0135084914010340c0c052071408221716090108509000d11511074002c0035a444018422007166200242d04c1c0352a00640721a0755201001c1c10342c21034940c0c2844600e01e200308850f025400382248244490702d03410600c10003940101001426410030803e5142410b820050007020010200710416180d01d42d0001e43c0e92291007403414044660f21000101c50600040c2c00256040d400003503c25004250fa401070025900300d0281040311071101002a01111050382c050004102035272820300c0050702039551254400d501400b41c6114010f642d84814084d8421202c2c070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 656757176 1250 656755926 656755933
    0x60512090f030f0d0e010506180702100203070c1a010f0306051314100614060715060515090a17120f0c0102030a1d0a1e0201031103010b030103031407110105071b08 72
    0x1d410014850085c0407061141800030000c50038450081510032804a0500d8034130aa01000708000b6031080041501c01c4030004011520781c1800d0a009141245200d01580e40e40e940e6111500c6920034071500e141265840429000796a10b980d130360034040c1100801d1004c10600c501707444404154107280b0031304014081030180c840b014401d031541e4100c642d141c0164480394a4a41f024025888420032110074a40021164020380881d41100000d03200b50380010f80c100a60032541600c50f00c1030030260506110481d43c4001c5651621100b110b1682c40c9410301816a1019000421947d080b074014503c040b6030302161443c2020401c801d500360ba00c181d43e24074031556200c01d01c1c400c001203840c140c4121424907000c3d000c1c155980d1240040002c0c546c64525042540303031100011a80a544062407540281071500c0d12036075264a904000e4000340310950105044031681010300169500320303046154000300c1d0b411003030100001140c0355001715008849030500b0301c040f446040359201508005049170700c000c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 656758426 1250 656757176 656757187
    0x3021309061a0a200109021002010c03140603120a0c08070c061d0102100e07120b071107060f080402010c0803090a1b140d0314040e0a0b0901060512090f030f 69
    0x507809840d954144440003502d0030b02c0300d080c04a030710910314003001500c0c40c042002d050165040900400e110000203502c6240c08501c1c0e0f14007901034100591050a54408201180c0040024011004100c1e2000d41c07642102c0b0160081d00c0c4240d010340030440a40c03400d110070158507902e40340039900c41c44041d039003d94940d8080100c540d01280700d90050700341241001c500450400047e50f12038007042502d640d0354680400303404018003000008024000e400760482c01850604103200c070b044080e19800001400c2111841d1080400070700c031001c4988996a01c00b850101e610304860824028008a041217000d01e804800f09209802442c09280584040c10b41080d035840c0c02400040b114650315071003804402e0800014840040180c0795110a840790618442c451a040b500804c0c0e141140b803486801040210b142c000744000180b2401c043c40342000721031990020040c1e483d00034802c2d034000620801c4021100480000110340201d480d01c2100c0c058444500d08505603045855920007004001c41c5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 656759676 1250 656758426 656758439
    0x3020907200a0c090216140f0a0f1b0308030106080730050601080114131119020c0301151715150118030b040219050409030c050d030e031602010302130906 68
    0x34103c0c01080300210451418813422803009001010000203001d80080602e000361100040c410461140d401900f50f50f0000d100d4075080740a4070816400b9a070391550300030380003920a00c510303647c4262a0460121815030b0310341082111804002044042004a510f500078a21141080c3c0f032122009403441c204180b1000302ca041c011141c00901c01ea04004504c03004210405d1002481111210117507100300010340e1140b03000024000d09003c0041654002503400800350b80c51449060034a05513007a00c0d42d01c00500d08150070303200c0d1810700000200512408010481c51007200340403e50003030701940d50360103600380040e0003002300300d6805298495040c0040c00725030703104900c00107044d449116100201d08545409104040040009000742d00b62550b40d9020441c01041c40002d100040080c0081c0c0c4a0745801000344030841c01c11149440b8142014502501a000d0700310071903401c40080d41800704001d070340e08078120300400581c1403640c00c1090300080d20b6011040405000d0102010605c5444c145 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 656760926 1250 656759676 656759693
    0x30c0c06090703150b21070614090603060d050f010501060e040e16030f02150711040c0807080601051b01050f06150c03043b0a180c03020907200a 64
    0x4081510581120b0800e000141c40c2186124503a10340c94800100ca500120100b0640013251400c035482075880954060610740018140307050300da41da9120300350300e4813002e401840e5003d41c01d00030350701a0051001aa02e81015680d280c0500e00460403a4034070390000100d9404c40b107003a0021380c00a45c6440d00c0358810700f800c1c054005485010710041210506540316100c1c82204d900005203003910100044065640301601a00444074064242c1d07034803030651802c0700048140d02b03001c40c01241000005450240070f1100b0501c107055585598081d50b8540b00112600d600041018111440d444044a140e5100b441042d102d50080040f140c1242084070401404ca4041060729014460410050003100c4000c0255002c4642c01981d9803a403c1c5030949800c0311080c03d07a4003580781d5240c40080c00707102e81081621405505540c2c800c006049008405c20740501c003865016080364281a020001401c00b0f02c0c0140c0c1c0070301a440c024a900c07502c81303d0200700000081c100105507104941401c144071080 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 656762176 1250 656760926 656760931
    0x150c050c180406020903031b030310120f03081f080a020a0e0705040b070f060c081f080717010219050d05070f08060f0a180204090b0f0108041511030c0c06 68
    0x700c81c501010107000030720100d01540108010040d54011400301c01649040040d2402d03c02c0895030440344654900f46142d4075007007140d0340760713110544690000d000480d03e8202c001c01c68100c080c00c00c9880041c4c034240c5403080054071118007a048166065213514802502c04080c08580d0301404105402740104020000360f0f401c04541c0f080c052003400f01d125004000c0f1405c903032a0003104e946803480750910240c0005009009000c0074102210500c180e0781c081946840340319858204421040c3c2e8460044002c556070207000e00ea640650002e00a00e084c140721243e900c007004001500e072030303903461080503840110078050000c604007040c10b00207045980100755000c8068941002d4101d421a002401c00740040d101c1c3c0c1c0503003c20207030044191152003042025000880a107504250550003a0b0020f42c4144951124186412000809440c0140040445040c16903d1074001c2c2c44a85030040540d1181401032509541c031010794030b011401e40b0181d0310440a0700d030010b840340141e405141c2001d000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 656763426 1250 656762176 656762179
    0xd02070209011418070c06050106030f1a010806010c0f02060a0e010f0816080603150127060b03040605060303040e010909121106010b0c070e130203070807030327150c050c 75
    0x2034008036943d45450304c0c5071941c001201c04079800d0361640942525641140b100103081c0c0c9061a00100d511070700f503080380501c84003c100801801b05040036401055055401c4a8000754200e80850b00543c441c2e9040034a4500500c071740420580b0590003d0041d920030b85e1454080b41c0030600c40801ca40e0804403c456140e81d03403d215102d440c1c003a194481c5a00b03840d07403000601c40d00360089010750b1410011202d10308005a82e201555840c0c85002c80c801c0b800700c0180780e1401007a0045c443c130a034180502c10403600600c402c241552507540c0c40034041d0000414480e0144002d000000b83c0400014482c0d009108135580014a014176040c4190841142c950100138041c07400044040c0d420001201c03811640351241e0183c565140d00440e60510011707500c218a450410020f0160b48004041440c420030b100314101c0b00059951140181c98800e24840580420100c03904a01c42c1854500d032038000101100c0300d014680c1d1546810703401401480c1180d00014407480300f2320100300e030070840054980c00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 656764676 1250 656763426 656763449
    0x211b140309030f0f090910150c081603031b03050a14041e0507170c03010f0c08150301060f0e1b091309060e070b0307020607030b01090302010309020f060d0207020901 73
    0x10000c2107542d0700e105020f151545003030000b401450070ba0700001900c0c2081d0004182011a0901d50000c6020620074003400d403515540d000d10380c07906801000d200e0340c0030703a1014009082103000700a031491414806020b40c1850b03100c44c903607400100200c07060004003445072400110741c2486180a0301b01e5512101c0d041000b29150280300106143c00000b508040c2d0090310111030720083e290507414403205611240c50b150710f491800240c0400411680c0b40d072032003500200140e1b0301051085068a82036404000480d10982c0401c60075208140240011900503001140c240d44c1d40203902903100c1c4580c00302c841860703c0da00344480c0038110249541c0f005990b0102600b0010a507000501c6030a860b00e00c090001d66aa840710100403581e044410408010000d4408041e0342e1054000c050b807048913907800502584000951850003845158002141a5250f813201ea066500550081582c4070007030307920403000b00c21405181da81000600045510242c0581c8a110f1441404aa400180c000171100340 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 656765926 1250 656764676 656764681
    0x5012309070e04020907031401171212040803130b0c04061d10201203090601080604050c0d080d062601020702090c0f0c121306050a0f211b1403 63
    0x150b95032103250403603011100184140c9506c1019070040074068100554400190000212020008902c60f00da0f601081510110120786e81d6850b89403290007010344030211600b02040100d549440a1030b4072203058241d007400d1098607211245a1a82142c1c040601500060706000079039200c0044c100c10100c03e0007601900c40a44001080e04501014003020840e191040350481210360441024140ca00800d941d16030040d900c0030007007503204032000c141d28421039000080c2d0307640011300345210740d800101900d040c44594007002510b103003c0c502600c00140a00908100002600c6540018034004030741802004012424883e5004a0a0f010205074414400e54000d622841d8010340d014200607e082c2e0745c0c60111135603000c03e020310701405149208901d204c141040750f40005100700c800c000000b8900f10781e00c810480b2a48030f050034280020300c04841c5411414060003040c85c4c0c80d0004041a916000b400000c8000ca40464182082110948449524181e04003e5041d0030703400c009001c0d0300c2c51 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 656767176 1250 656765926 656765939
    0x501020628230f061f0e13050907030b0a060e04060c140d0f05011a22080f0124030507031b0905042f010903110d0501230907 55
    0x3200e030941c0a1425125200100d12a109680c89002012540c060b0300381030751030380300205081035821240e000c88030425902049551a004007070700802c140c1809004020512210122440701c2591348160b00b000400700c2000404440f8001c031886100d000c802084000c0c554146101a407101504c1d4100c214a0000c090002000d0307404450f50040d003214011504080c1107204480001080c0d42e100002c48010600c403c07401c2c10b6402c041945203170020300b8000d91741c0324640104148000004a10460b0041021076080403000100c003a0422000c03144203001d9507203412440c14081840c11030302869640301126901c03540030a0500c0300d51245026103000007806d541d14542d0350003181c04017909041c65401c0d00c140a610010112014001c91071081c0503c1c203080c503001000b8086d0b58290411540700d06030103500d20400c2c00700503410607016514040c00030319503214101c1040c168101079400540082c51348000c80c000340210306a011082c1541d00660700020000000024003420301c0155420144040151 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 656768426 1250 656767176 656767201
    0x102011b0f23030906041a0f192a18081930120917180402071a0c090a06030e0f0706031a040e03030403080408070501150f05010206 58
    0x507110900709045801075641105486081021080009a1001003000b0701e80402068080c000c40c82480c80c9043d00104000002c014801102d846030004581000548a01e60701d55500858121100f80050701840100001c544c2d800c104907113040c1d80c024217043d40041ca51100c0b19901407138107008046141402d201c000c82d11400c882c005800c148415020035001e101018529071a0035070198070840c0c5403180700c8040e16241d2460350103070002c1110b2020b0026040c040303024a6a603690710080c1602022429140c511890700003803000c004c0c54000c600c508900b51154801802003034003604074042c00e0304600c1c008031445403004100034a0120144602881521001111000c1d940e240c01c021980c0181c039810700f40783c0000c15480400034070403080d0001d02e16405503c0355540211016114142880303690901080e144030b40c810300100d510170400180801d101d148910742041c41444503625185d0396880e040e0a490303030084920ba440c0c0140702e0070407080d0001155040180400c1c0007526603031400b100861007 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 656769676 1250 656768426 656768447
    0x190f1206051315081c1e0c0204020d0603050303011701050c04120609031407060e0610081507030b0a0b0309060f0906041704050d030203031008070e0c0706060504020c0604020102011b 80
    0x62a0f2504003444440c4001010080030f80003100c1104c172004110580500305880c1303a0030b264045401500385400100d05c507448400d0102c440d07240c0c201031003104d0703003070000943c484183c01c6221550340c4000710000e48180004e50080c10b00b1103201440d540d0241d40282120000387c20b81000d6481044100100c0c19000c960340c10541d0400800a403030141403c05444200c43d010050450a8002542c4e03c10050640e2007421a050301c0411110b0035941c07000140100282409030580e560321411a04148411042c12258802c446180105001f090718011032689121900b004100751404070410025980400020754000311b25010041c07141402c080142c1c032418003500262240c00012424040d4030a0031089400400010340f0f560365000d0b20b802c000f03443e5042924400d49070302c034440c000982c03008009012000e40b9046003001c2c8494907001104402e0740e0024004689a64a6140000742c5586910141ca425254440601000e1038923100090858000a0a1400e1025046482801180e21090018 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 656770926 1250 656769676 656769709
    0xb03090a030309020409020913050c2b0c0e04030c1b0303140304030c02091305070503031908070207080d0c061401030c050d0f0606032d05030904020d02190f120605 72
    0xf0f000380441c00810060300007108060f410408903004d100b02c0310165004040c80e03d000d10141c583c200007a200f0001e02200207680280040800f480100d04040c0aa400d0b5801c1031041c21003552003030740d40c2c4030b8040500007107034183e010030465180041800701c05015401d05029514001503d04d085a4014004081314074400f030040d2004800241018002c1041c186804d40090a40713402c0d242c841c610744c03010102120100c4090041c0d610004050030000191030000603244407a81c1c0303031074404074100c95400b03000b8140021880303400e20000314000240300980761605144e80d003c0d041405420181c041d90400210401004544001040821400460402038232412070740010a09a14200044103150414010304484e00e080070020030002c07062800040c40790300003800c1c170814280e044006840b10624101070095003040245c02c40c01d292680c024036030b615000b1001401d18904214407502600b015801c140401c174000303d120750386900007404580c004070307454082c4055420b00010480c4011010440d0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 656772176 1250 656770926 656770931
    0x50c09010915051e07020a030b090c150a08060102280606080613080a03140907080c060a0c23011a0306010f1410030b0d0804060e0603130f03090803040611070b03090a0303 75
    0x40c4c078010304421161901e4004080c1c04401d030700d03030801c2401c60700240c4101e45207116900e023003910741c18908401c9148080e140245410520409015158224000c0013181103025480c40c0041c50b00000e8903210b20610b10700c0c10320320141101d1805030700300d580e10703003140074160b02c0325007005165071403980324800c001e0f4400c200d541c41c0c0030210f00640150804489203801081024104100000001200422070349a0411200c02c80d070100e06200c00b0740b0402030880009116000b2480c04a240381d602ca140c1c02c005143c0d00142c41814a00c20750850303a50030340c24442007004c1031004902d480d003045603501505c40b101e00303003e1451403d9103e0b8040c103240b0320107034000c07038480c9901103555001c1c2e4448400c03054043c04490404000340f4140c0780d107501c40d0054501152074910202c0c454100081907a1181006088a9120600c0c03500c3d64594008940c40842c2000a204008110700c0400e00241c001080540c031112410f020390342c0e040b824014160081030103a4000c2c0b040000c0c0c070b9400985800e000d5010f0a00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 656773426 1250 656772176 656772217
    0x203012a0309150c020c0307060e0604171903050a020601080706090e0c040b30060d030815040e1509010207030905011d0a260105060604090b0f04050c0901091505 71
    0x40c240c8071081403915001540751102d21211180c0100f0903001030701086065032162902e0b4202070b43c0ad000908041a0403420a100034848103500d00d0425028008480071140424413040070344040004004c0d00310002403000c152911071035010820300b4003410004001c0c1c810b140c200741d401880d40120b80b0601300c418002c0808210002030030340840380038100c001441507903410007002c450b41101e20009101030803902e50007658015400048658040c1c0c000601070340802901d52001c82d24401c01400503400f81d0000061a50560341d1440b58000400e103a0014140394951001201c0c2402401071900325264010091040041d50000068082d00c100f42885a05800d0030306c0046c10070400c201006412020710180860004502104141480000c1c91003928034446407101c00c0c2640c500b035030000d4012509020520419180f41c00c4400c0014018140000080f66800054240c403410340300003041c48400202040c85590041c4010b021f8442e9050070621100302c044010601c0c4076010800003442c800c03081 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 656774676 1250 656773426 656773433
    0xa11030705070219090e0601120302030a05030403050d06091a060306061b0708070f15020a030e0402030604240305150f01030f0206070503190e01090807170a0b0403020a0203012a0309 80
    0x111103401d402c8050f509a01680f5010b05170001c001d8641601107500c103a600005a410612052565682e4154041d40c1810807502066071281c01c09841241401024061107200440b13911540001b09443d25000c6840780e2914802c104410900c1c07070032802032008004110081d101c10080341c43c1c0300600700006000b030440741c4100b03092080d036403c1524140034032800000c50300c000060f280c007915032075580604220500300042c1e079200b0350038600901103109000351030181d01e082e43c040c607403001c0702801c041000901154482071166820904540224070154213105000b01001014285038004110304840c1c109203c0d03c400070b1205100040c49904408048001c54440009441d40c480d407003812680c4440800c0141040ca18014040300c00003a41c1c149039403140c1d1310034516a0220346c1c42c80081c1c404141001c41032030100d00220340f0303005517215010404000605485400e48078500130340c050405007aa6204050a46800035404e00000440d00d40c00f4202d0f001e105680844c9003464100020b61241c03614 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 656775926 1250 656774676 656774689
    0xb0313060b030f060702150402210316241413150203090d0f03060b04091d16180c09120501060e0c0901020106091b0c06060522050a110307050702 64
    0x41c0301075014052025104488500003030403500494494013600c41039025455415080c9500b01e401960000a0200b08580701c1c0c100c0014442c1b02540b201502c1c5400002d010012550500710001c64400c100020150034003010a1003005007203482c08414025600d2085208292801c064012034442c001d41d0a08420807456810100c1d1101051809540700d00c0e00c40c54064490001c0c6101d42c02040d4604010f04040703103c0d03c21034007a85d143c981d00c40d0070241480c92142c020882c40b8503203402c0d1030400d20140038040d010000e4080403c0340d207103d605e48504041100716898108104102c42a00b401d20700d440707840d0018008000e4501c1001c951106035100c0c01c04030301400e0240c0c403070a844040c10042c000881302890090442d0314084e0000d0084644e103881e40021a81e1100754021445201f50418503850b1203207280c6843d0601a50307001c1410394032100095458210170b841082e80c501c4c0c0f0881d065203102603004140e4010f1100300b0410030201014100e100d2031000816010810400141c05011562642c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 656777176 1250 656775926 656775941
    0x7030f120504030606260a0c14061c020a110d08010306050606070c0609141914060f0d020d0f09020f01030f060317030a0e0a11010c1109150405070302040b031306 71
    0x82001d005c2e0a65514100c401d0800b00c10000c04038485490300301c0c1800300d0002d4000301039030b0b108010000e076610301142011303041010342216901040800c03002c4a95080e8108140c001c03c80020010380d07410f6401d102901d005a50740c00d50070103030809502030841c2500002c1090440723421035004901036980c03000040b07081c403038038030000c2c564000031501041e0030b0340c00b81500040e20020007a9003110501c0c0743c20401511140d87c1c8940c14442200c006000007006088115114000a0840c50401d40c8119015941750442d1602d20740459003c150040ca403440c90080d200003040000c0700f000207a03c1a0041007090210460235418552522418121061654409002150000b0389109a80543d16204482d6442620b41009441c18401405030095020820400301681302d01090070580342ca4005580c50498081e0598540d00b410581c900c9070f031a0540102e206e500181c001c080040c00606c20841214000341004040503c144818481d5210038412a070708101440c810302c4900f040c41c5018809040c94 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 656778426 1250 656777176 656777183
    0x40603050a03030609060506090d06110f07060506090c0a050d050c0c070905040606050f1e041413061d100f18030809010501050f1302092116050307030f12050403 71
    0xc880261040c15815400f42c0140c62031710605010166079201007120f68081c0150032584400074403000e0001400d01e902c04043d000c0d000c80103a0520403500c401c0b403400e42000c4c0c42514500d0312401084240d1400d07002c10765001500008250402050700e0009045020364080d91140964906c04074071001000c400780d400441114003116841030321243d141000e0b080070341d422250542000d00110310745c94450100c210352500540502011000c01d01000040e5056030442c0f904280d0300c07030b20901c00ea20700d020524442c008100e40f400800246207000b400326401030521207008003890b402d13400c0e4903101103240b0403a000b40110200780085e00b40c60000062176800c52515860000c80d80a1081581001d00184a1003ca1001f003246a070307160144105500030f01c0b00d05500c2610088416008030843e400740902c40d1010749541c00c46401d0b40b40c0001307441030201c116050303035010120a00090700500040000740c981a4081d040c524690383d00d03207181200c8454014600032408404081c610b110304140d8005541 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 656779676 1250 656778426 656778433
    0x4080406180513140a020a0c08131a180306010609120303020c070f03030f210e03162111121c06060f0809011a04050c0f07150606020601030c031104060305 68
    0x10306901d0801040c044c03180520401000d8006407881d0031600c20b5503403808081d04e5003000b80e6a20341c1c800c1100d910104d4030542c100c0a283c80070922204910960518409208080740d0312802404808140103030104071621a07032000006200c40ca5101c10100100c941c0c50ba00002c24181c01c0c07809401034051002b14208500c40c00c0b400080c0c142449890008480c0661218050b0041c1d07940e0803a4003c0d116074450020840c031281d48120301300707554494405400c0a1044c0c9040a041150002c2c189450000c20388490040c00d00c8218542c21386001d4884460042c10021244031101c8151a141c254412000c00003500c089220020026018068500783d0300d90101001042d0315050040c00a02c40d000c0e09000060074035000844503001449003090040d25071a80d513001c40060130420010741030040510070b48030002d10800002030300444c06480032a1080309807444001d0b00030014422620241e01075011540716400400200300192142e0003943c0e0090611340c20305441d403000c50098074a80d13000410761f12 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 656780926 1250 656779676 656779699
    0x309120711010e090c0f03191b1215090e03041205030d1a010c12050409060f2103080a05100e04080c1b03030a052521020105040804061805 61
    0x4080001c002026202e0f0f0b03207140310700001c0c808803900440d11195a242c0c10409404a80105006147d01966080c5d442c0c4005000b00841003d94118400b40b0030b02e40c4008609014640e0000d0182c1c04409c0220010048042d150014441c0c1042030701c01d042d0050f40d030780e5031000000343c24070031500030b070010039040710501e50145412a6254040c1200c422110300d4420341c424148400f50f4100403103441652628001c041903203c154180500d1032940c02448000c100000d840c02140c010f17a0010308103403000200071460070f48864002c00100801c0c10707105045152030b50000e074100f0310b855004011040d000517076a0310030f110010145800c0c1c100c41c821800040c01c00040101100042070b4410102040e00c29104550070b40c10a4a407103503940c241d00d60028880355034501d118101403c000074103400c0c055000b05501c2c0500400000994050f2030203184100c07204200b018808100703c030700d6414802000b40e46080d442c0c1611038082c50042504200200020300c80c0140b040070300401500c0b00400701c031202c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 656782176 1250 656780926 656780933
    0x9060c0f040504202a01180201050a020a05010c0309060e030a2003040b070f12020105090319210204051807211407020c030c12121b030c010501050a0e060a060503091207 74
    0x316030f902c004441c203003c0320030028170b0624180104504080085450b80c0c0f107104c0d41e4019501c40e00209141c0007140300d180c10071001700703000b4050700341ca0303804588001940c0d003c2c40c10a00c00b070315142e41d00b0703004980c01002506034080d4000038180710400001450220304e81c582880341d003507200b01d50001c14246e0700850300c030302071245586084800314030425600104100d0150140c0c26130300c0c00c50708402079400038444140c00003050700102481344a80d02d410304801e240e4120f07844410520b0303d030404c02c1e07c2d404113041c4003a0812a00c17400043c8001e82c0055124600043c00400703054890515448030703014103075070507121b500756008800184800400e81d115031a1841d4000c0d6589130044440b80310707100324124200f650509044180440c0031102c0500500755102012900300c0e8404201ca029100d00841d20940b079003c2403020f00460300c1c01c5070010640b54540010040000319a8200e060520701c404240105581d40b0401030003140c229003015520381da10400f46034280320b000c00a0914124001070b400d800c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 656783426 1250 656782176 656782207
    0x40c050105130b0f2a1e2b0f090e0105100525020a0f1a0334090e01060c030809031c141e041b0b040602010509060c0f04050420 56
    0x398000030700c19aa0100021074070001d48000c4000300c0680e50080182c91150030807900c4407a0360041e41b00708440e615007006800302e07410900f40f4926100d120401068403081540f225420701e41074001c2c039001c080d107400d000800b01e0b0490b040c0700f120312848441c41140160b5000300b00707503003000070140340050700c2014003501d80790343c802c0441089104109505020500109080492042c1c4800c140340a4130104203c4920440c0d40c00602201200055080e11400422000140d4824003a0181c1d220242e900803441c058102d0b085034010307070400f800d40401400300b5a4491220701c0300940610f06201c1c0e48c0c035050310081c250300c07a14241c20031400c2da001811300b1140c0c141d01f041075189801c8482480c1559510003240176051681c0c1104038100c0427401203004683c0590b091030031107880c1c01410408550f0b502e400c03c01c944c0543d008201503515641000701e43c42d01845444d620003101001c0030f00c0c0c03140c1c400016071180300300c0c020070784169500d988640c0180780e4802c050003400d1150445035604e450040c0025078 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 656784676 1250 656783426 656783437
    0x100c030e010e01060f030f020f030a1407121707032109051002040e04020d080d15090c0e01020616110a0807050d1701050105090111060703050618040c050105130b0f 72
    0x2599800c0ca4429100d00c401403080e0001c41e0301840c1682501815682c91f4102c0307070701c0000280d078000700140100d10203940900c401ca030741c0352041d002004403804269111781480300ca64080001d110b003c20405004c606005109088017101c1c002481c0e50300c18a190640307515890b80c1c4164002081d0391017510031642d440d44119070700c83c0500f084030301d101840d000e101d0a80c400e40c002c005a904000010900504206981d11080b5125065003420618031000c1041140c10311901e003494006d03070508c00c0081001911401240c8030036480c00114480205d40041d41c2e40501a0101e0068200c1e0402120f03198440c80715010054920005c0c2c0340c841143d03082c02c442682121500b6942c1d03000c0d41c44000c8201d0b018003101c0340185090401824260f10303180045d01d40c2c1d00210412030501891070b101541c20071041c0b008a118645a460001c6c40b030520405102c4107039074150103100103e24080501000c00c0c410184002100d000340b800541d5035003050724250034001c00d0350040c80c41d180042204c4509403000005000c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 656785926 1250 656784676 656784701
    0x8090d06060b03011a09061b03120406150b0c0606060a020a0215040e0f1012170c06150d02010e150702180f07050403030f0e010e0303040905090d0c0203070b0a02100c03 74
    0x115038030050440451b0300c2200c81d1698400030401080d90420061985504014012815a07040074a405503040220108840440790300d41d40c0c451040e03c1c3e085038650000640210310b00e0300d081084440d00b45695010280809100e03000110380386815500c204502d1407025400345c901d4410b46e609070400201d54105009810030300054000003103158160390b00781441481c2e07010710b143c50f4510b414000c1081e900124000e42d01240ea41e80d140d0890003e45008140100e2114001c041d103150048481c40000c0d403200310b06110f2083c6890f0b840151ba44400101402c4004440700010649903c202102a101d8000e0094200b100181558120441303503070350901c00c80500345180d03070b2a643c0580450303640c031490000a000c2030304070714801400c520502411141c00018180004142a500300080c075640081d8048003002d5118010003d80325824071066030b1004a41c100083d005110307038000b07621591180201031401f00b000ca00e0a411070f00c20040003a030750800c0d107420040103010980081c05030400b5602070b17 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 656787176 1250 656785926 656785949
    0x40e0f030a022b05032e032f0f090a0b1005073305060d08040b090f150405010c1e0f02180108100c03090204021306180501080408090d06060b0301 64
    0x7080c0050b103241c00d940b43da101d950784240c950350710007802014107001d10146000c1c0a800c00000c10b4049036091800c80a1030003103603258024907a0550ba40b014006030407140c0300d4001ea2008400706902c0c0ca05161444140840741d500c016502c0c0340d03103000105004074111354800c071162540552160003800030b00380381d8090420a2001035507840c00080000030140e04d0180d1021061254800c00540e03070002d5040030006200800060080d1903d240d070341c020740c00c00c0c1002140002d102c42c86240401d6900c0006900703950302401c000002080f001d080c06948503160504c449808a01e0810008040341070104003400e200785150300003070401542c3d0f0605594202d000d01c000311030001406003d42c2d07050b8101ca070420000d14030000b8900c20200600402c59583c010305858410a500699681c00a00710f42d42d10281c003000c1d00740ca450002031084d1140d2200906410900d4400d00140c0d901443d11603000f5000744c5000e9860201d04041144040044030240c00c140c41d008001c074000c2e109030000c3d8100c1e02c41542030b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 656788426 1250 656787176 656787223
    0x91d120909090f0d1b050d0201021312020a1202060409020f090906010c0c050f0f030a0b06010305070c26070b040b070806040e0c12010e061302100f0e040e0f030a02 72
    0x140e41d42c01d1000c41c0205580103414010307001d40b14003030712070b1140e50205050300241d1030782c0d841b01d28004480c5013220240c0d4001c40c4425041c080442000000c000c02c02504480250380c2d004101d0310341203030140c8201e202030b26441909641351001101e0040640020841d81c2c0c03202c0441d02c0c1291b820121410b44070f25035200200300d46620844003100d08a41003286c2500340ba02e07020402038802ca0400c0042c0e00107800e11418402650305004040c00f140c014091103603140382c000f0005049640080200c01440182969031000c01d080d902054080208a03030500b03000c00c4c044600300740c03500807008024003c07081501000100803101c0542405500b1030f0310b903041a41c41d00d0040000b51110202d5000c050792050b1000361841c9029800d49040d40103503000040d0808041040c5810000201c0340040580350b0300ea481c07002c50802554804031061245000491050840f00052131a1004902144115101c0101c40300440c010710503001c1181d0b0a400b1240e40e0551048040e40719690150b07560000d071442c080 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 656789676 1250 656788426 656788441
    0x801020a090e0f06100905030f01020c1501081005070203070f1101020c27060402280905010203120a150b03010906180c0c030f0507060603030507050f0c0307091d120909 74
    0x2441e40103036110011100c03d44d0391481408074902d0807040c0d040c10030013a0200013825441c1408030204400c080c40016030303a0440130110300d140c03c01517414505100c1e0a040104080d000109034080041b0125101050303a44a42c0002c904d103000c1c00c4d80241140c403d4905101c10841c0118610802c544281c0944007480480d100704104800016107032085c071031501260400c1c1d400300d511560fa001500500050500c0030b600319840002820120481c0c480108590b0520440c0d00b01c40404000c110920080d840d02c00080c03e400c800e44d4000d049a01e80d5038a0701855854152410b80078030141103101000b940300d40e56400000040c1816107c1c0c0590301038841c90303a50300f41085009000346600f1540707417000440340950f81116038070489496542005028800031000402c103001d503400842c0207582c0d0a407600c1990400354100000000c8801a5034041015620300f5140480c1e80021275031001400510510b000d00301d403824079080c0ca07841c01507014000800302401602000b608590106841c0c501c02c84e0b07260340 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 656790926 1250 656789676 656789699
    0x1e030b0604060503120c1f05091911040b010e090403081008120708070f0f1104050603030c0a080f1201090903020d020304060e060304140d0c060b010224070201060503070801020a09 79
    0x340c1d0b804d608452601040a80f02e1401044004051011603c2c0c007804403074603d10f20210449400522a00d4005000c244541040483c12070f146054000e507040000b80c1e155090400d00340700180c0906e0f100c0d5003800c0542c1c02880c012441410142c103040e514a00303071800902c844000c0350403100c0b1400c1d00c20013045a010015168a540701c850b1201c501d05110750f1608215508207000403601e02034290082c1c00011a54041d02e40710318442e442c0c1984004480040200756940141054043d034000e00900011081c0040c0c500100341e0800d00d09076031404507045c0c400b4a4442d00b03e1104040b10003500000b415442540244400360190342654918412240200e0700d074455440b50b10000703401d07408546803a18095004681261148403415000030b0407501072401d0003200c4031030070045025120903200b841000e00a02150380030905c05404104022403030f85c00e05c94a545515002000b2000000d01c60600075406100030300402001c481078980c0d18030700d40e4082d601c00740402000508502e80003e40d000d604 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 656792176 1250 656790926 656790929
    0x9050306180618070e0907081005040605061f0e030321192c0703060603061e021c09110910180c080105010c02030c06031023060a0f03061e030b060406 66
    0x4003c0d001251410105110345c2c1005400b55007140034008001030602d07403c000d00007000308a003c010a0380c0c641410301c0b034115032000f040540035a800401000e14280d0f03034202030590b1078050910316040140342001c03d1450040191501000d00b02e2410524114404404244950754210402c3c00302c25258241d68142c41d600e420400840c5008000030300b140c10620155403512600000325448182d80e034a038003080da400c5610076582c8a80c0e402c04401e0100b1160765901402a1140c020f600c2d00f00003020420165140f07180720900a640e40d070940041004602205070408130042003814141802e104c1c1e040218013600c5508040e0403200c04082401070356008100c0e00c00e4854680300c6090703180170300650b04002d0b641d000300d9150245231100c0b8004d65a50300518011034410050100300c6040450030060f9154071000800d25051004180486a0f50f05040314a55101440c003c005040c075964150080d0859820407840c00d0306004040d2045260010302c4000c0f24025092000d5680703901c1c080c0421640e19 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 656793426 1250 656792176 656792221
    0xc070510090f021005071704060f0c081e07080a020619060311090402030f060a050601090801200c030c1906241a04050621060306100e0601090503061806 67
    0xc00d110b0162400d481c4108801d0240e0070302500e0132000765242d0030700204c21803e41003078100124051009541c40710444940d0291410804e5000020751a000003900482d0710300304104844103070503c0508008410780d070020b640494895203a402da4200a5120359048601d8100315840c4030242c01d00c460b250080404827038014424001480c4090281703d030b0000011f005a8061280c192114180d890800c1268800c2d04001000281c80c01d01c900014560015941702c291703141e0500c80c3c0c0b5021f001c1074149005180c80c0c0400f0380d50784c59881410b051704500985141120781d01505007480483d0b030300c800318400800e110311010000710085203e5200c4466420b0302c42c0c441e450000d00180702844084418001200c0c9014640f8201503660340007600d41c0d80020302c0924030400415412071800c0d00301c0d00e0ba50300010100e002c0c104500c1e10080d24a01c0244c2845000c5601c800c0c4004102c1c035034003e0031034202030311020b416a01945084070b01a011441c000050300c4461050783c0c002040407104140c0d80708040705 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 656794676 1250 656793426 656793443
    0x2180121020d1e05091c020303150a08151b0f09090601050d0e0f0d02030405100e010c0f1a18030d0914060708100801051e04030212030c07051009 64
    0xc008100030342140c115011220b6445803020581d010707a14442c001101c1022010400c0d103000342095040011105004411024209015680980105c117881d4070000c042d18042a10506c80002003801d80107038040d00003401240b030782c2c035003120300b52107014803e0300b04241c06603036036410010440040c420f030781e03c2201808040c02408072510705a5802500480b05242c05402c045117550b400d0200ca19604003000f0395846040ea69100700020321207140c80503543d0001c0c50a091820010400c0c410440d040c2c4010450b03c0c6801000d183e00960080d511190000582103854615243c144814440e44101107d410702c02c400140703c400742e4080110100c40e010340510306144030044008098240c01d034049400302c502d04d202032341c1c003042005010300c41c40040da550042402c1c82c000040155109402100060b41001c04110240304c45410300e40149a000c0c00c2010185d0f1079040481c00d0024641203450360740c100109100240c050a800340420502031400d50f058100160701c1038085070342d21000180b40c143c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 656795926 1250 656794676 656794727
    0x121115070c02010c0203010f0c030e070302012102040b1602010e031606030207080702031209120a0c0e071e05040510030207170310030b0f0109050c07020a1403031c021801 75
    0x14400d00125041c5441030401c258280d5181d40002e081d10b41249049500c5562440f5100b003243d03060040d4004041c42c20043c1142034156000241048900c0b0340c1e2a007405a88441042201c2c002d0781101c006054800c5e85540b9611609005600400740c02801d03400950500b0a10485150200c0c0491400415003040351645140c61000d8001e5008000162900d003018014400961814804020400070b4203071880e583c1c0c1041000c0028211540145164951024003000c00145d0740071190401d8a01a026a80c3d40b551205801c0300c1d42450304403107484888800c401c01e056240c2150291003621000c0300d18620700c1d11540f808600b00e019a400c00b405185800c000b825051140707100854020032403a000540c0355499448030062141e0540f0394808580110004000440141c410260480c100c0403281786401825000228540203500902603054144a81c1c0000c6540030030482b0305190441004251040c81543c82c000203400060315005c581c42d2031140c80351990322407a00d504540610305001080c80 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 656797176 1250 656795926 656795941
    0x1410110a390e07030f090c0501030513122a0f02150f0d0c0c1a0901050c18040b01020c1002060108100509030708070602070803010b130b090a032d121115 67
    0x10902401e00c4080c103503034200c122466010343c020820501c7c0141030050307020f842e144c001401c83e5401009408481c1b62a610030300043c1c980644100380c203810349081400300006116aa801e184403d170030b240f01c0c0f843c60042500304036a00c01d201c00d02074002ca4035200700010b81707000443c4500c42c0002c48503a421040000c9580802c580d4000c1c5000300142c50b005802120aa451446403581e080c81020104801e0007081121003090042a82c0701c91504c0a060800d0041501300c0090595400514030480c1c40300c60300e0300f659100f006400c2c0000740c0100001d125116640002c2d4942c1028080e240c0c80d806840510b501e10846400b5681c0111410030040d0700d4018980c03600381c129006808200c405c1c5808101c84004100c00501840c00fa0120b100c0040e6140602040c01030542d0843e40600340c000c0041c450710605558002403030003281c0c0c00c185049505001b40305807040620790242500c1c0740145500045007405201c00401704e0942c080d031150a012385180072595610b46185148030b484003605000907104 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 656798426 1250 656797176 656797199
    0x6030415050c18040603020a03080c0a06020301170f01110a080c0405060706020c1501230a030605091c0e0607030f0e13051f1410110a39 60
    0x10030300946211409490380c403104015180292003001d019000401e1152115080f41000404900c08841c100300883c0ba503800301d403000a90703110103040c4a2001c1081503507040107104450344903600c81001c40d40d075078547c2402c4801c540e80300741c039804610a0030282441b201c3c0503c40c141909240400d4182428041e680442c2d0010005250305010b0b2000d00000807107888030000350100b00d100b00000758807007040d1801d5602d400210b90380c180380702c6100d900400ca8203410801150315913160100d0311010f0724048000c11020102540018002031500342084805c00380401e0182055001849251000291000468840b01c040a5055001104000000019010b040103030302c28205030a00d25111244900002c0d00900d00c651480c8546c0d40b80c03020400c141c0910441c0202040d40c0341351302d600041c02d1545204103051080741e074a01641c507450040740814041d003241020107502e9000c4410100702450034140c0b09820b07036000c2400100808000301413140b050074000c00b402100c1841c0d1511031625600d00b15 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 656799676 1250 656798426 656798431
    0x180503060f01261b100e010f120b0904080d0606020d020c01030507200d110706091a090d050a0209010b1801082e08060603010e0a080f04051f02010e070807050603 71
    0x300c564043c41014183c003824403008001401c090702c020b440c82a40c40501c40c04143c41004c01d4104100c0006e600390a030707080010500007465910308084181da140302190700505006990507480350060301088100604003004015000e112031081c001a0f41e150400d81c1d031840b4500408001d40c00481d801031155101e903008561010451400f50036100404100400140034400c90130250f421658900100e1a080266914141c000b140140100c0c4c0c9030000042240784180030340c020608002c8801c148101004080d07800001c2d000b0030030b119054503494140d0703940c034840400700c1c0075620110000031507110710b105403031100b11584241c0c9014500c0000445001c0002000040c0158800510300c034a013801d4041040c402c101e286021140b01c0c2006402d0f450044000c21491090b8101a1004c00d405008110f41e00116441110551541c41d00d12056140c0c0c0141d8100b1130300071140c1140c00203101400030205090000030b400810111060f03501e00d0b903d800180c060000298070030340c41008a828102d000f10b9 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 656800926 1250 656799676 656799719
    0xb010b070204090807140147041112060405070c06090204061715060609010915210915050103080318030705060f040c0801060f090b060c010c180503060f01 68
    0x9440710603039504d941d1600505001d0b40d60f403d00b42c5001803090402d1140400250300d50000c000941d0814806482c40c0d440c0d0004040c015000c510100c112400c01000207042d820001e02c03d0020b0682410205142e42003a000c0c402c100054101180103814288101401066144c1d00c00345404010345584002c0c4c0403540e42260015500c50f40083c645400c0711045502c0c5071544060300d2000b048480364008210081c102510a0034100880d2145a0f0400e040c0c03030890b24001010402016281c40c1500c000e0581212585035a0b800700c50086c1c001065070140c0c83e40f620030080740901101c010b60f00b10444409000c0104400c40401c0840c2604108042002d0390b981802c0440b80b512046036500c40c200081035890903980d41801c014007042007460300180300038100481c001c106161a080d00340010b070615100300160150303075210700005911071310200c9481038008002406000402c5e00e0050144d8032210301040340d2038142902148070f00c0c011a6036130044001d2410000207900340b020807200c1c14408500c05 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 656802176 1250 656800926 656800931
    0x14031c0f0f0c060510230f043c1a0a050609060706060308070507080f06011412010507110105010b070503030c0a030e0d0e100906210609021b010f090b010b070204 71
    0x440050b0f00c60060621130010016108106480c1000c10b0711140307498032440210004a222122103501c800c620101440700860b0040381d000f510104400720350143c56004281c056005841d02c0502c012640a1181c0c200c400d80d00704514845964444090001902e85a034040e406003c204030524291b4060f1119001c000c108501c0e1540c1981d0301411a0501d5004540c115004503040007800f00605c0120001c0804c400501900303807511180c40c3c0c650030140110300d05254071409020190b110640c4d051100b4880304000c002074140010040d246000e00c00e001482507003040004941c40a920081c0d58640764420300650441d25801c0c2900003a41200f540c9000301550790440744001c070810080b100b2001f0302c81d122201c107000450f0512510b00004243c88081c0024844100b1403207170f000c8048088000c2e0140e040c07000101c044403030303005000300781e00079240640041881d40c11017010044080b00c44c805240204441e0300303888a20016a001e403036000d04a9840c0c5c0c40108849050b0308020010a440100300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 656803426 1250 656802176 656802197
    0x9091e0a0e1009240212041716050606100203130308160206040b030f010b091302030414010e160f21050a020d06061e031101050702030309040614031c0f0f 68
    0x12002c0728030380c14060351105440440e202c1130194100f03002c20544a201d4040d1315110007095500c0480101030b000501e0248040e442c10409510a02030f10030b0444070300710303104103d155030810039a10301d0266078052248400080c0050b0036400002240d001141140556242c02e1454440841903046203c0c210f0303062072031902d0700c0016503a003002800640001c480640d20707030911442c40001010305800c481c80700c20041161400780c3e504e43d000d045901c43c4c00c0f5030160f903d640b14907006c444100da2505d1008698200801e00c103a40b9000b140c88000c151402030052406940d90030140080d000610072403070300843c40d01014082c05440001e103144e141c040e000b212090750744ca034045050001440360035038186560719424421190100842915180c1032038002e40d646045456101000c2700030361201c2d05100740052880d0031520144291041c108005108001c1d2913954030920303203030540d500c501c103100c3d0184914024000c42d49070181c06582003070b0f40c2d44140c0d03030b05e01c001e0544a014201c0003103003e00c0344d00d400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 656804676 1250 656803426 656803453
    0x140c0c07030203101512021302090f0a030506061503100e1b1201060801090c17070c08070602040303080702151302010c1401090c14091306060803030c09091e0a0e 71
    0x10820134401c0407800080c0e03405108105209200180d00440c41050b503040000c0d0260380e4090030003000c088042030060380c03201500b001a52150508007000d0304100540c81c00010321074080761549c0318501c107a4400d030b44d6120800c0d4517844ca1200701c4989201c2c103580c003014440001c1080700c0944c03080c80600c0000e028101c4031030000b03d64001065a8034161038001c0144100e640c031081060040c45a4202408590949413002e000346141c45410080d8140990004100d40e10910000c04640d4010404543c0c9060905141d4043c0d031180c001030b40810500d002007a40181300150603e00000c211000f0000b5445519084081c1c444902d0160f040102c05c803070440210b40641d038052107001d60807000003004145441c0140e001c0e513643d403001202e956134003120a072540340c7c00320641c1d0000c241041c10300d400c0300c43d280074402031900e0303003144050380300200c2000f0f07110407050000d04c50f44908951441d131030b40c0c40f24a4900e101c2100007848100c01c0040c1c0c0441c203403c0c01c0d0742002010712000c0b4152203158a0002 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 656805926 1250 656804676 656804683
    0x703150504050328090b03191a1003060510050c070e1506030a0504020109050a2601021204200306010b04030803090a060e030d11030708011502010207020303031005040c03140c0c07030203 82
    0x1800c01c414158464900c4003158002c14800001c00b40301b0314850071854030407030b2103e110004d8440480c0142e100d001604448141d0625550a40401401446484c1002d08020000c044074040c950091204241c1420010b000e4000c1e50040d015040c014580c0074144400300c11034000140c0084e2039284407032040641980c418000c1c5201d4900b1141c0061146018000140b43d0541d0381c0c0801d0013802188802d10008000d44c01c030f4107200c0c88000c40345110b03040141900e030080c403032940403458140100d001c1c003081006000103080316101c08100540c1280101d41095200c000c01e1181122505041008000041e0110090340d4802071840a642c543d0201e134541c02c0664000c1c1c00040d049410010314000400c40e0303442035000d404200c02c03901d401d40c5000480a0212101070003a00d16100d403071031f04401030502c00d404585006034082c2c180da88904014410b20107030358042c05894800c50408810f40c2201c1e02c0792082c41d200d111040303000c0500d5183c6042c8001e081d8850180c2c1c000340d0043c04e00120150700c040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 656807176 1250 656805926 656805967
    0x30f070b0601080717181f02042303100903051b0d020d0206160c0203100f020319090314030c0408030f12010e01080a020405190c0e0f0307031505040503 67
    0x21400000c6a1801c000010140c200c01001182400950030201c000040320b151143c1c0c1c42070400705101100b004c41d4480394034040c48042e404d1014894200300c558100e420f030300a0002c8480301521842440310250003043c00700b00b007000c100e0b0160300451000072803482070740048442c5400307810014600810b42000c82002c041b0f20780f04401c15800500805100c9504001c0c54800c1803c40c130190a07907040c01d400e510011050003112030200a03040a428040d56000d1201ea11340c1030301003100b08074000c2c4074040b54010b5002100c82c00c2207040200410b9100700040c2c051040010381c1682c03858000d00c050260050181c202811140c804907040c00049010070b0100001c1a682c1002080306880c1c5039001da1030040380e08143c000b00d4000464a00411118000060300215a6411038001c17415a5a180440c1c0b0912003c03d0304031302c40c90030883c7d4040300640240d030350111004c00303a40000c0441034200030f01da41c03550035200003040100a140b0003007810016601442e00140f081081e240b61100c06a10700c0c0084850 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 656808426 1250 656807176 656807183
    0x7140903031306020717070b031b0412020108010b12062206030f0c12080406120b150901080c0a050f131e140117040201030902210109030905090c160302030f07 70
    0x702c003010b000c20780d0104800c000509001c2808030303111895200315920703a4054032603004420b03000300220f010b9150850b40c0c0d940d0a0710340383e9801c0d203031603548102d604800c8803400142d0100701000008143c0300c000c0c804a5400d0314a88807000a0b0f61548001c0c0448010080340c00d91801e400000d21144150f200c0c042d440c02540280c00e0002c1100090a200d002040e80d03901c2003400075101c104410026214000765400c45845007085400714100040d044040d00e0f404007186d03030010011408032900407491005e0101c001007a61884800d54884101d03141600c00c0c824144041441884071000030300001c0001d004200241d2800b41540303a44140414080304040c2510300c041280480034010001c0c0001c84140074542440d0841c0c1d50150102d030321101b50740140c8064109900c822245065480381d120342039074109484064040f845010b180d203402403441d514110f001440c120700009040c6006904580905540b00c0b04c1442c10058004126400041040490550006110002114003800090001c4500 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 656809676 1250 656808426 656808457
    0x10f0e1c060f0e0f1b0904030e04020d050108061807140a080d0206040302100606080117031e0a020c01021c08071b0609110d0f06051003020319060b0a0b030714090303 73
    0x1220f40c034080c100106000103007000e60044043d44008088aaa840076506098520341d00d01d403034508080b01d01100490301a9042800002d1180c40040d1a9204a0494001034190380480c0c6030384420070050500f82c00523024036031001000f40114014a00c004e18050001444400160b544440490904107040c1c02a80540c11100401c011f0540520000504006102003000741c0741c188007010304034101c180910202c0d411090701e096210320003002142d43c600c1c111842d110103481c0e403000607061980400c24403001800342c030182e000154000210002034160a0040301c90403031841030200d40100c4000c005000300240c83c10360204907880d1080301040c15010300c1e004a481d0307106043c4040c1040c0c0384003105000e895213100d40701c0810440002244603a5005002003840d455100b99011103032030702c5e04041e5142c000c9001004020030b403020b0318144540b10306000e015900d00b280c1080392a61080c4512a2640701c2040000d00b01481100084401a41c610480741170610840200c2d1541c2c1150110340300f00b07003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 656810926 1250 656809676 656809691
    0x9011a12130c08030304150c030e01050a0506121b0d1e0302030403170c030313022b0b06040b150a021c11060f15060d02250c05010f0e1c060f 62
    0x32072922a0b0040c019030030081d07185003019900d0301c5120420349a644081580d41d0704084c070040c400e4001d810140301c240003d000c0ea0506811030001407409507030040c0f041609251a4803a04d50100d200c40a06034418500260080000240481d100c9407020440740048000200246840c09601401c200c501950066454605510b0280d200c41039860a0803811803062011001c0480000308aa501105030284044820101d1001c90611420801441c0300306000000c000350b1032126004c9980400e01612000d100c5496242c14441103516001c0c1e201d40001004018458520400c002030804101c0c030b20444111a440307220014680030701003038420000d005143d0041c00540b0400103242c200346050042800c0e400c200d0b107034000c80b40b100d1000901807000800e80160340c11403981031b01d0030f40c45002d950800600b2408800c01800c0e08440003250000c1d058131f008a441d501c1040e0480704030f1290740301c0d04850001c0c602040890000500071002e4085000031500c001b42141c010080303060250700c0c0100702c11 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 656812176 1250 656810926 656810933
    0x203100e0c030912070f151103010b0a12020f0f0304150603060b0316061e090902280201091e08092d010e061b2b120b09011a1213 57
    0x40380181c00c59081c130308180070b040c02007039100c00103d88081d80a0f550305003604a019a1001804040c03001c1c640c495804000026800807600040400550070340e11141c0801500000c24124041c2c550741c1342031071109106014402c2c00711001550090f0040300c1c2000d991412090b0203042d503802d0f40045407201e490b85190041418200034406c10029003192200e0036504180009043c644050301a4001d0b00440000800d864002c0c0c04007000340c116880306559514a810845080314450208030491405001020740401d1061042c40c240f90b07802010041080442684021481c0340c100c019240c0140c2041035402598a0407218084070091001c0d10a030010088400d0340b20b010841803150602c41d107080380c48840d5480e00102d0b454580602540c0340040803100c60a442c04144080544801503000b114110030000240e019516a00d252385807030203069035108034400e8034400b124143c0c11510030300c014003900740d814422100347c6c0e40d10141a4200340c2110407a03035080700d090b0780d0340c960004a000c9540c1131 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 656813426 1250 656812176 656812183
    0x20a020a11060909040204050601170f0403081b09060715090b0108010c05120604090f0b070c05060c0a0203311806090902010207031106120702012901120203100e0c0309 74
    0x445800311001c41c10104041c004c6404078000401c002c1c482c0e03a80d00d0000e40c0c43c0c2e004001c0000c035400e1a1405414911f880b260311508144151070940101d1141070005d260042c0e01c0c00380c1c15611313400903001d50603e6503000078024943c018440c221290000b004a401c2070360514401d000c180d600075001c50350507500d4260210b086403071000d6803e040210400c91410319031103e10f107954109001ba6400900c0c81102d0078581070040485400915000c60042032200241c1d00001c0441703a58010303402d481440c0c688012000e4180b0416a202e00503800a010000c00c0041c2499059140c140d02008070500c6540d8503440c50100300240c11484146c14803150800240c0c58500c1a10090054400d0400c074007407203500040c1d61200d491100070007030f1500c0d0140d542c00361200307026100c04240c1c45210072014181860f000c0c0c040e000300e403070208240403412502c220070501d83c11940031550041c0c50740f050b810549054000603500080a4400c04581e00c640010303880f0b101d4a13a54464000001c41584905041205605 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 656814676 1250 656813426 656813453
    0xc0b0d0b13061401110a140a0312060609060f031b02030c0c0402070804030b100810060303020105100609090b0a0b04060c0c0b21060409050601271b1110020a020a 71
    0x49442e06006002e402c0844200000800090800884041c4c1443d0440d250050034400100040ca00c824500e44101c1c000500d040b81c14400e0b250320b041100c41e0f5400d0802c40d2424440d007030008042e0403040042c5030003548044a100c0140c64003080b030405001801e010340022845100c0140e10001d10071207c01820f008d90984c9840c1140e081d450001c05845400c0d080c056400040c150b079044c0c0e00855a80011044080e00404214046e1080c500b000040d403c0103040d0343c4020340165090500007079002145e420100196241926140c5160b1704155504000708142182d5681003661040c001c284841801c0c00b400041401d90313940da501c441075280030050a5182e902102c8020007c0c07141ca0320228410490741607044d0480341d103540341c1e610000098050a40c1000240450241400104898442c03400402d60030b08120640700c00062010606011511a65801000c00303507011411a005446005402200c000b044101c88901040c9501e0500726808004100003503444280d40c0d10400010542070354 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 656815926 1250 656814676 656814709
    0x42003012d14060c060106080402180f070809120409051f030c0618050904050a020a060f0c0f1128141003050a0e03070b01031109040f030c0c0b0d0b 65
    0x1400c20746401091030381c1001d035001d0360000c40c201c00329030107150b16460103541c0b0084100044548550303640d0740107004102c003610180d000b0b040e124017000030701d0304000c0b080d802031850f20f072070960301d0741c4924080725558400380c440700c0b090260f1101d030803611103044094000303482c2e54600002d29007032500000c201d10590b0381840004c044100c1c0c0170400318044540041c2100c0d0f26051040006480801e4882c610f4001e810550b8401510002e04c000d025000a03684180da02c280c0b400c2507019100d0701c0070740b40b6242c4182c1301400100c2c40800310b07000414107003400050510400313401c602c0791000c100143d0150a01150b16581011902c4000021040820403800600168508480301c00900000c1040c0801c025001800d2540301e40100340b00010a5101e14000c2402c4400d59466448502d031020000c002844142e404c900c610380a40502d00c0c0c5200468081d981c408000304544229940c283d651000f40c040c180c4840d030310103000007003e0449100420301c0ca503051100242c40e0076224100302441805d00040c6 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 656817176 1250 656815926 656815979
    0x71e05010309020a0b03071b1118100b390111070209010311010c08040b070506010506132c0115020625031116030e0a1a070201030b04200301 62
    0xb0242e2103068611080c0d13901e0755055651380e83c2c1d104c41076500310500484c0c800000590b4604809210100909900c0036508031144040030402e28844400d1070350946460b6502c0c008903408006d071f1a031050080105020031381d41100c554610b1074140b4280d441c801c405109407a4182c801154013a0284290003041b0250885076007010700c0303074011074000034050100807c041007010315004141e0141080041c81c980c040e2003981e503039454041e140342035044120201e541d8818000003045501c0d192045c1e9220043c940401a2074500e001031000d2980d03014050101c00a40b0f12081c9a40003a031307200682d000e05010076610016a6440e40c00038130704140242403000e210500d600c00c44000305542d140d080d40954918010501046036901100c01e881f03441c0b044201070000082da40c040542011760466007038011152034071880e0341c81c8000ca49244010410442c80407007044100d0040d03029a100c000c410b617025000240e16840300c0764030038001011014a04618201100406c240042e549001580c1021419007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 656818426 1250 656817176 656817191
    0xf0603020703020d051b060a1b020f03090609062214031902040b1503040501050106032007020d060e030d0603050127080c0f0616120e0a02040f020c071e050103 70
    0x3500c6104404c240e80401c00c00061041102d06c8a018610b00c0b540c0d4082a42c1c19800e02a0925004003205090f0f0082a00e0070040ca9a0403800230402086035003440d009103140c54140000c103c61584040740044d40010103010700003074440d041c07405103e00c0d4500b0350010107150400a04010000d0030422451007640064101040501c0307050f20b14440f2503044d503000c18035a4200c030001e0903001118001401d0075101200300001d209054104034121072071500c5c02c0010180c00040b403d1075028948440c14030b0703c42004110300500340245200400c60060a00141001540007914151350205900036480f0740c65502c140288607081c4151424056910079041040f1103440c0c50b241210010500070b010800c0200f00558254028006501c4400d002da00303403840c926040380c803124000001d90b400d4001a0075803042c241e240c1014803030381d01e001c02d0060082c0f4100b0600e90810000c1e051085e5082140f0b1340a010065880da010040800901340c3d4808102c03050f0410b040e00000320601d43d01c01810107040070700f03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 656819676 1250 656818426 656818433
    0x71b18050c1612021014041a1b090406050d031206170a0f051608070e01061d09091e030a0311070803010e07050c120903100c020c060715050708010f06030207 69
    0x4002120541c000e080f94181c145000f000d03030504400d1056841801d041505840b610781000440340e211b9807040c4264000501080403000b40780e103040700c0c26107501a40304000314042c0600c0c00545140a4020030101e020394444004c61034040d201c034002c6000c1003241c01c4508680180b0f0003401c0c0640400c1c4881081c0d00e55100b002c0c1e90351641e140001c0d01c0074034104110001c0c008140b10900180d084000244040c0b5540d0403041d540e80079603c85c0c14811141140080307401445810b12000d40d459825180c1c06100401c81000103035080031305441030500c02c1d0103000500f10111640f040c3c01c5104038014548486c0300f110b000c0c080c1c48640380100404601080102d000030034100659054580d41c2d03003520b803965940581030796188140f031880d401501c28480300c07440d03c0c00300c84e005081d42c850580c00d0340e880e042440c0c4024241c401810203500941c00c244204440e6052520140c9140380c02102c11100c46602020004200c410651325200040c00010051000c0907600c98403030001d100c2440c085240c4540390301d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 656820926 1250 656819676 656819707
    0x8090a020f0d0201020705040203040c051311070b250909060803121515030901020703030f050403080412051b010c0f0503040302030306091323060a090b0c071b18050c 73
    0x521161040d1a00d10002c1c0c00c0d64030800c201c40c050721001c2e100f1940e03810a41000700300e0540030f101d201d1113035403040312540305603440340a020080d54042c0300490911845555204207003600905541d1010200791034150801017403440d02034215450345418006a0030b0a85860643c0c0c1e440d000449254002c0140c0b01402c0003441101d0342c09800c403442345c2c00880c00d0700b0008541c032a07010300d07900407918003000b440040740e01076000701385551107610100040d0030031141010a6a508076006400706100d48006408941c130000214001d4800d85020b902d000c0742d04000408140303d2030074810641c0e54441071001e28a411140004001c9500d080c40e070300750f1400380d0f4002d43c3ca11006040034025801000400c1228118007407601c012507103c504008200c2544c540300da04155900142c1c59103215900c0803608039001481030351040398204601c2052592007107180543d0b5400b81034110713048514a05880824801c4a103600050151030b1036100540304107403000c0c000c0d01e002030540b400100d000c0020303020b88901e21 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 656822176 1250 656820926 656820949
    0x120e130c020319020c03010f0506090402010c0215070c030c0e010b03152b06060e070203220509040b0f0109020f03010909020a2d080105013002030312010608090a02 72
    0x590000ca50050304480c12811030180c4001c040c003c0b40d94280301840310b0780210324280400390545c001c0044440030740f211015a0130540744281c00101d84000715015520841a22180e6800540000c2c40d85a180d0000d41060b4059541038036114040a03041c020854072140e000003c00100e0030080e400e5041541034002880302a1a07448840e0a40a0807900ca46503c0c1c1000600b1039801c0d01e66a0034000c0c0d0501140030740322004212460780c90144042000345000c40309a0242e81580e009508111425514811122201142c600031500000700050580e6420b41442c2c895440303a246d220356814010303409810b070302060300b24044460052102d84000034940c401e40c2d04440c26900041024811030010640c9200c45402001c21040c1100d4038100d8801c1e031218070901e1180200700c103100c0541e40d0801d1401c0300c6080c092501492095142800152401c160b0b42d02400102d0741e4021074408180d00107490b69001c1034034006040b11040041113681d4009815035808102840604484011540004c504040c01d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 656823426 1250 656822176 656822209
    0x9010e10080708150627030106030b060f060d230f04030c03260901150e06331206211c0311030117010606020d0816030902060304030804120e 62
    0x300000503099a416482d40004c0b08006402c0c0c036030f181e0481e03046038941038191089503800d40040e4140b81907424144a445c040342e401c010500d080d41c440f0b030104555000e80c0c83c210b5600180c28440c01d0746c901041c0c032504644c089802a8134510300c0080e508581d811900030030b100035003031071001084082900b1080008600d581454501d24240b44420f000320340d1001007001d1130070030340c4d10420080706007130540c080490b09201c0a00b440c105a034070200d500daa100104d80807038000611a928443c1402c058280c00543c41c52045070030707010300c044646c0d44181c0d0440240400f801d03a0030b030140401c0b41041e0700e812001001c003131031030149025200d05917540d4070396640209880700406121080300c40c0c86648902a19150402c0d055aa03507176071440800c080c03507589402d0049510740303200051400c0c00041c1180340e51302261504103450b642e403480d41344200005264081815107075481c0c500166210300043d0700c5980b09484e01000c0c1d080500385240220080721504061142000080203d41e40c0d00001642e0480c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 656824676 1250 656823426 656823437
    0x90c040f06081b0a020a0203061b040506090102031207210b03031909380c0a0807061401120501360203010e0d110f07060c0609020a05130209010e100807 67
    0x2515100402c001c5048915035481d020301044c085200c940c0495010001c034021002c452490701c401280d03100440a031040e143c3e54003c104000c00850501001400385000140162810600001000d115240c8115850800590002100c420b003100d04a0b2074411020060410410505004003083c2d43e803040e040100001c2000b05500018580724190b0527015000325003d82060402c1c0c807010302440e06458015000ba0a402e240d441c201e58401000e483c088400d01005152100003030721800c030140c1c450b40e008d4030415240e40202c2c00701c0200007140c50007091407104011042d201428514210b0361521104a4080040035994821b00c4010b2003441d41c00b0f010000140700c1c884544002401451040559042070043e104c107080569004200b01c41d0300c560a80649000100302c901180e00d44500e8090000410035150030700d00440c241d6840b400c0098405400060f106885500042454000519145100b5000204000c0e81d503440260040702c48829070742524074090000c00600b440e6001804c0c84100039 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 656825926 1250 656824676 656824681
    0x21040308041215150602010b03030c07290f0307020d140f0c0a0b0f06090a0902090c0c010f06170d05040b160c030f05010203010f060c0b0403050f0c01020414090c040f0608 75
    0x950400300301d070f24000c0d9241000b0846030103c102d15400428070511001d540f0b00b80802106080110454010064030005450391323500f0108100f803181c6050150301d4175160920303a244c0d191034030040288400c50301c000d40d50340c9038540010000e2400309078034108401c0296201440210005c04820307101c141641c4640191644054aa4140307072018081d030281c1b000030008140000000d4001445002d080191900205540c8000c1400d090360080000207400c800c8600000d0001e0184c003010784046e42c0f0400021403c0303190a14071102740c950320b4001d65205c180c10007255a400d10108040749008850341061401c203440d0410303a000745d00880100300e01a04070f00f400e007410003000b0f8050b040616486032010b2041003840c02c0540c001e4109009080c0c1d4030301c5d065004200980140700c00005c0c282c2c070455140781c55456583c215455000984182e407120414441c02c000c4030800c0c00500701a04511f48921941100c00c400c004520102410004000004010601c96406801122401d40e0f5140c10a420281c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 656827176 1250 656825926 656825933
    0x1020c070e1503150f06090403020304050108130212070e1806060f0a030c0f050a0501080103081603210905060c0310031103031c0f060902130608101205210403080412 73
    0x10300b03503510380c99140c019210115641346014030124003610141d5074075202a902d180c148030014005a402030b015034001c0c00f0400c06980300d1340885501c0050b104500401140d0341e030101e40c6001002c06400c0e8240c011590910640d910007151a030b100c4d0075585c8100800116200d031079103035000607003c4ca00610320f82c100d40c4500d440e4652480c0040d5440140c41ca07903280c0c0c500020207141702d140200c0d80f11b031000c11400116903110321103039410380360014469450150b1102454618410101049080c4940c0310f02c80100c44041501c003c1159104841c0810264103500c3c00c3c50030040010700002c3d0080040c41408040d1440034090029283c0c0014500864012040003d01e1030180c1035000745000c040102d03203107608540350081e00d210301d04844240030040d11010031505901072100b03426075000f0081001c00c940d034400d0b000542c11905040105002e84d407122100318000749490390a407416409403902d502215100f440c0e0028060010542d02e00301425561080341c0d500c04c0340314241c00c0c48011114030050 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 656828426 1250 656827176 656827201
    0x1022214060c0f06010602070f060e1e0f0a060c03020708150103030f03020f0403230c01120b0f0d060c08070c02090a0203061c060507020705040b06090111100c0e09010801020c070e 79
    0xc24840f0007100d18940c2e660a00a41d2061340340105103441a9225002400c02e0103814920403003c001441d40314a44807003444c2a00c580008040a0350010501c00b5800c00c81d210314180303074080c040680e2030341107041c60b90802134501101644807207003981c03001801540100301d030102e142c1500c0d070519040f504900000f038101d0190088802c002883d0500003000070400031003035074110011710110ba80601241e00318403516104c0d0083c64145020403c00740b0903000c0510568425941050700030452103280720802c1c0410790680c890101151407a584895a03150950029880c950040f143e00c0d0070401c0460307950200384100805080005556008008690030350b0b1050340c040310000c40c103c00c80300342941e68207106014000c03e481e4040540101e88010a241c10140940f40310088003800702480e200118004403600350f01c1000f1282c3c03030b00072054007801c4c04000b4043c05503d0001a907480108a2041c81004502681a0700600780340e88100040001150301003844000c45000302e01608441d80c0740381d411002d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 656829676 1250 656828426 656828443
    0x1d13020d2916112107031e120b0d0f06020903120a0e0103050403090b12070809010209061603091a0d0506120613080c12030f06010504050916050409020c01022214060c 73
    0xf00513400306080011039481005486214003c1d41e404245000030029240315040302201040000e4100710300d03007100c40040d007100e03010b040083d28504d0090801e868002c14030740c1c003550884006800054a54583c03a08011820907804d40c1c14000d480d1807010640a84400e620003880c2d410300d5100e40019003414003500300d0f4001400e603112110b98603404a500c00c840380e10200c52000c04900c07034502142c0720100c140300350341011381c024040f6841c0c6070f040850004801800d02e004c82c200181c0410104034140b900c1540314001c0c031410034040e00c40205000781000d80d1401000a4080c0500f002c036800d1004000650301e40150b008440c44151903000e0411044070f200d1040900c66a1203815218803030380c4440c4000314801c0f50b41001e00c000c1c0d40c48010044529124510469921551501c0450100341c0340510b00c40d103844250130a28a840d0365010018240d070060900a042a50b0100d40b060100089100c1551000e8143d2200ca1504d81070065800307048000a2150f4040c040100e051341048008118000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 656830926 1250 656829676 656829703
    0x4060f140702060a02010b0429010c050f160e070c02061210031704080708030c1507020106030f0804080628230a0504020312041d13020d291611 63
    0x155600b4291318080d028000f2040f000d8000c62502c410514801b0380d403845041c1d9031981104c9110800502e000464800d504c042d81034032a8018200c850392030b054104a04074500d402000c12048440c034084d026090030070020312400c00d03c0403100e41e000040e99410211010582d00491240680d20381c0c041c2c40f0468a0207410050039402444080390000441c2d40142046441c1041201c841c192907104840c0c9a0107000403001c65580141d1440340c42400b18044c2d690b00030440c0c0300000724250760342c580001c1103200b03050540e09440c002505001c4204103101c0b540d03000400c003190715030000309102d0b02600500400c0030080b0a035a100c1d5507118101c10000800c00500100004401d80c0c2440780580c0010001030324200c1c8207200350710000e503401842c1c0044c3c40803501040381101e0112003440380c40d2442c5500072f041e00a60040c40040328010b03a252022018410300550760520050b80d542c0c41082c1c103914104491000c50b02210030031210841da020440442d443d145400361a41800d18040c0c1c1c83d101c45070f860309 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 656832176 1250 656830926 656830939
    0x2060705071721061318030c0f1704150f120e01020913051e070503062101050a0b0f0a03020a050d0c231005070203060610050c0d0917010204060f140702 67
    0x1c80d0089842d5041c50040341d00726150362000440c982d01c0002c4400c881003800c8032000200d04040464042c291400b01b0500074240741c110004a583d0320529503200ca482c0d0320b440c08ac0814180040304c001030389540ca0b000c070f5040240d054052041d02401341508003042c48000b980f10110b15422003c29010303a00d03003400191103c40c00c00e69007082c1c0f201802e0202e40c0340c903041c000c1552802040d8149100c46005000580f540b0b46141c0301c050601404000010b01c03210f20154000d8003918840e003d204035031040801d0180014140301e540b04010b0701401110655202d040410400e202581e140f007900f104460044801100c0d400c0c55140100c601e40403540010402024003d82e04159032000041d0800600b046408e601544a10032003a6a24028114013940640c44000003d60f1403d12250312540030300b8034203220341000300c1d20a42c0741c5001c00001207507001480c0c004c010400401140c10b00c0f42a01c448900950415040144c014000c510201d0000e08101801003008a01114002240e0b031070b82d00075144 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 656833426 1250 656832176 656832217
    0x1b06151208040e07080609190623030106050f03070902090f0d2009040b0601110f03040609060905040509120a05130906030b0906060603011e05040e0d020706020607050717 75
    0xc071940b60442d206000d000c14003440000c24040c03050417000d00c04d0500070000d4903d41c0b1004007114801b40c4241c032145e015541c4031404141c407220030a0104e41c24101c1401400ea18403040241829606540e0081d402070242c280116110742d4007242140c280e41180c2e50041c0c4400c1301500154a540b02030a94582000c403215650040c8900026080ca001040701c40c81404014850b0600c00710304411140600080b0008022501640c410b580d207402c2c80121070225483c070141944224110b50241d4050f5001c02d940350400c221a1b034005102d400104003c03a4108114501101d8060321418902d980c0e0b03a025000240d6126040d014406485446c41251b40d0422020b80b6641294020a964003040c3c48050032040001d04440e0b000562038450f42016101500396440c2c00021b03642d5000040001000d0545100082242d0710f0318420840b0388081100104810302c44020083d0a100c2d00d600301d0710454008408004210360484101d60304075034084500d01801d007020001041d40d020300807031458030703521081c903 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 656834532 1106 656833426 656833433
    0x1060c1202010f1a03120309030901081f0602030334120b06132c010626100f0f0e010e040203030903060106080411011b061512 56
    0x880c2045041400c0415180001300f500d11903a0000d0f50b03180c0d985401c0007014000c0d80a48009455410885400382c1c030392003080c028506001c0000c02045101084548000d420611158440c00385912020f000351664010f03510051862503071168045682c0c1c5040318442d00714240c01c41201d4401c030741007055601602a014000b04240d0b02c003440c0489403148401400812103d02c2c00003021420943c80c090000c50400a40d10007600d01f0801908101c880710402e03043d103440307051010a4038440c090103450010305003d0182c61030200c2d414403924000300b41c1c000c81580c0d4198031103076503180c441d000500b40c14014441e100c00e481d011401003009021600d0802d8100e030000d01501c0c41c1079851000700c9e15000c0280d102600146101c81044144144501c070030001030b00c00d2030b050305580040441c441a0101c05000a42903d55583d10b00700c003560780003400e00090551850741240d8100d02e0070b = true := by decide +kernel

theorem cover : BRFrame.Cov 656654676 656834532 := by
  have h0 := BRFrame.cov_init 656654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 656654676 ≤ n) (h2 : n < 656834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
