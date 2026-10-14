-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3488
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:48:26.673218+00:00
-- url     : https://prove2.me/submissions/90d0b4c8-5af6-423d-97ee-3855dc5b12df

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 627158273 ≤ n < 627338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 627159523 1250 627158273 627158291
    0x6040c090329070e0a030b150d080a0e22050709050d030305011e0503030d02030c0906030106121a1e030f06090703140102070f081b10091e020307050d11090c04060201 73
    0x1a00d0002d1910001400130940b0505d103882c7e01e80000c4c00948101191107412840810b281c3e41c00e118a8003690080311419581d40004c900030f4000b401040d44180284201c195500f1116091082c0070700944198074040748594405000f2161071103203030001980150b2036031481c024036034181c0c000703410303141e011403110741d12010300c20020790310b403068860264540e1040042c0c500e048510b4000e540c0044203042540d06101280c40040c0141e0800d030801000281c00020008001c9014018036a10300fa01d048440c468003d84008a01e01c5204100d2607925481ca0101040385518200240e803603103200300d82903805034241001201d4030343c40180300540710011445668414400c041c800c9901d03007944400f000503c041c0903610041c5507040501409000905440345c0e081600091291020950700b0060003d00c601107450181c0c1e800c80c6070b00000d0006d400c0c094a510058a002919805940c4102e0700e051401040e4900300050030400741020340c010350444188102d01540b0000341003900c8a81e0000c0c80b0840c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 627160773 1250 627159523 627159527
    0x40f0203131716150905030a0309020405060108040c0b090111010612022d0f041b0306091d0a0b10120b010f0602150115090803030c210c0306040c09032907 68
    0x1400200242c6120540c5010001a06075020304041c2c0e41c0200d4080b481c0c0c200d42e1215400c6800c0800c00c000130942b98808041146005c0c41025408035090030526803c0c05c3c01e40700d56201e500207000b181076050f400140b44000e03a018000d4175140d40c00a900074400b241e2600e4905c00c240500c4074081b4040d03070913545550760070115904002c481058400c90314035000c6d19802003107484028003041a400c41d54810f00040305291143c400d0503080400d48000c48e29600d0414a40100d8071003034246035280c5180000d071407503004040340310700100d42c2044511600c2d441e00c0e1680300941e21640d0180e03c2122183c0410348c00c020360a40d14a040740e0034030b10314100c80e84d60b445059071101a0040c0c02e1110000800c01403200448102c00c860002c2c600b80382c0910055110380956146071710642e040341c0c2d090b1000c150307000385c01012100c0c4109207086050002185c2022241c044050001402d01840355403661100d001c8248107991840043d900240d040c41c400c2d101180340c0c40c00f2200c1040c1d418018010000042c4618 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 627162023 1250 627160773 627160777
    0xc031e07110114030a050c091e0108060406050616110901080c1503010501021c021f06050a060c030207210b0703050703061e090e0f0f1005160c0b06040f02031317 71
    0x620503c202510391340c2d036460068020040100740004405040c0950701d99070b2900c0d00b4003600354004810020040c1b02c80c5001400c10381c00107112900c00c50800c5001e21590f11540280d03085800b00c80107910945003180b034030924441209111941100990000042080000130141414078041d03c11003145044200e002e1828802401540e0250703020515034940401d841c00f564000c80310b075205890b2404540c8851800c484070344803803c07014a88a640a02052800514a100500e49810a2407423032101d6503019407102d41ca44104400014071401042c4020000c152080480d54041010074407483c0200303014008000507640304c0c00103860700c0c0011500d1040f1100c04c40001a208040c102c0480c9070a00d50030280900701c0d8010201c1c054422400c208100c10420b07034440044500103080d0343d221340080c9900301c50380181030f01042400c040c101c0e450780784c0206038507003c60b4016100c00c400e95205404903020742034640301c2d10081d900c00820804c401b804042c040c0c0800d441101e0740710303401a5270141040e140c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 627163273 1250 627162023 627162047
    0x615061b101440150203071106010f0807060c050f030409050403120b031002091201180201112b11070b0c0d14030a020307140412030905240c031e071101 67
    0x22080302002d0560340040f645441240c0c0b18079948034031602942e00b400f041e80c106a07100300110303010b02c20322902803505110f054094000080d10803415440d04450300d80c0c0d850240700c0c0e241440400040002449000e0040c20201c0105108407595143d556030400002c180c00c540c141d001500d620442004004507010783c032a44c54008008141c501c415101e190300941c400d40225a01c001007003031440800c0800c0c0a07101300004070303da03c0600c940450001501c0d1500d04441030201f500203440d03088507241501601c1c1e110488036a4182e902078900c00c0265008285502108291b21030001c0000d5034850403001404000740c01800d4400d440d043c3c1200303803a4070003c0c10f41e840c0684018000100c10014a81c069640824903207454018801410b40c1e2140b258400e800110780c1400c410848400c2c15005940d44001f00303c00e0ba01e691011200740c14800c2c0e080c4001c190388c200701c040025038200d50481001510400880090348501c410151208480182d001c40e40031030300040c005403120041d600460442ca81 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 627164523 1250 627163273 627163351
    0x1141c020a1412060117120703080424181101050708030402121e060a0b0f010503070305101a041a041d090a0b04080306030615061b1014 60
    0x40c0340c2000c00501d00091003565464000d00300c00d40300300c1400000c1044d28001c06910344000100300c248020641400b09090680000b41010400c1c230700080d504c04241a4007542044607400d80f404601c0414a00c103500700c0c10307890803905011401c04010b415036020301d0014418152a030050400d6401920180580030000d03181030070a000040150a0004084180d208a4001da481601c20740e040d1703c0c1240c99084407021940e1000702044a92030340d41c030568690b2182154503102c400ea000d0002132141c81b008240b1001c064540b000f2420b01d000d0800130b600640440b2459811810076001c0401c2c5903002841003d1040c0810550b880485c1042070444081d00d410720507e41c507801c04040910854607014280315004e104151080000c00c031181c107401d0180b4480d05a003640c80c05c05000700b41c0b40070006801e03040149540104008141c2d941c1d03040350002182054403090b600031400d2030301e0400c940c429050100328203050b26a181c01e155560a103102e0140610341400d1001c04903003040010450707a0012074 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 627165773 1250 627164523 627164539
    0x504110405010e0409020a0b0d0509030313020d02031e0c09010f08030f07080c070f0e070e130b0409021c050f010506061602030a0f0b0703060b0711012601141c02 71
    0x1544a550403c0607000301401c0421140c60681c04200306003041da001b2501c50750041151212440c0500490f50041d0300030000754218204881c0700700d207012403200001d00c42c00ca0115040219101407028081031825221421400c0600150701901c0d4240108058400d650000c008240b20040c8006641901c8076400114244903d40c2d07403103240b030b0b40140c40680d034806040c058a6126070701040761501601e26003854940300b5107032810458003d20003a056205009091020741c0c200c0d00d4185090540d010b100d04041a000c000c9030200d002002c0040002e50407080400300404540c481d61509200c003071042d002c490142506048250803214190342e0554002801c004c4408020701c0345815000c20b500007400e607052048543c2d250042032031101012242000b41c0c8040003903141d09440f0355002081c11150b01482c1c0704c05961780c400c0940d0f80454450500c1447e0400b403a0600c10b01e008180340e207050340c0c2c4516103541c5801e1916500d00340444024030504000d0701420211407221809162241c1c080c00b031132 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 627167023 1250 627165773 627165779
    0x6140103050906131a09010f062313060801142d0c0703120c210606080402060a090e040b01140109051f021009031107050406051c050a0c030b1005041104 67
    0x2401200d004c005855180c404031640c4c400c0001c071107065004070a460300010710114882001400da42441e4011400319401c03d105901175446820040b4464504490044400c0480c000d450300070910ad4220b020a98680803a020000c2c40e169807882c00340010f138031500101000c0180754003442c102c0d2246003014a03401c00128030589241c0d800780c44424400d050070580c4c8070402141c88200c45070036009400240c45c5001c1100039804003051091108003000b07050008038142007015000031000f4200a015207000641d88011511039440301d0b02a00701e11501d08680e091504254101c00700c28001d0b04c0407103411240b000425800340000c0011524090300616404502d04904a03102c1034103c03590741540200014034219200c284180d03203259104c1d0312404030080f001106c0500e841c2d40c0303410440c0642d280c40ca0501544d03845801040d20080c043c010107040140c2840c0c103d0400884907002029074078005004010024440c1c481849aa032441c0f0390840310f80c3d0352041005550034001c000305502c60400c418 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 627168273 1250 627167023 627167041
    0x901021905010b0904081e042303010e0109030c140c0108070c02040603120c110909030403120203210105040c1701050d020604180e120901020601060822030306140103050906 76
    0x4400960041c000040c40e0b040364400304080345400c0380d080340e40040018000002c0c0030080e141081900c0c031035508506060500d00c2e4038611400d18808458100703c1c8100241d41c81e5400d401221001c0074000084c07141d40b01518015150034140e280841d50504101d50403130501c0000100d02180401c16900d0281c0b9884001050701c8c0300d20b0000080c0d0300941c450001101040d00c0040d403941c1300106a0395129200054204a18521900c04ca01031281d682c001c18013031800c4002091300d081e03a030807035178010313440c010780c1c105030320710310030210100c0c0c40c8146640c4000091150300c0000d4101c031030955003480700300308080c8211424080b800a05041c3da003002c00600142c00c00b0041042c22078405080103252944584180529030380780300c600040b041d281c844003e08224144600c03140c010070552914281600003001079140c0c0d5050048804000c01070740083c0780078200020001145d01d1120350910314003907a060080103810706000d001a4208488241c9800d075102c0e1141c24428180140a00300759101e038090 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 627169523 1250 627168273 627168313
    0x507050d05072d06050906060a08061006111c03021b03090a1e1805010311090415050a0f020c100c1119050a080a020c1f020c0114040b2a03090102 64
    0x104003450f01421012000140c00ba01c00c1138002c9542000600c0c1c0b501d41402000044860340d002084550800d1003131002d404040d2080005940070f40c02c0c01201d00e000c41d03110707600d407034441c001c9100c180c4c0700700880c01c0d203068250b1b0042c107940c02815022200b446401c1b213215a00c0c030070042c03200e40000e040541007204006c80c00103984001c00001c2ca00400507690b04441c0011080c101c02c007410207560300b00400070001d5468140c0b0507850146c40d85100b510f4143c94101c040000810422807403521040054044181c95210f25003046074158115200d01146074519990781c0c0916055011900d07140340403910714080c0d1545c54205198100510554a01141c144448503226104444034401e012402000507980c02c003400080310340394005c00540e03000004005144c0714102a0105080001c054194841e41c00f0a5802501c10300b0b080c1030011030340c03440341d580e01c600c07959120310038801700410041c03203280050f0003100107403206058018820b11300034075041d00e0744200440580564452502e01d1075502500702 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 627170773 1250 627169523 627169583
    0x513140a0c0306080304060e10020a0f06050a270501060905150613030605090f01050a090c1e03050715021b09040b0a060f170f070602190c0f060507050d0507 69
    0x5404100380fa03131411010f1450f045a0008000306620820b6007420341442244801c2d00c503041e1006000400e882e80740c45008408100d005041e40784c079000000e5040f8025003040f84284070408000075070801403070341c1c1e0900c4050b0000440d19035080140c00265101140241401000c12401c0300d80b000c0003501c204102d583c0908032021003141646400000f003140c43c81924490051703600580288515034501c41d00310ba000504100890380b80034102004101e1817001002650f21240e440003180005810b000c400105a620003030843c820340b10041003010444115219a0085408803001100d1410103014414165481c10741c00c8002030000601058010601c81d40001d04000000f907101e032900b0b100c06103602640c01807100b40842101a041c54401000741c007600031004005841d0940c14150001d4490001680240c1402c030685005420f01401c240ba0328002c1c402c03201103100d5150b6446000d04590841d85083d5214003401c01548500e6004804451410703a1141c40c0c1c4103403c0d0110b40428411140791 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 627172023 1250 627170773 627170777
    0x1406010806040c090e0109021b010c050d1a09150f0f10051e0703020c01260411040e07032018131518021e01021506180708010513140a0c 60
    0x1020024000c181c5111180c040d0002282c05030759000d80345041091027400c101c00003040c1c0c1c900f2410394491a800420344140d20700000000c2001c030400600000d02540219815911808020901421042540310468440d00079a00381030908814820404c1d0030b80ca841d0720390b82101d0308480781841c0c14410002040301c11b241404030752826101c000914200e40101e901100035903c8503280410729070704a161890780303411074402c0c21a204121400d8101d201e0002c5d00091021850114610b01c5641d9604500d443c1d03c5c0f071008941840e03540c6e0601c45005040107031018103038150100105110b06004000070781d00c480c10300008400da22107610724851007290080a48050072210424443d62244c1d0240014401c01c00e180c8280f410210700400c80150080256501b41c0380c8030315440b82059801041c0d20441e50383c41030111205550742d1000c21311465440042c00a808000310410491030381003106a4103a40050741d01c40200003c124240c41150b60040d0b01c203041e444603d0000d040c19221360029490340d402c0e4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 627173273 1250 627172023 627172037
    0x606040c021501080a05011808090d05070b12160201050c1603140f0310090c0e0f0a0504050f042a0308030a110309070503010e010c0801031e0503030106121406010806040c 75
    0x44481036081140070b801c65425a017201c142d05c002e0000900600311854042c891800d2030111681d91200c240c411410524041c071024448941840814844400204801035213a86c0d20564034087d06545001100c041486400100224040b1881481064800e144d000785991500ca1302c14456400c82c60312070070440402038a0f038801d0b03903000b000c0c1015086160a490807261203040c00c108004900505401c001744040c9001c4441c04981ea2000311311008240a980246922001501250310b0a1158101c9030b00141003005005540148603c1b2070712960064480d92050300900d00c03e1203c54681c402803607a08400b165080c80840c0524008541150b2940310001e40c1d0014400010010b07041242e1340c100715080210200040d003000c0c016003044407502002000760f40b100d141c000d418180e042c00702500095807a007490500c400e00010000f0b060307801c00103d80d01c940e900c0c00b00401c02d68000251000050500e050f14901450405056004400507101c00c145a5902d909110042905c01c01081c100802 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 627174523 1250 627173273 627173293
    0x90f022104080909100b191e050406121d0a0309140306011503180506100501261008010504050705011e0c030518040501031a010e0705030a0b040207050102031321020606040c02 77
    0xb0840003400c0f0225011414030100d80b21f00409003179049030600220301d42040361940d4014a91020844e015600705040102e40020110f6490b4000c0558804116020542d4280d80c1003019000a0fa01c580920a0741e6021549803103600c4800000d4680c941140c06078820401840841c01a1000d542c200302c1505c0d0014100a10819841ca4101401300613111900720b1400c0c8a02114004d107c900038000130709000f00c6001003509480b003a210607a460b19400071290009c2000d50380030780c01d41c0c001090800005d00550400b418055101c504603c00c0364081400d840140240741c1848031030042000040e194429003e1450714240e8940c1d00007110035140300302001c0c3c9105180e1f103030f10440703011b0360281540784603420444845030103180043c3c0140c80300c80204030400c080a944a01202e501c11004080403594080001c0810041c2c0a203141c010541c1d4004000c205608242000d410300d068010101495402501a50380c50841c010103e25401238114400084e020b0409400c070800b8800644103c0303000300a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 627175773 1250 627174523 627174539
    0x10b04090e0712120c0b0a0515040903090e07020f060c03010e0a0b0d020f060c0d03050a1a0306041104200d0b0405071b020a05041107030201050906161107090f02210408090910 77
    0x10300729501c0d04480d66030723803d0001000c5001c1c15090100804c0d10100b0a00b410b90328060400440c0e4461084001c2c8041c00180c1c11620901c01440c10360042d1088511b581070031040403920fa0001d0181f0744000503140e0008104119a00540c140c044000d4144220b100007a000c1c04a1207000503d20b9410040c200b1201e0b041d81c00130044102d0b1817100b5a070008150500c1c80340c01007510650540c0302e9040d445152201e40d196070104a140e040341e8030903c190711191011011802800b005a01e002900f02821040403251055600030280c4100404c02003001440103000c000480d03d00b40d0752480080c079540c25584000c1220028010031500088c941d100090383c0d807001030150f0f010042a0ba03502c88000c0383c41e20405030240250340d00189200007405451603c08132802d5410300b100715600400144019400ba007050070302801010b010600d0080c09070002d44ca401201a6100c4d42007004e9117030400400040c8030000d00c50a9000e50f911014030340c901986101044215440030b0301307107480764044401c0014548 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 627177023 1250 627175773 627175793
    0x12151a1602031006090f1b1101090c0e0702150f1303030204092f040312030b1306061112030c03160918200724090803010b04090e0712120c 61
    0x3c03214480400c0103410a89010252220040c03082c0e29942080206d0b200b0642c58141880340451519020716110943c00d10b486c054070100c980640b4844c00c00c000420018045024a88100410340131200356040c5d940c4114112442140c100e003108078007401141007001100540c038181d90003403070058281034940e100b800841c0c821841102500b281e0400c600710200c642c000712000b800d9540c1710a4206403454841448400b030707103110302003015a526220003403980c403001c2c18000b500080904001c070a4030368501501061300105058414070950b0100006d01002500304c84c41000000c0a880c156180c02d502c50040c08543c0314007000344000031101081d079650003115020340705070950000c07640f0851568848c10140310841c540e0400789003000a5008100d1100d014090079001d040f401441e0100146540c0040811070b60041501e50000700019685217000007810a454106408004550740d0000007669010544684080d160310b0b1150a000700311000400c0b00362011601b0031410104156496443d0b407 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 627178273 1250 627177023 627177043
    0xb01020a0b16020c06130e040c1701050714040f0e091c0206060f0f030a0308091609090b06040615031109060c010c030f02130e0901090b0712151a160203 67
    0x440340c0359014541180c0c10465000d0910017642d00c82e240c07003c0f480f4083c0c03661b00d107030044402c00170800020904011150690b500100b4881d58800b02c0343e14002042da0107407900303850140002d90b400801000d4004207100f11821100f212000400d0705144c01e10140703080600800780a4070703004d221b0040040a19002c17065036007106e190701418807480c0900410030002e0840f0115400b0300d21035802c1c21140e442c0000c2103c10142c00d41072001d503545c1c80d04e502618051200000f81442442524009400328180c0c00c89180984194000441030759040144403c0711a18419001070350fa8010496422034041d5002c10810718000091070f1402d42444003184042e440f952141352641c0d0341d100441011179040c802d080f061030300c034203007585000300c40850b0440b083c2031400750b482040c20500114144100941c48030b81311540c01a0800801d10348100003405108181c4041c100c85e904242c1c01848455a00903980140c030b02e00030030b14031460140c0d0f12451840d00900116010030b6012104600940d8080041c0c03411 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 627179523 1250 627178273 627178291
    0xc04050c16050f0d080705030a0b0f0316061209030801060807031b0e100207081002180307030b010503160e180c030627190b040c0906030506040b09190201030b01020a0b 74
    0x444a0301c05100c034070380311030080254100200081071084003903100b005c0749c0d001040c814010540c501240c00144c004c0068110199240c0304140701e200281e00b00c90340c8841140c1842e120820307451403140420041e255020070040c0040d0403c4010301c680c138082d410641c2c10031a05e290004444a8140c1840e0702024180d40c2440410350511309500d2500e42950341d42041d020603c003501160f0700e06580d0075610318056240d02541900460400e803d500c000120030b208180007400c54010541d2801c1c601640042070141a0183c01410051444c60407850a0b070360459081041100c140d5480181099214400c83c10920641c007850200c00a15907042000038003030312042003109194081c0507441c01010210208540c2c040c0c00908035180c001c0140070114078125000481660b20342d65510300000d100b000c6421680429162540102c00e1140c00a5030300d22070b91140300c072986140c4074500141c0d512120071600c01080040003810300c1c019442508080a82003041c01241c3c03441e15960303515464807404464543c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 627180773 1250 627179523 627179533
    0xc0b0c030d0506030f070b0307050d0f020c010c09060e04020f0d1a040b010914100905030f240c09041515020102130b0901020a260d0c0207170c04050c1605 68
    0x1d06031288181c980003074088009280800188200e1a2103440f04c0c4101505d040011000504490081c01140c0e4120000d40040100107410403005000350010070740d1740d40640c40d000c0320410441c05401a481510101c0d1145224406140200b202035881100361480300e1805000c1205119402d019840d481400c0c01c411981c1081c001040c4030440d2800101c0604200c0340010410985103800b07817001000e2810354401050343c09420042c0e40f25905517115079090300c035100600711b8018001c5013002002c0c240388050084244501120982902d090341d50a070151020400b081c0549050790040d03c01c1031170b00403040042c40e91815019803040305440040050307500040c100b0003106410494502800380540004d091204140000b0764411110000034016003800c440c203186820b00340704030089214031a0740c2c43e5031024148881c1d409040311100c5c034400351180040200d000f5001030700d40410b03041402c009048a0b400710042101804024140c81e20301d003010020106401a2490300782c08007401000201 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 627182023 1250 627180773 627180787
    0x200d020a03031706330712090303020d3908030c070c150509091e0406060303081003080f0d06170f0d0c0203100902030c0405072a02030c0d0c0b0c03 65
    0x101c140303a00108040d100e040311002030400d5600741d80d5020349000d00c00780c4500d070005900c041561719104264014003000c00d00d22445a903182e005082e0300941703110354203841d42c40840030002da174180c000c3c00004462841c0d0800b001910740034001c901000d071602d030321513924291460321821140d510a4403c620783c0c9a00290420500400190307840c020042400003074414030300c000d0300500e240600e0545c0c5202d014841e0209001c80804c00c01c45c03140d035950020340410f0b41410303c1c180004140500c82100820300b00400201c0740c11801d440d0307a086940007610946003108901e812183c0d81d000c52480a005030742c94101085400c0880d403441c4070b4403040c40c01055a840032010803407801440741040420000c1241031180141ca010a640c0d80b0140403500110318030409200203405c00c1d80c4000060b0704285400200000940d200034224250b2035501103104640c1c49000027920300d24041c0c040650581c0c40320a1003002030602d114054104c80c00b80803051806521580d443c00780d903218140401080d403000c1118 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 627183273 1250 627182023 627182057
    0x6021b01020c1501150c05100c031406030609060c0a050412151b0c06090809061c0c0c02030a0b06010e0a08030307140702100f02010e160e06030a200d020a0303 70
    0xc54400448103c8a80350341c984040140c001441076004800c00038604d440d0001c0100c104021030000191050a00030b000312940024010b11462003d44240e10111001c9192070030046040c500074903900f000740100b9907070156080c0f040c0c1e00c03001d801c004210701048005020344800f071002e480280704108070001151003680b071409403030a6548456000f00c0501500b00d100303030040c52000b1000c2e4412030101d414002d500701110740c1c0c00f5440420342c000d140021390009081074204a0411050500c20401042002070b50072280802c2032440250581d0001e401c41001c28a008a036607030001d014584182310000c0c801c00708500715299881500150f0020090004454116104800c1904904212421301c0b107a60002104900900104814414080d6020000c00d10079044018842051001c4a003e6203115003401c416061910070b00e1999459003012036101d16020441c000d00e2600b00240280c2c215014080113000e8a031007000580c0544611110001a2a4005104000d41c02780d215103640d101071b5059 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 627184523 1250 627183273 627183283
    0x50a0605030910050702030403140c131407030b03030d020706090804170d0e06120a060e0c0a0e09060f1207120605010e100e0a090201050403052b08060307050d06021b01020c 76
    0x20f10f4540d90903c2c040000c0140d00105403021642c00480d400501d941003005039040c103100160700d40d003244d101c0024a110035482c5d008129a00310000c2c5085480e0b480c0d903411000c80300b800c0b5085616400801c032a6032104803e4000d40520750007400006201140341c0d60b4000c00360b1080d07020041c9810004040502100140088251702c0b00314200300303a200404200098082c466035100e460944003210200e08908645d50222000d070040c03003980c68040c1402070b441e18582d00300d200c903c00010301d50f081c00c000600780707510043c1c080c0e100030b070041c050f14a102c41004648a8000070310720a61003120b80000e4100d60045500340550300601000501b135051003140060355500625154005000107000c0148149214880d030303010000c080001522150342c070048500d03108940c806081c0d849060005402c0c0500364001580b000c50102c0510741c604105807096925445c116449070307143c0c010355420846400d00d03905401401c0d2007242d00500d0015015030482491280405a010580d400700d85081e0311041040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 627185773 1250 627184523 627184543
    0xe1806190921020f10110a0309061e060f060c080909060112050421020a0b07050f070206070c05030610030c2c07030614010201060b0912030708120a15031e0507050a06050309 76
    0x210500041e1100c01c503090306c074403a2a0005d410907035141501c600340610355100111500c11300e8205a00c1e203a03c4a0840007401c0c950089102042000500050302401426040443c0340e202601070700345082c4008002d145400180503074107014204003903071209400d0741308507441148100b0203a200f48030000c80000e4486140751074042594030000040001c100741002c3c3e00d901c034026240c07065aa07401d001c0c6200702c0380600c02d0020b41100010982004000c2c0041e01101070710310907400c8035400d136207180b417088008100b440060100300300c030b0f1010321402110b000c204a0004807074001e400c401c030008a002e0070541040311910002650b070007060140391240c101c1c00610410910003404060f00f0041000014881c07822654455050714115203400e031000d00035242c11070b4010340d40355200d510325040401c01d08802c80e14601250324040d0710341c0203d09103140c00401d80e0f0700044020341408009a0310781d0074000b44007040daa83e20844070f0000f20342e62540102d030050000d5940d20394036420a10382892038120211 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 627187023 1250 627185773 627185803
    0x3040e150907080f090f0a03051804020f043f030201050604051603050402190f060801091e02033301030b062118070e1806190921020f 59
    0x8410300016a900000c52078001103401d00302d1070641c4880034a2440d04986c0c40303601c4224090b44149030700303041c0c11102914060b20001e014542d0781071500100310403841510b144c074849100c1484280040d000d403d400d441d6480b49422000074170291006079107080801850b0882c1e16000c0703511010304150b0b085c0656504081c0c00d94050040d070034081d00c6851030f90019a1601304066956000500b135650781c0700d844000000d00c1e00c08201c038988403c201e12415025002e164082201c039800000d0107142881580340e101e6032100b1408003d410507092001039800507110810400c43e82d0410621401c40c40c59848848109c0b10f00001d1800c2000c0025080c0d4120400c010f1242d5000d02813451a840c40d81030600e48034030a401c42102c55900c008000c00c9490b1103c0c03190340d10b403013820790103c0e6250b0002c0c50a4001c40152001907046100e60003502d82c0e6401c100d440c4006503140d00710001105249412020101d031052001400200c180101a02c007030084031440401a440780c800004416001d01040c0c803420451 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 627188273 1250 627187023 627187039
    0xb07110102070c14101d01021f0507200d0807030e010609020a02150c0301030204180f111c05100c02010609140103110d170f161110020316020d060e03040e15 69
    0x14171006070403090104495040c554482c070706140503a209100d5541e4014048030b920500c003901c10100001001d084502c0400705554446880254111004414a00d100000200020b00310340300101c2e4205406410303c0705054440c032000a010342c0c01e0181201800041e20010b0301c905044400914050041c1144032005101030300b071190a8586008076410341782c06550119840055400d00900c0c15a0304002601406c0c60803114400c03c01b545101428107001160040c000e82c801314002265135910a100900c10340c080f684241e48a1000c0d002000d60860360b000024055030f513840c45034151040d00180d145076240c2d200040c8104401c03001c8000a11074140d811b42c0308501ca903651040880c410204085540304041103900c903002464044071038103005034603c00110303450752400c0d41801c20007481080c850010440031016448c80001a0740b06c1543d110004805e45803190288124032400f500295500d03515000b101c064541c6c200300030001008034440001140c9042c2810b08415800506030134482d20718 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 627189523 1250 627188273 627188299
    0xa150b06070c05090405031b15010b0a081b0921071e03060908040314030d0b040506030a08030615030702060a06060903080306060c0f0609031c060303020a0b07110102070c14 76
    0x1c14100c82e0b040d200c09a450304266151410018610b0042442c030010408601c51000070101002c122400749a00800303d02d0010390b240e0321425502c5c01881404030014000e03500003008461100f0350b418080340310714421441c7c40304050103d601d41040402400c0e141c3e4000010201b04102002000d0040c884004411203c400c4e0032403400700082c5610000d4681501c600303461003804580e01c1260000c4d9803109031000c408000743e0600d5181e40040820b02d03903051604c42e0311a02814140110713446800c00070050107210f580c550b02c0c40400d40010f000180c00c141e01d07044c0190058012402107000303901a8008040500d4441010070135030f0210f07004101080319609040002403035000650f40c12800450740180c50300710007a5110f1908002c0400c0e661244a007809201d00704101100414040c52980551040d0302c102040f441c040e22000e100003001a88581d55120100d44003001c2d054101005103001200c10361000383d15130036a001081d0988002d070421800300480b185250000581610503a008001058 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 627190773 1250 627189523 627189533
    0x1080d0503040311010b0307090c02010b0d11011b050a0f0510230406020c0610090b060408030d020f0c060127051501180509010e040b01060c050d0c020f030a150b0607 73
    0x800b4000034240a4030000d5042c1c500030a401030120b2190260031101d6041d80d070811100648000420000503501c1e10214007a20f04001500001c2141c2000d0704015201810300111900c80c0c010307003a5100c0707000800030f003030020342e00340b10780303400d03d03004000b11070780c080d290300345641441d4040d482d0740000c51034100100d00410811040d1f01d68980080028416903030340d07061a001a1091740d408a071180030303101c104003030160418480b10541e01c05030000c002200d6181c0074800b8610441c020743c0603607441806a180d562000e03070014a00710900403030b8a82000301401c1d0042c6000c20a80011725108980380600120ba1190081d040ca8003515030010300c01c81c100b031102c510740d80044503a4039040069544190101215801585001b050302a043d54581d607980c0008041c0c3c464141d030120381d601003500c00058843c2c440c10300f650105800001811420f06448000d80788910f40c403008980200c155444510242e4051280001d00ca00500030030030420103480124003201d01207010350380b0a010074054000400c0f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 627192023 1250 627190773 627190777
    0xf010819051009170a090f06030605090c090a1203050306040c05040e0609101716050402070203060f040c0b180102010f1a010503040507240f02010c0c08030402120f1501080d05 77
    0x1c00c2c1001504080a04007002c0901d0760904201c04884006408804554004001c104030307101564541801038807040f00b1001c0d950144500d5074408100340c0418483ca01302c0009168201c00140b090014680e252001000d0301c1c0000c0085e00400d00110800149003414061905001c9051400900c0c25040800411000c0c0024010ba4050503081000668200c0c00c01e0250010300300f286900140510395032030f22a03035032003440c1c8020b000c0d8a041d103001585080a009440085a00402a00c0c0c4c603515000c44213100c0134001c005030390440d0040400a018044540100f01d80b0542140d8507400000c000000ba081d1003942e80a03045d03d516114120b0079001c81410070b50512202440d0031f995944590410a160100c0707074000801840781140d038480d4000540000c03401901076a210021f81081c1e90209a088139940c040820105034040300644c002202403009642c02440200400700d0620101010340c80d001480e91400b18540c00460511200e0a01c00040c03401040b540c0c00800004050484c010214 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 627193273 1250 627192023 627192043
    0x5130905012402010e07150e090f071b02060a03020403060b090708071b0c080604020306070f090b070305070c0303120f0b030a110a03120f0e030c0d0213020f030f01081905 75
    0xba0381101c8003040d442e100313400103e0344491040032209240c0d1602d2041e1801070040424001190100c030070b50740305040109860384208401025900199181d201c19610040e000c900c2c80e0060000c2034000005036942000b502440340181d41c0140c40b1800c518100302103401d0b916030b0a11a03c0709404101405a001c0f241940c003141078a0018240610482c204102e000c8504d0020030103004104041007110002034403612480c001c8003101e10a0711111008e5400509500b40017001034401c90b82405100140300c0104100c500ca85080d0f481e08072580c5038480c6840c0c03290030840014142010390102d0382031031b0055031110700194400f00621001100026030740c0707607030445c0100704500100800002c1d5540c02d144000964001c1c00b00c000c4013030061801000c07103c0410a0101042c1d6205150741c01c0e0030001107550302480301403c4d4050140342030b020030030030f05110380410200540030451440c402040e003014602410031700c0c20500c15541860501410290104010a048000d510508001c18000134904002e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 627194523 1250 627193273 627193319
    0x61206011b021e1801140f060f03090d0906050a050d05130f051524120c031006082415030c0907020d11060c07030e0d060c0513090501 59
    0x110149072014003410501508081d40c4000c40d01c0c08985035003031034051401140c10440310000008404400101c200e81d0a000380c0b141c0ca907107803a0b0214181006141c14480410062040d820700c03109074040038950340200d44040180e0840b41d003a961541d04034220300701400c180d040280c140420184010624040d0103030001070f0070740743c40c003041280840e41d446944458000e0170280301014a82800c55907001599800000241d691380000c4400c0c521a0002406611208942e1452001e4004001c1c0002103001000c045e802000c01c00700465a0800500e44004e41c41d42002c01d415190420385400c104180902503401c4554003c08111003110424282e801803403641c00003100880b200103e840c01c803900c000540c01854000600000c0c0703800050301e030011103250b03a8102500901c002c00d05d0302d481041d10120500c410500940f0006030080c00f0b2420400005040c060004000e0344be44000d59000001550104900040c1d00306a0034401a4501c040e08040344148502d525005030780b00c44001c5407008101d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 627195773 1250 627194523 627194537
    0x30f030d15080a08130504060302060403080c0f16180203070206010b131805090f0c010824101e0201050709031113150f090506091303021002070b01090b06120601 71
    0x46070381e40c0302034203201400202c1e088980c2d54800d480d20345026441113807000584500f000e0001641e1400b40a80800e80f60f000c2c000905140c0756507203442c05500400800000c074041c0c030192400c4590100110604003003410100c281d9a454030218010040d00c0c240c4600c0d0f500e00400401c194250001034450440d01440c0100303680d80c2410400d00780509090b049210000781c1c4040c046c1000300190002405500c09030241c56054045403041c40d07131502c2d00203019000c62000c800203200951022007002c002c1c82120080c0204103080c10001d120044030541040c0421410b10040e000058011511046200580000c00076410260400782294049110040205032800d0804e0401e49030a404081504014002800080c26164a0320301e031101c18064115280890300000a02452070300074030307002d80d502425081264440c61000030603000c00c40800e8065201d0f0340e10341c192100780340c402092003600501c203801095051609071070a40341c02d1030549111345420f00404891303407065048180c1206003420088 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 627197023 1250 627195773 627195791
    0x60b090a0c11240916090510050103091502090609041404290c030c09100c0209371b0201140c0408101a13050a0c09080a081602120d020705030f030d 65
    0x340c5080407107920315170f000084080019442003e500000c1c0200c40031032129591079124401102296040c000c00f40c4400c004003500e04d0516140c3e0300070200d00e00d02404003031401c1107a40224040d1040034144040d11018042004240110760301c1c40b04041c0c403800c00704202072400c0030712401e903c40b014082200200000000c10300d809091400c41d90000400b504001c0b100c0841ca802500c15603811606030b00451840002540c2c03000e580b02050035808180d0300704440d030041e010100004014412416103060b43e1110658411040007140c1c11880020b98000300d040149442080d0f01c448010340107502d404c0c8140001d0080d103c3c08611400c80e10700d2000002080e070780b003807185403007240b8044250340c005e80d42030f049082258490300060712a5500d040240224210684125100c0407180311716011504113002c1480014000750082444c0b0f100b6214820920b030039900017030414201c0030309400306030344141003500700e47d40c0500031030b0001c010440c00384c840e85115a80b00387e00c901c16103003405541ea03601e00c410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 627198273 1250 627197023 627197041
    0x8010b090c0a171e0a2924180303070305070213090b090a1e05210702061305040b0306090601050d0515100608100803040b07060b090a0c1124 62
    0x10a000c000c641002c0c801c2820400182c0700d40d44840707007021007003002c0301340010360081841c05a01d030304907220b205c401c40b0545041151508520740005503948408a003601c0190086100e45414060aa5101a03542d030040d10084030120344c0b802c82d11601980052012801181d00b2074145d070080c1390155030391003c1c41d1600300070200610541d04014946500c0d0000d0040345e039000109401114031450b0380110000041c0c400103482000c5490052050b80f0000c038039051414805031a0000d45180380d0598105242980010703001c1e00440c000f10062044d01a041010b458140039950301c0d5002503001c0d042a0600031480c075100d001c1406558015540600c16004104040050070668594207180300c43c2802d01122900c0c03a8203842c4a00000074440f003020440e2250855120021140d0b004011890a8901000408030f80c01c40c04064030042e917034150304103c540ba44004c0340c0c42031900c8000010090301d011809040008030f6105441e45130320002420000d40420220700342e101c003002c084d0628580e20f452074 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 627199523 1250 627198273 627198287
    0x110705060904090f050309040e19080a120e330402040209061204111014190c05011e050117070521030412020306012304050627010f08010b090c0a 64
    0xb0044c40000c0130744046083c8880800901780c0010b0440d82400b00c1558503034000e030303500034080940e90309501080c501d0001499010041004911500f07109498040207600c40b41121309444201e00180c20400c900d0320440100f0364400414400c2526411901c0d42c03a032200510860000c200a00685e80003a44100c603588a4051f640b00408101e07401c00146042d04e0425816907485017580d00030030744a5481048036000e198011580c450001c6601c0c10700208028131441c00403420042c00074024400c10400102e01c081c0110f82c4002004201b06200c54400b240001c1200c0b416445034a010500017017020f0041404150740040310340403030b144009491071ba400510200b0351007103041c445110015001401c80f01c030f1000390180a000b1400d90b00b560b80e03903012241010107511511019100c0c41500c810b11403409d41c2c801c5e50840c0e000344c8200f801900a401580c03541108803040d9018a0a14004021030340c8025800e03800352171280c009108507092400810142d01d00a411480007100118100c10b000c0e204500c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 627200773 1250 627199523 627199541
    0x20a060c0504121a06010203070b04110d1505190b01020a02060f040b1201030b090c09041410020c071a0a0503010e0c07020612041203060e060609010221030105010f110705060904 78
    0x8104200c0580e241303865a8111520b0202c0700d0340c0d4844400140d00c1c1d40c004002c1d94403c1c1d400510303550455485030341c0c0b10800da52035a2040e5000c06510798860108502e5041e0594070340c0142d07000242c900300615041c10705542171403022009410845c004480303907404a9480e01141d81620220744504500d20221903500640d0005085107a01040034080e8045074046141280d0090b14104242e03115410029140d07020350b0500b81d0040882c002090001e80400907140102d11420240c0d45034030b5054810ba010b0340e211882c0d400f4130360301c101740a00452500105a036904001d08440c5890b11080e190013802034001403142100300d210ba02c0000f2007c03a581c0b412502c04c0d0354014850381d600c000d14550740038082800d4a05456950034132107032001da01e009102d02c10a035903403499088510707680c4004000e165809034034440d046000d400741c040c504841ca0080030041021640744240c80e503050400060941c1020743d482010401c52603503143c4012804240a0292502030718016650075094022801801502e1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 627202023 1250 627200773 627200789
    0x60127091a1c02011b0b0f0711060420010503040b0a0203060607050a0807121107050f010c020306010807061e05090d080f0703180512060609180607020705030106090606020a060c0504 80
    0x20302a282c1e040c00318800540390b00c00d80b01c190300c0000c81e2200300c582c00034450009156543d4034021500000c0c00740c4c8240c1d4040c520780b4100070390303240755807829040c2907080d6000c030303089810402881c00d403481100f038060384544203182250a600d0162036400180c00c0140403401c030b145d40000400c4250300c0b00801c84200720b40000456030219220f241440d0035510500301034454002c4141c2d05041648103c00d000e0b8500d208000502c200d90500c2d040054644a102c40c25040c0584501c110005803814031400b0b00074400c01e00a4130000d843c08901600d98441074401310340200e01407d15448140c0c21a05880300480c0c1a41c550000313070003601d000340d079078401c0e040003d126031004100c910406038072140c030202032031900e01080301e83da41e101c041c009500501181003d0035002540003030a2070500d040c0f0980d0104809069026601500d5019401e00d0410b498200053b048080240058102401403c00900206000b044201e10300b1034029220031400c10002c242a46074010030303010900c10780130b480240001c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 627203273 1250 627202023 627202039
    0xa0207080d050406030c0c020112050a021606090c090c350a0c2007121e03080411091308090406030507091d0c0f01200303010905060127091a 62
    0x3410001d0095000f501c00c40000034104143e0411852003100080142c1e64181c4800c6001780300946080041d210040840d0792282c0d081c0142d01520180c541c4c0054100d0091a002505600c2d50528500716503944d00002102e605102034820034940c403a40400e0302410310b022061440c030940b00500f500c51203c82038040d1816141007808122070700381c1c0c40390a85607041e07140c254490440040405110400c80410030194101820400c181802d0103007a0400b1845000213240d082c4002900800844200d40241c0c0015811001c01c8108020b0240b01c03501042c040310f41620500e44112030301c080c0c01609000400d080008a41542141c0300d0b50851009981c3c0201a10440d684071400340000303040a400200761074803001081d21883c50301041108900d407010700b14100100b030800064505002c1c28401007100b02228150341d42e00c04050000d180a4004414080340e5400e022000504812400303003202d000d50011840207090000000c04003046889040740404d40351240c01092a4031207041070070540180078 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 627204523 1250 627203273 627203293
    0xc030a06061d060310110f040303020a150b0306011a130e070f08010f06030e0f010e03040609080303090604031115150405010e0f040318031211010606050715020a020708 74
    0xa54001000391164442004951002c24000c00421030095a0680d0035810150030211803545907001241c00107004900d062504030401040d44565110341e000b64010780181d01e1610800172038070310fa00701c0d076051a403051108001d000006a01d0340410b12600082c13210200308000d240780e181080e1080480104006541d91350395071304901c5001d608803210000224016030000c48140116503980c180c07140d21510101c0e85040003420b9009001072208142c0920500031401892030090007412003003241840030710b486516143d4040d281c64080c1d0040e001640040c000c204119000044241d4000e40514085030791045c1094000d060001b080158000004400b0810500c0810000305440f00712050b1402c1001c0d03a603e4601201140043d240c0b078030f14400b04030124011903c0307a041c01010b240e00c0c0c4200e81742c45680380d0300c3c5a02800000f05040c082174808089241c1d500082c400c5000402c0b690610516004866403039450042c1c0b01300303401d1500c1d83e011801144083c403c2222901601c4080111003050305 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 627205773 1250 627204523 627204533
    0x1606050315010e1804141207150506120307060f11091c03110d08010e0606090102150a060e011410050f0a050f09040501080f0105010603111209100f0204090509060408040b0a020c030a 80
    0x100711031294000d445180e00d9a01a80947d004848186070400e400030091085000e941002e44406480c5540c800c0c8c25100941d1500003d1000b480c1039403081b240042c10868015030a000d0300c2c4440d2407805c60010502140e203643d04c07809118a05001034180c6414001403d01d0151a01e00340743c06251020311a03022513030020391300039403a41d050314000c85030700e00c10f648c9910400c40c15109104182e40140c0161603000c2c2020391700b00c0c1698100090b0600861aa80c0710540d024601d8003d910440c48044908505c04003414142886490300b038591404501e0820700a002a059104801185080010004030443c3c42c0003014103948507160010001e001c90350b59054a04d039500040e1241c0020f551030840002800d40c00f0744210210b003003011320070030700345050b100141c1054400108080d5860040400220101400e0b12401c520f8503107000005888a04210301d0104a5100030030804d1158007800a00002c6454002079030700719402002010f60344e1416110880c02d2086050b1500c1d018030503030a41c2030400c9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 627207023 1250 627205773 627205793
    0x102071509030b010902040807060f11060f0f0901060608150a12081b0a052e14162d050d020f18012606010e121606050315010e1804 58
    0x43e01403d441d10040e42c0780e81e85d0900320301c658450680e02c1da00441c42044484e00400354040c260611381000c080105400c0411814600d040790303044503c078004030404c03440022181c8010707004407000008000c400d05101c009800c0c02000360081010081d40c1307151090303941e6895590000b825041c3d901100883d494682802d0a42102d460380c0c2c024501041f00500b901c000003210300205410200030f0a13400310b00a030008140f10002d90303400012003d910717100c1c007c0c152030180091019203030451031001d1900c00070b0000c0c5107410b402c882003007000398610441c1d01d0039601381e2400c3d1443c02c641062200040850103444600c9100300c1030782e0796400807d401c100043c3c0d40002c1c0001111011000b0081044071004440030f105400940c4803010814004d0094a07100d0055030358401018140140d400c0945000901215452450101d0700d60041951488207940c800510004100c90f041c0b440c114184550f460382ca001180e4513990400c0b0744117208030013aa88101c2e2840758208a2071201c0090b040c2800d201e0109 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 627208273 1250 627207023 627207029
    0xe060702030307060629070602090109090207051e0f060c03070315090b01030c08070c1b1a1306090b0f031905070c0b060f0a140d060c0216080c130203060102071509 72
    0xa02d20000c17a582c03001d03051104080703404006d5850910b84180c660b03030b6070020740100403594100310891401180b0151644000d00100d030140c0000c004c40009040401140c207034042d210b502035041030920940b03030240090180e401c400324400580d2030765242c100460007030006150540b40210a558002030701c01c5a41d1040b2440308007030742e0a02c25a10140c20a60f84800c060320200b000508103407075040441c810001d012000101d44800285243d80d684401101a130700f095000802c450010340001c100b00401b88100040415083c011110341c0307800b5503281d05000350f00d0a05465040040021880b6111000e00d0850880701c03c010042400d00d0000240040502002182d0f559508d0000c02d03202c0c5001c0c0c0842c042d50317800038009980c1314100b0f582c1c20300c0d0785c81c42410241c00c082c6d030003c80d20008000303000d400201030480d401031942c0c1c0f01d4001551340d070044640c410945034124600807007050701c0e41c45003041c1031114404003681e03e465110040340f420b440c0d58001600007039240c3d580c24480d030b8402818002c1f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 627209523 1250 627208273 627208289
    0x209040921080408031305152d0103080f07060923011a0906010c0302010608010501171603020d020402090f0d080d11180d0302030f0c060f010608160e0607020303070606 74
    0x1400c40d01c0030b0b070b101d14040d60040c0c10010f05000107510a03140400c580819440b920948202120034000588842001d03180341c401c002c003c01c40c90a080ca040015420300c6c040005d51a9070b95495900d54084501c200c0652000380d5400103a2841800142d82241c11a2540203c108071003070042c50352881044250516100300d9402e015102480b0900440c43c070a00c488001c3c060b6840303840b01001540c980d81c034248210159521100009908402032203070038002d154615803000403c0786480d1182c2044a03000f182d090b02c24007600d0138400740c0c841c200e414030841d605840040e5241c84060000d2080c1a008405a0b4080c1d0411145001c000006c4050312103a0362840d02885000380c600c0c9106904d0180030390003034415400c2c0f000181d0614018000307000250182c01600e00d000d075a00c0e0120070b164010040c0c04016070081c1e090014000001c000240180558a0010800d090845c5012506207000360403004110b041d0240c00865529042200e19a07540142201c1d680c0555141510180c0450310038802 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 627210773 1250 627209523 627209573
    0x4020d05062a09090c0a09090e0a03030c0f090909080c1c110f0a06110f040306021309060b0d11042d06210f02070212010e06010f080d0c020402090409 66
    0xb0032003040152011007100601418140d0365902600489403c0f000c402e004000c442d0400141d80032041c031400e1741e03040301240900310b02c80702e030b08018058803c040e20100070071114407031811440e64805c22000035500c10682c08075076650300781400540c40c0640b03030b409040c038020850b02d4480c901e00490034003078080560702c0b03040ca0201c089810580340c2545041010081e004141c040b400540550b202d10810720154200a0800100f0100800650043c2d04212003a1380e00040310a4000003e4038800003e14000c034040c0000741c1020040c14403801741c0b60003240c0641d1501081e20719910b40c9402d45002d007141400e04100c0c200c40a08210414000c0c68811031048000c00d004a031040c0302e070300301420036426a071010400c1a600742951000380a0a00440c100d0345c0d00b40724480041c0d54000c0038202000c2070340004160303e000c1001280c10441d040e441030305a88a001c5042141900100780c1c21422050303030a120100d005140040340180c441c0000b07040c1c0c0285010b031070358100030126072006107008114800d01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 627212023 1250 627210773 627210841
    0x60c05070f0e0f24150c0f03030702070806060609040b360606031b07050a0c030f061b1e03020409111308010203072010060603020405011d0a0e04020d0506 68
    0x10030078a515510f1000801314041d0410882d0030844400e034450381c1140d1020313240c1402080b659080c4001c01c00301c0d551582002080c800d0032030741008018003409149018000b103007800d01c0080e6031131080c10503260003540c0701c0e00d10f81042c0e5168a1704000404148a030b11944003c0755039101c8200d601c020304003414014003030101303515050400c20399126042080c0808103140d2808070840031600907102c101d90502c10b100c0e1010011b03191101c3d4800a44c1f107050071040d030071070034034119061f2003103190b10f100c07200070310800221a82c1d80070b00c1ca1000b120000b100f010420003800f108401a1140750051b411070350030070415101d0003065200501e00c030b443d0300d151040b1040d12040d95601342d20083e1501c0000840d003c0341c003585c1d41c1c80c00c60044240703213044049445004060142c0003e582190340b024020aa02140400c02560003190700b034090302011854911038038420307002510412403130007900c400c00c1d071301c9000801b151a42200d0340b82654108086580c0b514040c007894400d1040840c4a02401841c0d100380 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 627213273 1250 627212023 627212041
    0x12f0301050a06111915050a090f02012003041805010e040807151b08071b1722080a12050f09011101021b15060d0c060c05070f0e0f 58
    0x14038181d80d0700401c4034614500d0a0307400c58a00d8600c419490150050094400182d140000140401c61041c41803a0b0303d6140e40ca180e02c1214001020840e1040c01e002c05040081d207606003405402e642403e1507180d9405080031011002d810f558020680d1100041c0451380c081b06140f0348000300820079051020380e80f0703080501c0283d2001e40340100520001e20902001030142007aa00741c80c0c44c09040020354070b80e03120107021781100b04003584010500c99030078440105c0e440850034000300c3c244c1c8007028081e002c0340ea880800410940078001d0542c5c010880305d60b00c500c070f07845044011020b805441005a11103554a0300c4502c181c030103c5540d840c5010b2842c4890042c819203160707031010b403406800d0840450042d42c00d20202465482203540c00c0100034034150b47c842c00b1881207007505000340103110081c0408000c01c0300151249200314640044040000c100c0008141a562686030210f041c1c002032428500d0a1001d0f0040d003200044468003142c030546402070240b02d41071071604508180c83e0640c40c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 627214523 1250 627213273 627213277
    0xc060f0801030807110406090203181f02070609020d08031503070f06270b09270103030c21030b130b06030601032406020703120201050702061512012f 66
    0x2088089589a001007011400700005484443d0160b14454082c82c403800010701203d0240c2c010307200b441c1e03021003400b480c28454298a00b071852400010050b2800380720501c01080000b60300007011940008050003003020030741101c2c1507194060000c81d84c02c1002d240045403031700221502054002d548010041c00c1c60000303030203c01c130380f100500d0010181c20101c00715080d003c0050303541c0d07081030038515109043d01c0d0000d5020050104a002c00d0302c03020a841001800e24200394135030f50100d00030f030b4003200c864404908641108d5050030620f000340d5151911003140c04080340c0e9981c81207205900c0300c4c4200c0d0990003104155104444808054200826110895000a202c02e8000006100240142d40aa4005603030071401d00104000c0441c96201307210080c030640c100c04016008000d00300100050300c80358000702a404d000a0281c2e10740890029914040144241440401c00c0c110944c0d40d21550a41c7c2e020340d901e07000a0108404005082d880c04005180800c1c0a0360403444400400301d552003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 627215773 1250 627214523 627214547
    0x40b16020c100f03140a020a020c0f060301090e15090c040506061608030601030f021b06010501230a05120a05060a0501030903090b0703051603091e3c120c06 69
    0x984502c164903808200c0e0780f80002c4040d00d040c9a600c5603d542c2242d10380c400b0070b104d060365040159035179150420007410401c100c0b803224020003224004014503501c1e5420f82c0e040d04c000034000284d88010740007562514460f9209125284d0341d000520929040200d054030b05201d0a44050140c1e882e0b5030240407040c451034061f5031400415003e100c1c0051541d200450301300300b0501d400701e801016048240300301d0b40480d054400842c00d50030010b01d81c001c01e00c61031380101400d0800d83c2141d150601d07000003110500c03403911482400007444c092404e00640c1079400c0c0c019000304180040c508009150010002130742c04910400c0b51000000340744d8407a0045404140e031658904618514003184280190001c54080b0107028080c8641c0300020f26880201070198065501c5001c035500c2c002c0300c00b0440f04a1034044080d41c1d01c881060100c8074030710001c410003540800c02220508880582603800902c000c03e01400300b68031210004010f69107002507180d86000d4000001c2c4680c3e42c0c0c00549000300c600c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 627217023 1250 627215773 627215779
    0xb0d05011d06030307110111030408070f09060b0a12090b0f0907150507020108100512031201090204060c11010903060606030e010b0609090c0a0c241401300605040b16020c 75
    0xc1030310300240c0b501007008030540043c10420301d840780402384076040d60040d4100942c1907126070401c0004403800c0070808002c00349100f0400c51581080d0740c2c42c500e4440c41003910103205010001d448001c406502050445800548004540c180544108902d80e010364805010b407080420201301c0c643d584011340f00b03081c02c684823180342490326401503e9504006001245001c42113400081e641c8800e00244c260384510340107541d0362034003032f081d4141810068000040c124030600c024055980c01050f81c1d42c901d6001071031200980a03680040320100440c2d080100b4a90030280001031060b0076802c25801103000400a0000031141030030f10032540103c0714070950006001c1e02149103907a41100030b0491b0107040c9403e42000f174694862000034030b03d401c901c020a00010001d00342d004001d10a640107034a6002d0408282d51502c0250070200c1070b0315006d00ca414610554012000003501205040d25910080c103010f60300d01820f11542c0010200c604800e211188d60300d10f080340d0f00c041101c29640c0c07001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 627218273 1250 627217023 627217027
    0xe010810180e100906050702120702031b0303090301110c01140f04080901050c0115030c06020d02120c0a021c02040e030703020304060804020f041401090c02030a020606060a05040b0d05011d060303 86
    0x31000c002600308000510401e000b9200c503e00394032000e002d10095540203a0000c11603081c0210000d03c2d1059107100c1c038407002c20602a250050ba8045140b00040c44180030a80210780d030703e0002030031032148601c240c5d410b40c60204c3c1c014054038110040c05c0895045402045007060000e880c610340b0200b151405c00c86071200d000200020709a001a0800071018509203003042030200b4418210780000454a4000c1905802041001880c03101e19010f40316030710103007079a0141a140a036844410300c82003244440c001c02c02900a0900b005015032441d00288000032040040016100e01002054241c0c0100d0400c1c8014000790000012502c0b0f041d8180d0080d4542864402c04035503c07038002d0012640192504101303021903403035000d555036014108079003040d55494042d449040300e180007061001c0d0340080c0056980c164003c00d0b6aa402881652020b653310300841c0200c2d014030458001208049011a6002084540c0d42c00a41030b10b941940002d01d0344680c003d80c81d00d0342c1c81211800d40c59401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 627219523 1250 627218273 627218309
    0xf080703091112031204050a11010e031902030c04140108060106030c081605120a0f05150307030803061206010b0a02070506091c02120712020f0d030206010608040c150e010810 77
    0x240008002406003c207072801c11800c0b100100900304140c40581d0b1a03441811540305000c1c00002c405000b06090900b0105036141e8004a610f9140450760070404250980c0d41c0402d544041c0108070b541070009004010302074800d81f426415080a0080800da41318800002c01d2040c06403040d1420f40c1c01b10b4852071030968840282c40004c40a503904141040700c1800742300b022504064080b401500302010100300242658840c00480e070f4000c00d02034180901900000303150702c01090030420380c0d800080483c1d59907240004141031802c03400209215110f60000050700e4080308001e009007404c1c2d5401d4404895403481006094001c2903a00790380a00e03000038900a100b044100c581031035102415010003120704880700c0d810714056501c11000c40d000b000c4200c0c11440c001c9001075501e4000c540c00c0f107102159071030003903491405006c4d0100344000c500200d000e00071808000d400505071072020000d1070041801c010704c482c2e01141501d010480c20408140034140740031140d4241c40c40d5600305460184 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 627220773 1250 627219523 627219529
    0xa030213080a02090c0d060b1303030e0a0e180a050d03090b100828021807120e0a020105090a15021c0203160206090414040f050c03030307120c090b03070f0807030911 73
    0x3120a4011410b0380da107c50006503510200d0140100c62414071880304e44618505000e0714584100100500c250801541400840402d0a003660010542950205030785842000305d89402c041c443c02821610888682089256140d081068214030800c015039698507400c00307044015040d0b0145850940180e1002125000744401d000804c901b2400c11b1038500345240c0104140c80c1c08140030001800c06a4100240c0a400680c0c2c80311500c1440001c000e010141d4204580318003031020000d04011000413502219500c90061a001d0620155001d030b500c40d48040217542e89011010250038950440705d54a401400801603940b000e44800d801841c101450b070800400b5484100810b03485079450345040101089051214441c0d442012001c41c2c0c60020304010b07141401e40c0d40030714829031007042000107441d40326120394001c1c140300c0c0000c02c010404d0320081e00d50485541105011601c04010004410340c040300c1e807014028252203010039038461104c01c4082c6d680007080508075400d012401d2145013 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 627222023 1250 627220773 627220777
    0x10e0a0b0714041d0a05070c020a1a1201140907051614010e010f0b040b0409020a0603050a0906020a1805040612080f04050306160206060405010323120a030213080a02090c 75
    0xb90844480e441d080d03c488407a4000a400c003602c0e0210110303a02008182c00c3d040c402c554005020341003410946161b6030015941403580d015131038001d91109070801201408005650075100080e81804003981c5a61340d14803000f2503903181501c20404403002c0f80c5107900500490f900209020120340715007415440e0942c44408942c03040c0255980e81440c1c919185c02031145c01e4242001190106603003982c9002c0000b55054400c1c4507100b580307030004040040e682c0c9408a81220f27004c2c00d010817560303249500407000341b80c0c039400030b001d031070001901c81946a408500140361204802c5821050760b22641484101c40c5240265006202c4408961010410389405810251030f000909860242c6810110781080ca0642d44810301401005204482c1d5130180451580840c0a43d010031103036255444450702e0502503910610a02d0100d0a510681ca006000c500c041d55841c0102c503903a80e804140040003540700d509294094804540d0104100340f0100340005400d4001300740301c0c1070f500e440d216890a6 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 627223273 1250 627222023 627222047
    0x609020304230c0a14090f091e03090303070804180b03070902070807060e060702071505030403030902060c0604110a0503010e1b0a03050a060c0314090d03020a0509090f0108010e0a0b07 81
    0x42c41002034070b800f00c4c1c0e5002c0b211000f4100707000708000700c1001c140034020440800307400b00340c2816046007000f49014000035580140e000c00c0740070001e02c500b0840d4107403c61080340341144d054000095444140300415000340304855100710303000300b02d101040800e81290b04800c111507143d00320342c1d4100090710f0310303070050036001d40101c04080c075140c1141d540c0000c50345c040c480c01081d90452010002c80350340600030310008080c6010500344074201e0381030080c0144801400202815a00c1c141e240540d201d0320151100e550060044170100d0a1505200c8005240e03210010312401e654a070100301420f041c000c551580012600410180c6401088200a00b0000c840035030800650900040840e10411002140a019100c00598a036610b400103060318041c0408503007400c00e14040c001c202c10300041e80c0c6510bd83ca0720300140c8600d00a58101d505200d003882c0140d00540c011306114140d00141d00070790403100800c008001c0900c4804015450b03500d07007040500040140400249841e001e008d60b02d800c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 627224523 1250 627223273 627223343
    0x20a050d1416061b09030c06050d020403051e0f0703020906060c0f032709010303120911040f0e07060e0607080309120a020c01020c010e030718020415050c010609020304 74
    0x818188002d0202648074004050301d81c1130302c961225100b00386083c03a1290084a40c6020581c0c1d42c11602d03000684400c6210b0a410400001800c0344601d180c0d6051341e002c0c41d0310409907400301d07269074150a0320000b0034003441003d0140b50740b407094203a4001904011030368050b14420a41e500c06c1c04109060b08000b08030340450089880204141c1d8081c001012821024100040c2c120554100c01c040c644062050030b0081d4401001400030981003070201d00320791009000400c00150a00d08420f401040c0b081a40d005402e015107100c092006810a43c04c1c0e1070204201d410b22941c8072800c4505448070146150020410007041e804142c0341d000841c0c3c4148220300f2260300031000f040b0030f00c1c5a4009454440141c109280d100030660307040c0010307802e2070b100746001d4245c1c4480a0000740c6400c418803d1142c503a103100990215115250140c40080c6080303040c00804500860700942154821000c1c02e20951a003503021807848081d1017130324082d43c0c202d00072010300710b88210170489007070760303c80f100139 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 627225773 1250 627224523 627224527
    0x2011205010f0b070c05060307080403091e03020f040608070f0501030e03180d1b0609140d0203060a0e0a15060e0901020301030f0803060627040609140f06010c0b150907020a050d14 79
    0x3150f45a00c401540270384015690880b4920302401c006120a6054000d841200c4059054142c00a500940d5809584e01200c24075204046a40082c004000a40c410440c60082207400101c400740c1c0b8100a00315202a00d0500c110b103031494907561603201e80642d48600741da541603119214144000340924403840b500d62418a03204803400c61080c0e141302e61200000038928901403040c5140b88180c0c2202500a8450040e1010154006515860002d012080b4280d6990714412808010441d50700400d4000109101000310700e5544800760006000d40041958140f0200d00c5421f014030840f4103c0340c010000e0f040500f02c0e0350328020741c0d50024280641c8207400380958039030450144024010b500d00b4081c60750003008000284010703202c1d80d80c4594120b0b45004004030100e003160380c541e03500401789141c00b0440d640c0d21005035180c00e070070140a410182603008104010206044002d110f680858a1200d580c0c2c95900c00c90303860040040c01003290704515500e0a26500518045911011510f0158 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 627227023 1250 627225773 627225779
    0x10806031926030601030f02091305130605040807051c050703120e100c0f020102090a09150e09010203010e0f01060c1502360103020f0307211802011205010f0b070c 72
    0x44201464500b41450380940041401443e40c0c062240c00f411980300c3c641941881003c00004800001c484d146490117a110400a031220244021080c12982d100400304150f08260800c50310542040000b00da203889070191140c3c481800e0780380200340e0101c60782c0b114640f0b42c91340c0d82291180201196804d50030b0f190100310104000500c800e15036801c144000049191024000401e0803847d03000320020341e4410007074162107403180c51000059502a88021403c41d0483e18848a0100141e2043e40f1b4072400a0a1149624040d00210304031880c41d07994100d962500811006118800e200d0403001c10341d005400c10000d410f905d00d000148000410050070502500710400314a00011166129102000040b0304400b004c5c08282c2203030329003840c2c11801d000c4c901503644458840070b1b041c4003c0c810450070800b00c248010724003c0ca02070904506114100c101c41d404041c41d0400e5000300c0c041040d00b10600324440f40d134070410f8100c940000d1280002c038038114504583d507001450a80e2041304454003c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 627228273 1250 627227023 627227063
    0x60e0105190f020d1805010e06121e010503030f0319140702070314190f050c04020d020c01050f040c050f0607141c050a0e0618040c031a0108060319 65
    0xc2005001525082c090070304562000f814105091400824420900829000070001600301410b50340e0038200078454410303800004a181c081e0041001840030f12004010080318004006800310100d42c42007050741c0d0f00e0313808040d100c0c000c1c004103240c200000c0c00081c00702d10055030355541c0c00242600c0000c6503400f5503030044015030304590310780160f401250304004104407074010140c110500405004409210f003d09146c60000010203080907207081800741c2440340a12552a088000410440d600d004591091000e900040b803511603070352810300000c00d083d4a00342c00c60f2103298003420351542c1078140410001c14405400000f03410580c24407038040001c008180402e1401262070082200b0007021211340e9103044080076080c1000000e1203170700c1803150012a10b403c3c1c40012a0a1529242c5500300700005e6483c840002ea4410308001e0f07086801500340d484494421880345180740403210340701c010b44011600340d4070030750164050240315050401d8803142901030744c820401d80d00e01c5001c114030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 627229523 1250 627228273 627228307
    0xc1b0309060a0c0f12180602160e1806070207050f06070c380409050105190e181c020c012c0414040b060102150f070c03090513060e060901030c060e0105 67
    0x106541d103401000c401142c04484000340b8240c8001d000800890500240c04110751144c050501d0ae80004980000398628003001c103000c0d120100c6100d4644018002e40d201d580d1310410b8083c1c01392030480d403044d0074450111200c064118446840c0249450700c50700c1c60620f03445024000300a0b401c00c5032000c2c510311100b0002080c0c10324299480e9828411500210388060340320610074000071000749803001d020300701030003201c803480c00a610664414200035900c14145146000c80c1c05940070190841d861b0040c00d002c40b410550031598004101c0c801503400d03041c00000707044070034940c580c02d6031015040103241c6810302c0050008180620903262000c600c48050700c00715114119402001b07400e5034100182000c608406216400398140715025030010400504480100000c4182660615000d0181180100009400100e1030340c0c1e04040300d00140024028280a52240c00c04211241b820b146454166a04104403030f000500e0000151107485a42c1c1e5a9810301009116205001c008507031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 627230773 1250 627229523 627229553
    0x70f120903080603010e0601030b15040b0a0305011a0f0f090c070b100e07050712030506031218041104140105280f1106070e0d03090e0c1b0309060a0c0f 67
    0x20b440106003400410142515110162100540d00c0000100b001c545078080007500060740d482c2012200d03000402050242c81c2c1e030385005420038100d01000003040815844910b40c46c9040c02d007a424540c02034104003409040595003a4420034030002d4104901d0321010321a0400c0c0c502558601d01803042d030390003040c2c4104550340340a6001c004000c102c030b80c41d002d0740d00341c0c0311055241040c50014150b5603100d903c1c0041160008040e40c0306c0000b04c55031001c001030064080044405a180c03444203403c920b001390f00d644c8803070041f81403000c0280d0440300c11003914103032a01203050301c80003d0034200443e015046000d104411150b0300019941800d40d104420f822150780740d540301c2d8032240c0c03a8030143c8031803110b044074511584002c0401c461203900640b0711840c1402120019448200d60034100c40400c01500140380d007041c03103001e00c050b544d0030780d00400c1032040044140414240304415591a400b0f102c800d030b5000740c82040400314403803142a0400c02030344509862440c50069855175000d0a40b544 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 627232023 1250 627230773 627230777
    0x20a090e0c0a0803121b040b0c0a02041515080c030406020c100c030501050f1c080a050c16060e0a080304090504060908120f0a1e0507030921030609060b03070f120903 73
    0x440c0c007240700504031500e03400350121080c514509406d4001c2d2109206904c9412140c10020603500c00c0c1120030700c50404681d0300180140541d40e01a450710110210368428072030094281c0c0003142120b805101c1e241d1190f044843d60500b556038540b50800698041160109103018074030b101c0b1031000151041d0101c17601f4999000846605000c140b08030b0103c184001442000b68a030011840071030703c2c000030950b40d406491f007a00e03184510015112030240c070941c1100d60040758a9042101800020310080300c44907503501c2041c802c94018421002d480b4040d82c81c040d0801c000c2070145250540111350002e02c140c40010300702c14552070f00a106d40003901c4c2c440c10400c0c0b4006106850100300105034100310301d0042004000041c640300b650528804900c1e0382140d07180d50005200c079000341e0001c0b40703e9070411110301044400000c5520000302010034440820b1600f240400c0100d000e125040c152a04a0701c55855074441210507074041e5507003042181040036103603407030760f0355021809001a0b4521036 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 627233273 1250 627232023 627232027
    0xf120c08130f05060c0a0201110c0d06140c0906071115030f06040b040e0a0f02190b0c100504110f040608031b151512030c0a0b060405060904020a090e0c0a0803 70
    0x1100222403052480c0d030065128407001e0001482417240410050071466090814080010000c2202c600f003600c4101030607486050380300c0000038081240c11420030241c0065150007282d45001113a0f80701d001c1c190401c0d8225900380580b00015400441552582c040103218107291002c19181105130350040f03a07018500e500500034020316003841e0181c0b66100804890074401b1101c0e5200440d56201745150180070182803244920a40d10381201071401c1c40f17000212500e2458885140a444e6030004c4450707081c038440c08500d214034810314451507001d554014080d4500749105000c11107070341c1800250540c01696607000141c0c0e54800c06c01000d4900b400d81c40103c10070106c3c0314603030802c1c541d20640034401200104020043e1501d040700003a00d4022a0320a00305a00d66030140d185024502544845106044a16051118a040181c07144a08550502040d919030007400403046041d20002e420420505040c4640c05441e08003589600b690740c22601034100510003d000500c80c0c0d80a5840da03000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 627234523 1250 627233273 627233279
    0xc040501110607080c0d0e0111092407060504080d3b0d0809071d06040e0102090907081504060b1b0706090911040b22050d0f120c0813 59
    0x3550206480c074003201900c103070325040c200542902030080c41c18184103c005041c11070060140d01840d48804581c00801c244075820381124a01d41c8410510b034810000107070300c1c2e507418010301c0514104641c078000c12801e02e01d259481101610028004483c080418002960704002c49d02c00c00140b40b401390074010107030300c0b110241401c681c01100147d20030383c4000708411107210005004926a072041c81d28040d10f42c1c03654100303814220150000d0002c00f201501400c1709950455125004120445040113050b508004844c205d02c20711007c82d4110b1004400184098060741406a00448140a40a80c94a0320000401b1100b4541140d03204520200302a040307004000e041c0442c090714007005008640c20700350040c12001445c4600c8403019111107034901d01108000c282d50080500f9100c40391038000a2090368400185255011a181401d40e000100c03450000e03409151281c1042e402e01b801d000686800c590490780311a0481803203080e13101000042c5c0b62030000c00d4602d44a408141c3c070141 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 627235773 1250 627234523 627234527
    0x6030a0605040b1c0f0c0b07080306190e0703151502030301090b04050906150409080d0c030c0513030b0c07050a0f0b06010e0a060c0c090501170715090315020903060c040501 76
    0x40940318070f025104200500c0f50700c0580c6002100d00b60703006280a000c2d404186441b0460420b03c2d0401010081c02040040800410602030360103060100c40502ca006441e1007220590f4880d41318011a8210040104041c180203078403e400900b100c00300d181403070b500d40014180044000822000581c4000010040d4101a02c125414003404440c1440b41d41010805640c0d5070b10040c0c10008890329140d065662503503981e01008070b5503800340c84252242100d0400781300520700c45545502190900e902c0c04040d9215070115000ba00f01001103030003242c1551245409554010082246458100140ca02185e000c02110701e00f58403030162012001740500e85a0a04030005d088503060000300c02c01070800343d54400b100400e030b41003442c0015140e005170802d1f0b1601103440d4032102a60349003100200300104d10204900c0c0450200003190402c2d550b403019801c516110b01a503100140484a00f031001841150350a05212aa0380f800350a1080c504002400c010060f10500801c0200207002c03c0030396 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 627237023 1250 627235773 627235781
    0x604350313050a05060909090c19080c04060b0d0905010213090c27181508070815060a051203121302040506090405120a020708070803070308010807030507091a06030a060504 76
    0xc2e0a8901400152030100840c101c0c1c06182c0e0818461030380480003400070b06080254044030f4100901c03d085500d01c0c62903448100c6003d02481805000b807a802c0300c4942414011b2400b01c508180065251024403480b040003445e022400b120b040d50208040260b207450f10445d00050310001c80c0005100c8105103018000e540ca4018207880b18a035215000c0c500c0103070407040d02c1150310111041826024000c2007800400c0e400031000c14060035154003149081c000540030b425030748140c044909900c5441046c0440c000b04644040e81b001481e40c0c24840341c101242101c1d25035111000f140c0c2441100b8103103100c2000c0488001d094441044c03089010f51410b07001d0070b0380010082d40d40b902c00e400c00fa00c41580f5080140244020810b00080c25040175108005003402000500241c41c1d4658580c5041c075140c1d40115000d81c0000c102030004a02480c0108407442140d50080c0101001817402c20224054503102c0800081c000c2c059054a07015124070300158418012840c0c0010118100790410081b2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 627238273 1250 627237023 627237029
    0x3060a0f06020304050d020a031406011701021206060d140c0c07050607020603130c090903020606100e01360308070203120901210e03120103060c0e0604350313 70
    0xe0314000c04200401c07074021040f0790990f4005d5603444003901c02d900104441d08841e41c0010404025045000301c41c10011500314141da00c103070484030f14400110b416500340d008a54000024202001c0070542501d07010b4020806403903581c03c01314084c04000c42d0310000c28011540324001e008002920441900280407101c050b2501712101414110183c010495900008205400e449a540700c00804e00601850440052240660030f04c450325031441d000f52500c5d0306541c50760003190803c03c002012401400700405121042c3e40d12103031080c0040c21101c2d0800c070442c10f00b8036200800c00d03400807500d01042c1800178500548400c0d640d41281e206042c900840d0b400e04608084051100d204d1a03a4412025180c80b030700c0c1000341c04024001038201d0018040400e072004140320004d050002ca2030301c1301c0410b0490780101400c1250402102c0140d0b00104d15155142c0d000c2000c1105012103043c20840c0c0110460740070a00041070000d031046942c04051001d1302105600100f420450619242000c80203 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 627239523 1250 627238273 627238289
    0x71a1305061311010c030309080315040605041a0603220b07020f0610270f0b031c1713020a0602030408100b030c0402220b040e0601021c1b0203030304050303060a 71
    0x11407201511184090000343d40240e0400c00c41d1084501414481d4200442860f0171406d115503d0a010b2142c2480100302040940258109500080c00b0b00c4c040c422696410000d801d854582025282040141c3e0303c02440c007612081c0945040035401c14415401031500d2240d140344085040c64400030303203880c0603090454916030010b42008048540360b00c1c1c4004540c86005400000c0c030300f45594080600c821110030070710625114420070521002e4104a60700c07070050b81a80e82d001345079014007a0140510b4003203404a2418031901c800c1e103590074107107588070716850300101c101d03404c070f03400140291074550184d80160320200e014807c0b0349040c8107802420715802d80801c88490a0400310b5100c0c959035100074801d41e03002c42c1071280c0c6000b4940404880c1c2d505100628440d803516440d2225030800d02a29001a90250004500f540001042003140a00b10100f403412150203104507416102c241d59030240c080481251001628200040c40c025071041014546a00c2c0c09418001c948860354410b0342c0c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 627240773 1250 627239523 627239551
    0x80714040b030a2a0314010c0e010f02060f04020d0605070806101110020c011e0603030f03181b120c14150d020a0c0c03061a040b100302071a130506 65
    0x4009000118034100001040c0403840d0601c4c0e0458500c41c0e0030403254005441ba100c2890880c0103010107502c904400a425210000050841744c01124212001804a001350b4003a5011465080368840c1e8541c0c028401409895804401c0d40d40342d0a0700c02c203540e184c0102c5c190700c05001c1c503864901c4103462000210700d03200450084a1614075650110040c1ca10009070307001501d1034030000203400c8562410080142c01000800c40a4450010061031105800003118030b040c05901c14401d001d8003240380c200410f08600315070192101c07000ca68800083c003114020181d400204540d00a0000143d58081c2901c98515481c000100c0104224480c1c0d0510a4012030400b0222001c5d01c1d042d150308589a620040c0c0741c104044098501d0404828041d1100c0843c4000004000f110b401101c2203003d07548184080c541d400041c8829a044603400b543e2000038200d200b03500c1c40c0710740d015290903409241c00300c18003031214040080110041c3c80340c01cce40c2d00f40d2021000a1101c1080029002005000701c04 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 627242023 1250 627240773 627240793
    0x1b04030602030612010b0a0b07020301060305071d01140609060c0a021905031c020d08040f051c030f0603030e0f060913320a050711070f06021204120f0c080714040b03 73
    0x1882c1e1f02041d001c0c502c500980403440f0425918250301100280d5840070481c0d44a43d1a00c2c800740b8110700c9070b1100904034040c280045400b01c6d03081c8031404003100252180b82810080010054940c10404281c0880d2150002880242c0d8901c1000f20710172160500300000c0c603050005050920f40074050501d0080800b440c0440713007690000310f9008085041c98441e45640300c0b850400c9846a000e03001820f40e00c00e40c81300e0030400c407541042000380001604d0420400d0f40c4055180d0a4410504c8040e02046100e12514201d003480008104404001803659203402d960400062480318102c104034002503503110002c040c04d042d415040100044030303541c41c105500620009240c004002e14207000980c0720380219014500030b151070700402d0106400d4880b140d44440c41c00c80020b40c01c0c40380e640117210352404040c4602c51041200d0980c0c0d80c4009442d4001016100c520301040d48a034210f910fa40c142c80000340d080b00a120745405080341c6011070700c104e4a264100402c0d900b507001c50034400c3d04501001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 627243273 1250 627242023 627242029
    0x10507050a06110d0c02010203060f090f0c0c0c090406021305032b05071406070816050d0b06090315010608281a04060807031202070317031b04030602030612010b 71
    0x300c40c109611810110749803d02e081e40307803424058107240d010005d05040400c2012030b010b4010310b201e81c1068800071919640d100400c803c4d00400c0d1100d41e08034a554012448a94150004000550390720003154001c000c81d001280d4001c2c01190305a6200e0782c04034614080f0f0f40021100c10042a00700c00500c00d86051002241c090003410348031407100e0800680042105020ba002c3d80e0110350171802c10465070002844598172000e045901100056640000032000702c00c0100081c94010a40ea0303031814103545a8800c0d00815080000315880141440350f2000c2d958100301c80f480c43c0342d51440074040380d4500500034000020141c481101400685040051100b06041003603080e196882c01040e0902c071060f9030390440074180106a0002d0400d80d020440740800a01e19085a118009030249145d40000890b15541103000c0101800c08000000300134140d041c01554000440000780083c050304007241921561055004481868000c810070995107400001c01c0c0303500005c14000c0c0402402d801c00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 627244523 1250 627243273 627243283
    0x1b232503050607081b090d080f0d05070807020c01180302030717010b091e040201030902090c040602060606030906010510051603030b030115081009061404031e0513150c0c0e011401050705 82
    0x603ca4800c0404501d1b91070581c0c6128002d003034950407080c490f0341d07014540050441e542c00130340300070310207810100800c000780d200b0540703548a0380030350f405818555040b2004560907000e40207648841d0000007804005030b501484000c1c000c02d480c040e403040c00d03d085078449007903c0c4c1030560144100c400e0020441c83c2800d2070b025480c0b60880703002504540d900ca20050300105480300d4040c0d00622400c080000040554008109071101c5808807003440d03494130100030f0603200884051106410100040105042c18014414112110308003e17081000042c484160740100340030a40000b91604010007040c1030a118011002d0501245007a2903414450455917658101990f03014040e03481000c0000c1c0b100903400003a018080c0c5100c0200c0b401d203070800030b04242503d05600c22035003e41588045040c0030b08103c0358a0300311022041c2c841d501c2c1c28001524465000d1492090009501002c000100d40c08031100150451041c3c9907841e505111004c000040b0041040c1d043c884100070307510125000140c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 627245773 1250 627244523 627244561
    0x2010503010603020c2b1211090922210f09140d020406090c14030108190609080307030e060901140a0507050c0708030403031b23250305060708 63
    0x1c0240c0e484040e50100341c90f00201c00f4071041c0d2106d042002800351000112075220445c0150340e401021001d45665204954069606c0840d907201002041c4581c01d103403003980d902c40c1c43d14032800e901e4004105800301d2040c007280110343c15204414401a5522004916406e006980c40c1c40e0202e1030b4900f00c040c021040700e0103160544040c100c200302240c2c0d40d0341120031032264050424490199118580c0340508040b00503031000c1842c2e1604500b14681000c02c2d24100d401c84002410b0185040049206800b4206800d4481d10348400e00da41c08900c2c010000d5005034025034000500b180b90003240b0341401d101800807001a4181314502a03000a2000c0b055084600d50340700050319221101e06031001e100d81500088103000307616002072440001f10160089074007030344444901039015610464041e41e0004002c12150300184400f155144c80a0f003582062198400c684030802a1100011240c20361100700721307598411081441000340a10480c2e070030101e00d0404015500740411544c01c2400200 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 627247023 1250 627245773 627245777
    0x1f052401080406150306060311030d12020a0504050603010b0306031507020a03032a050301061e0801090504150e0a05240c1c1109010e0118060c05150703020c06070c020105030106 78
    0x80442c0078888107a2001000300102c05007008a981e40e8a0903502402c0540304c241c0300e64a440d00c05008031308000c40e00c0e43c0c80f02c5455451407054801c1154603030094100040c0d0b207041080c240400f090703c3c0c842c14011070103440716820351131312450318604061038036103e40721041d00721000da800d020302e03250009015401076515040100e410f42010f0807040b500c41ca01c0f0990390102c5510095000036581210041d81030390b64954540c00700100800003448014210152480080c54440040112a116074441c4d9041403144248030b08a1305042e03444000e8030101a00080f541c0c000700c071014100130042014102c0d1a0122007030b059005549440c1591003403009090000c41400013911207903840b04000881c60070b002e40d1104200c180040c2000c04032641080c2021800b051041d9100304036903004072882510030040d0380000d100c850070001c0440e22034a44501c112900d00ca242c41446500c0030038001c0c00d1043e5440d035001a200c85081d5001c42c60140041c2800040c88801501c400150364818201c9054412034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 627248273 1250 627247023 627247037
    0x370e061c0912080402030f0304030506041e050f0102031006081510180806181c0f03060905090a020127060e011205090a02030f010209060d0903020307051f052401 71
    0x8160180030700702129008100045035142500d1060300100024000e0340280c00b04c81d10041c1b22510240e0740c0c45540000340c603c0e070044000800180140c160002401d00c103e01ca40011022659100d1612200320040d6a10340d40100c10800d0003c04c1c40a44c800400d4a468000d665007006640d004283d4032511380f0303901400e0101c4006030340314058450f0200b2500c0c110040603800d0350711003c01d074481c907058401c2c3c010096980c100c003010190015402c070055028031081c8082031030740d40d410b858039142070b0751620515859050001d000c001078802e00d8895030303035000135000d164800d1000411503900b0500c020714418001c040ba42031009150f80c40d00a4a00c4c0d0700303064800300400d40041c2d4841c10b03211100340c4581d082c82d040103100c20021400c120351034800e8040b1403c0424030300526080c1d004000c501030b0440700c148826811144242c02803003904d030090058a103008560346419062020038078000441080c1c030101c08444083d60301c0341c0d5030300c9403404d1940c6425114504002c46a42d000c0c452650400030a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 627249523 1250 627248273 627248317
    0x212240c0f0417010209090115120e030a03051f081501080106031208070c0f0f1106030115080a0e1c2303070810170109020a0f060503160302370e06 65
    0x2541240e246e07100080121405603515a1b14000880710092404000b41456054800b040340c0c03030094404402c1c0c0c21014500700105614200c004102c014000b06e8a590f00704109986800c00d07410041c003926906002c3c19a00e0301c02d80324111620010382c0f114107141e1401c036040021482d1103166a140b4185403030050129101d0003011501048a02c90150164450320380c0d00e010005c40304060001e040c49102c1d0070501800490400080c0d00091040a200c00c3c032040d00114503504c540074555002c1d403054400113200d0441035030a803030f002c0000c0c40790207250506910040020741000c24031071448030783d003182c0032500300c1888261414040500003034140b001c6007003c20640c6100710250b20261005e0513000040380c0d00180c400e0b01078070480c00142d0040c02920300204029a100354281c0136100f143e04e5203490341c1c60300d03000711401c03c1400701210200742d801c0c0100000c01c0d802003170201c20546a045c0d54611000504200300086d25201041410b008803c4101c01c680e440341002e980300c0c0031600318050f800481c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 627250773 1250 627249523 627249569
    0x110703080a0306060e040e0d0f020f030304030905010801090213060e04021204110103180221031b030901030501090b0a1401032c011404030e04090212240c0f04 70
    0x1105800080c00c400000c68024421035141e400301003201d0480d9103051000d4410f4040c00111410503000003170b550840d810701490325018000f00c01040700188111140b003d01055090b007141c01c282e40850000d60306172810009983d000300c003030b070240a04000461415000300c51740f0b080c007446440b42c0400d002058a07004025961a0b0554020803007081800c030f0940307454174200b4a80c0030b110b0541400311385400e501d154030300a04100300404550141c0606940403c80259600c10016022030702c11910040240403409064000110820f4044000442e201d0302c4000c0050103880058002c00045441c00d40c0d2541035503200000c01080303d83d0030110712065800240100c0180c4034003008070442041140110306150941c01000c002c003101c04008000003070000e000005400d406030b0b000b4000680e07006101560b0301c2d141d40903000d0f040c8010003040d21441104001c9080001e115048150000c024003001e552403211688694446042d0760300914100000c40354034407074000c0e401000070381d2030a0b980721700ba030309 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 627252023 1250 627250773 627250783
    0x60b030f032505030307020d0207060905061e0c0a0f02010e120c0904020a1e0321020304061103040e0118050603072105030408010908040f080115030605070e30071511 73
    0x7500f01068a41d41d10300020003035682d0490320358100040c4500b07040020070714030800f02403090b1000100901c0c03410821404c07034003010701451035130500c1c40070030840c207090160204030b400d0340c00c0e1064913016503074000d6000140c1003860b2680d049004046801440951361404941c00904000880b1f1140c0151214004504042c0140c0c10021003190341100c00c21500c000b14a40704c4c22688904070621581c1c000c1f280210f421014404640301503401884284201030003001d4440003100d030030045905040e518260203528200a81c07003500c0311035201800c2c103c80003d0340501c9034003140c01c0d0003c00c101490b00003021300003e61407040c0b151001d00c486190b410040d0a004440c0240081d1000b80001c0d0b005003001c40b0340e58494441c410a080c464000042d6614040c00340300140c49480c0181944146103403504400350000070540720410030715600083c2035544000c0100c80c1c002c0740c8914802928800d030501c2340e1200d14001c1d01440355102c080c0404c00e60240c2020406e84001d40e10304403030b0508a13006e00c940b0380b0f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 627253273 1250 627252023 627252097
    0x90f180201030c2001060311180f0406090209010609210209070509010302121602060106020105150d020102011404080d0b01050412110a08060a1401120c030809030c0418060b030f03 79
    0x1a5801c0c0b81c00a154080541106d002e8a01803000da041c8858001c081244801041c0701c410344081881000950700c020307000030030743d206001e00740104141c0c0660f0300044000c0310907017002d000314604000600015804a040407081745003000d80c1c00001d006034001644c0140c0051085d000c05c000055120b00341d912075010707540c0e00c2004102400304d40c00d040220554882902031014018859000006200f40c070502899001b44507413580420048000c2c0180240361048403001e81c195922038104940804821107554455400303100b850342c1701c1c0410200941950002760246041000c18041031100125407043d41c8512548600c10144585140c03003c680021000d0303204c04001c1c01000c04210034480f0301d070028008140b00344040749442e81c0700d05002d12502080c840140107c045200c050000408010041c03c0e0f1043c000c0c03c40f5401e03010f40c0005022340d0f1242458444901c3c0e590303030303071410008140079003200c2d001700702e0203040c1603c51039060035540d016048000411a4900005420880680c0e000e0050 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 627254523 1250 627253273 627253307
    0xf063314120703080705150f0708060103110c0604050d050702060f07020420070224120c09030f101407141804020c01090515010b040b0904150807090f180201030c 71
    0x108079540d040a2003560860701080d5198011900d58000d0032000c0711f8440d21078944104a06540d0b100c40c0011541d840e0300400b1641819034400c403640316940700501800c01e00581500500d01460585011801c1401d03242c803000a0210501c074040c01a602c4400383c54100c4007880e900b035250b41c2a4000180030702070302e4084d0f01c0d2034040c106900b103010101c800100342803402603500e03050400480101c500c204c600007100045a407014010385420074800c0f0242c0340c00c4684034001506000b03000000a041860301c42060020758480004250b0080307050040184c602d00580000c021403400b140041c00c1c00d4034004c20040288400103280c0c0251450141c11001000050030454994407a010420f0003001c4a00c02a90203215030081003003a9040703c0c0c903450507203191f14142820305140081c1c10b03040d90404c0a6250b4483e490b01c0023060034145e21800c01e00284034860040074100c2c0703848900412908084601250b15040c21f082e400d4007003c1740a107440041c0e0a280010328042080070860714a2140580e661b1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 627255773 1250 627254523 627254533
    0x120d140903070c0e1003080304030903120507051605030706050c030f03040b0405100b060f1815030709080c0a12020f040609021305010203210c04030f06331412 70
    0x2034100000301600319503100704010010300d03490741c42d070f00d1005104884002c14501e0604060002031090400386402070720900340b0700380700d685995400d00984441100c0000081000c99a102400700802c81c000300c06514013001d1201c1402e010110352101414002c0702d00380724001030680a4540d00b08215203100c403c240106491f0b0a041c0f805603030361b0100303031401e8600784107139042c16a00c400e0600c13481640303a04c010583c1d864000501d0111301d030350b0000d0748820b2890203246005074450b281c030070104085a16141341a82d403480d210001034103507440307904511001c0d0702641c4003d20f07507107500c1006000e64240b4901812191118400600140c042c00070035500075003003500000350300f00e15401811004248020345003007130783c944004907503d0140c0982440321440c50b54280e0000503110903410b4112010f2081940b500e601e07600c0e2042038072402c03207003243d80310341e01d805032400348130034050080d1b51151030007170600910100c10a001d0904814069804c00503030f5246030903180c0d61844d0441402e19904010f0351 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 627257023 1250 627255773 627255781
    0x1413030f111009140f0a06150e0a0504030807020712020904210e042702120a0b090601140108091b04021b010603060507030b0d03050901053c0c120d14 66
    0x1c2d0241c20b420b00c1c2201e03209504807540144c550081041c070b074450301100c0103010020980d01d611010b001c40d0095800c0f5444440d8010031b180d03031018401c9200b13603d50100891241481c0c5802402904020242e00440d00040801e0010b001584910310300144c0441c0c4d00c607440c0c0c5580c1000e90031040c07500d07062000c05003104401c0c00d14a800c804005100307042100d007004500719270b80300500c81030407400d0130000c600b880b030310039100500e001c944401030051f0000c02c0380c7c1d0b94803280da40c04841490595580400d0781c0820010040503070840300038040f01c031007840c140b0307598149208070702d50710004e01114440035824a03111451035129a41502c21001c1e01c01040c40581d01c05815150091409000949000703080c08005030f042802805180181d41c0090454030826403d901c0449071a000000c000f410000d04101e800304580307120f50904090340c4c1c4040540c0515080040c40340380ca0080c20341d14540080103000d807440f005800310b0010700503d100e8504664400c0d4412101c4c00800101600802089a5074284 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 627258273 1250 627257023 627257053
    0xd05040b06090702030f0702041802031e0105010b09090a051e011508090102090a030b0a0f02070c180c02030d09020f060403030e28050d06090b0103060f1413030f11 72
    0xd6402160140da4000194035000d4049840348a40d10503400b107080c0800840005080c241c0c0901c00c02c031a0002c0070b42d9510034135800281050018002800ca54904803544000c0400a10a241c0100041100c9901d800581c03070124120400003007030803c500e13640c2c000003244540060031555110514000c000300c0f82d038440c0d4440074003a00c14a105030005031640c00103104100144203c0350640d200074410740c070807072842e56a91240000103003580c40013522a0010685e004a40c000f5006da14440d2107602005401d0804c6141e54807860034420414906050120070703c0d64000c8101e444984107c100807a055a103400410b8250010b40865500107100040000c14194002601200d040c1b00f04d8042d81c0c240c0d00300c003002510002c0380303941c580511152002080a03103060a0ad491059100740c001040d0131405460f00b01d80450240c0c819110701d82c07941d40c0c00035211940d00c542c001c80e004544158000d410024407a03585009100b40040034401a6018250403e0140c0e00c0e02c40345a2501c0212003500c3c0842c190 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 627259523 1250 627258273 627258293
    0x15050f0121120201020a1d030703020603040c0e070c030f0c1104020313051006050301060b04030c2102041a01180305120912030d0b0f040608190c17150c0307020303130201050d0504 79
    0x1080d03002a103012003400c01800d014010310341f00c0c04018000e04105045800704401580082c00c100d90900403c9030016140d50340c1d820152044655840d50b8480111900b00039100018400c0d108003044400d0300301e1000100d120242d00300805090b107005845c0c5e50f4441c00b00302c9084031100080c1030751180078a07030038901401e60000d5069900a90092003695643c8402c010342c2c2c02107000c000c2c55881c24620a00a0044d082c0b4110803848486418003990503068021400725445911b01d00311410703d42e2022545940c100840401d1040c0004620111a00d10b8a541d51158540c0309080400600041c0c011190381d40e441c0c81c0307030302c0210307010940f0b5460791741d280400c00034610a49010700944a42003000c030310340b0b0a841484103c590410180040000c5e0382d041d03407000040c00808542100d240a40030400d90060446610b000314054024450030211900442c28034038011300510350818100104020311ba804403d0b01d40120f80c581d6800c1402c5464401a1707103500402d5214030301c451400003004244212541 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 627260773 1250 627259523 627259537
    0xc04061205011503031d010207050a06050c0708120a0c050307021915050708090111100c031a0f10050a110a0b16020604120e03010e07090915050f012112020102 70
    0x2041800c2002e00b00f0402c1000e5484040e000c20701d5050000d0310300b904581302100644051058440b04c64031140014001000d030b400a00c00607801148180441c4420068070000e00000c0005013526880784588501a2056854400c208000c0c80080b608110301041941c400f00d50040c1500400a0407444640e05082c0d2849a1100c0c118880000d0618070b0240080f2881c50760800009440d06094100549401042085d0800c2da4462150342c041d501c0000e204103420480c40b03030b1f00411080d001e8001c442121840d100464840c41581808000a5642048061180c803003418480d071241500202035030500c4003c0d001c0c0c21107010340710240b01000740b00741e41c2510518070944040e81c05206213000301d99402e03044030b00401010603002e900181d90b0117021001e0054000800114181091000032400e0041650002185940f40d401903803c124100d80140401c2c0c14034035080242c1d180c95030100d058210103210701003452a144c50a01d511440103100810b095802845c005149903890900034000d602c10f80c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 627262023 1250 627260773 627260783
    0xd0e032802070b04060e0904020303091518010504150806010917031201090b10030e162306030f0f0a111201030308010803040b041e0f03080717160f050c040612 70
    0x100002c5030038620300c010340e01545d840c0e680b02103031466058140004500040d00c240d9041c030013403094002030307134400d03814400c0224100415500c403c21502420940140b2100090500c6010701c800c1c004140a030760414075030003880c94118180e0300c900005841d904d20300d4006501b8070b08080e2444805a40000040c02e0000fa07880070020244c0ea502c030b00000701c9012609c4a64406109000f4080580c0720390820a088080340d41981c1900115151140380d0b010194003440c1e09003049920314403202c1640450f4030701001c0988000d865880c3c5024410780310708000740042d541c0503118012500c1490550700c01102400e210700c0700340c1e80b101c0f0081180c2601000b440700701c0001e845500081403122010050b5000c445460b160b8504090405680c1180161404580ca10349090b88400180612150b1003050045019851003039503480c5604020304e030b0000d1400e0800c0201c4040114417100161040c0d407451964200c03d60203201000d514015041481e511711640d4000d042c60310205450a2040691226611031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 627263273 1250 627262023 627262033
    0x6081e0d09080a0605090102040b04030b060907030509070e070903080a1101062c0402060c03070c061107030c060c170c16090c140f070606030f23030d0e032802 70
    0x410300300c603032016074001c20086802030204000090241d810803900110100000340c20b140c1c5400d031510858200364030a41e03040600c0310510000e4200b400d003190700003001d4981804540b4190b840a80e0710091740c800d0070140400800040c210601c81d1240c0000b031a0701250391583d4444c0604006c0c0480c0380b0300b054180d1546000f0f00040c007840f00c081085081e0302154100380c4001d500610007948200c00402c02c4e40c211000304249203035914248000c05502d48200312618001e810301c00f005003d03000c0344038401e071168090320045c004908000d9500b007c07540d21380340907045458549088100400701401810001002084603038603450301184a00074a41c03c0703c484080e840e5608020015503140351205004110210600c2107070741401402030842c40d000a0120b481e1003a00e035141c8084601d150300646000c00004003490402210450355420064140e064140c04e9840d15021600d0f84a602c1c40c82c00c0706d694a60a0780074842c014410707601400302104c07045540c120340031100c8410040315100c2000500034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 627264523 1250 627263273 627263293
    0xe1003120206090d110102070c060206012912130c0305010605120114070810030b0408070b0c0705100e010b0d0506010f17121c150e150d020402090406081e 68
    0xc0050810301c10007404006003556800030303401740c610a042d00f5005c00300c1d5400300480000b051280c14039500800540d8000c200641c54808130180038001d0102191450a4440d07100c018403107000180c0703ca021400e080d60115454005002e80b40c5403545400414064448c1c00003c20f002042d4804012543c0c00e031200d80d00031401c01c00c568200e1b078188507184e82a81050b408150020710682d503103580040e07081c0d00c0b401000d84075114005403040454003151070201c002a4a0108100c251406401c0103004105a00f0702c6016074a207610341e0104050703611825682c4041c0e035480c2000350011528000080c0141410802070708000b03031544000d00402c01c000607107000016880001c0030005c85205288400740540c007850510480d070950010741ca644e0200d844200b44c0607955458807502501c03a000c0690540d10034a0143c00e017160940c0241a041060034818604225485404200850b250f04541c01a90340e00c00c400000d0040540b074014056511070703240f0b01006003100030880c52049440500315101491 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 627265773 1250 627264523 627264527
    0x40b010614071e052b090e040f0c1509080c010203070b19021918080d170903070b0f090c1905060c0705100f0e03070605071403040e100312 61
    0x1907103004080e40c00314200b05600100e2422100e001407021070540345002c0c155542c0303c042c9044210205800c080045098175000035110341d00c5160042c15030301300008003610f401114030075120000c4c0301a04810603410a4401c000d645424503020303244900450880e5440048020305184443c0100d4000388178179120910550b00010a9501c0d480d404030018903155506506031210303480f69601804181c1d0207200104568007040c208901c601030503918140000038008170b40e01c004859602c540d01d25009035440c41c0002e0391011120381e402e1284100740d00d840d07c5003001507155101c0c80303001a124120324814400c60150205219001e607002401f22016420500f0410500d80d081031100100d103103100c0004c211908152000d424001d0688003a00c6a040e90396020078603050000c09000c00181c0044403015005400001259034020268001d140150404001030903a01c90008040c0c901d8540d00e1105040000810440c1c000d4150b0a0b14010341d424030324072825000742640011100f421030400310102040c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 627267023 1250 627265773 627265787
    0x40f0e15090c0706020705030d141f09020c0309060c03040e090d02070302010e1903050c0a140609040b0d081218031207030225080705070b0403030509010315051305040b0106 76
    0x1a00101010001e0300c034054000b040343d010b5401141c0c4181c0920500300820002c0c0040d00c0d10b00600c00000c104011508104001203030000d040355042c200c010111240d22111107940025101e020100603a55501c40040600d1406011100b0f5801140010300028401c0b0101c050700031201c5425106203661a00890310fa200c0c101d04071103078010307400310404102643c46060b042d03401d81400b6017a241c5038502d81092807418990390300b050352664810090034500b400e0200046004080940040d0003050004001484a201c0d20020700e12036900c038180c4c040e03d5a1100d0000300740c00d0b40705a0030f030b90301c008280f80303e04c03200022103071800744038a00c1141409000c4040101c03200c4428001034442e0a54414100354001d42202500e40c00850252030344040c0e1340d445403111400c150180c00c41d603071210040d00d0583d141502607041520014414401080003980010940d8041002428045451101c03100700c2c3c081880d40794000c9500c01446151018240001d40c85503010754000d1481a20980e01d85800f0359100d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 627268273 1250 627267023 627267061
    0x10501050d050d051b0a1101020f0304051503040303020c030a09030501060b16030c060204090606050711030d05040b0a12092a1208030a022107090609061e03060308040f0e 75
    0xd5000020441c2030070f8420002030040310481c85250f8040c12000105c245800641d43c0201c403003000840c5448002d60b01003284002503840da42c0110324240c20000424060854880508580346010010904160007034042d1610300c00074004490f01d40089000040c81400a4030080ea141d51a1205c08502ca00c408001c4560054005c0040f0760385842d81d54045407028004041038034034507824000070500200350700800000b040d080da105c81d21101107040181141300402202c1d4072179031140d101c101806030460155400c542d40c54003042c7d1103030280c05003034803248081030007881c440346044018010440e05048119502a201444d02c86e4000d09041c600e2583c00e0701d0080007940788000048100041c007000045521011021001d03060004152400000c102c40f0300e50041110f021004002c0708552110122004003103074540303800a540f420a0140620400b203281e00c09000300b141030201002d000c1d8002500656100700600d6485540b0b44441c4140b044c2e40c014107408006020201e03141034071541d0101c00c5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 627269523 1250 627268273 627268283
    0x41a01080102041d100e0a090309080f0c100e0406060504090c020d210e030f030612061504050a0902030f160503060c160f0f05010b040c0518120f120903010501050d 72
    0x303440104d0800180b000700050408214524250b000b00e5a5400c01e19014003031001c0b00d0700401c4050581c44e002e803400005412245055100e480541884800058402608082079842c0025034044800c01c03a04254608842600107050400c005444c90b03015005104842c510441040307640000c010481c1c445403110840380001e010309410224501b249034a001d502c0e0441c540001d14214403071289410341c0c01c110901aa521404010040c050610b03d460b40500c40040000d094140741c001c3c448000b11f5a40a1613901a65503800001c3e55040e180c1d01607260b5940003011a8951340010780e020780c0c0e410b0f01303501c4544004c1c03a0150020f007900340040c01c80c1c010500054103506244c1c200403a8140200b03e581c080e1507240b240d140c140d0100d550030082d601018000c800108420401900744070549107030506100420004026144e450300181480e508800030403030340685045a2203250303600d4075070309070b00341e1040c0c0c01307161800410032404030018004040140e000780700a03070380c441c01c1040a83d01000d001d00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 627270773 1250 627269523 627269549
    0x2150415051c0e15070215090c030c0d080f07230f07050f030a06050c040b180102070e01050d11210a06050903040501121e110703180f05120307050303041a0108010204 73
    0x2020341e13545140c0c140e0044852040741c180030740480c0c0d0329840e054240d0707000040303800c9005d02d00880e0409003c403011811f4142c0d45003405001c1c50340c07880c01d11b114036400f6040d0860040340e10b01c10800c0490980c1c1c60324070110300c024105040722004684818402c400700c00d891041c8040003038141084800c5503800c1000038054080742c0400c0c2c44000241ca0003c0460a02d01c2d010000440d840013148040d262004c01d11960044040000002900c6e00b0500d800614101111074010030640d56185c2405540ea644040140c0c136400d4008041024160100d00490794100702c0b64200491050001d00603240500960041c04a9190704144c603031a03203d1030145a0004031407440220344042d80b60061013089203a004e1449070030610500050803034026402c1d070303020f02e44009065800d160384801341c0144140c0d24038403140c1e05440c000800340303404114840d00c1c1c05020080c141007210076040c807c0c1c41200c0e4000b01074039030720301d050b182010341d814004812250803e4480000715801c801482514203507908107410315 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 627272023 1250 627270773 627270793
    0x11d011a1203070b1911030610052206121b021504240203150405060f0f0a0902040e0105150307020a0605180a080d0b040b0a0302150415051c0e 63
    0x80c6085821445208a2208002c0000004c51314000c1900c0760100300240d81c14110302080c010140c402c5018804a0321000740144003a9940b031034800f448070091800c1c0366580d1f04040c010440c1705840b000001c40c440003041c1e00024031a4101c500381c0d1620030341d0842002001040d1a004902144904490006174800c0d180e00108010300ca00180d0030a00800540c01e50491001d801c2d806401075128000c03005801005100110455011595000344100c0d4107211510300300303000c01c00048480702c3d824414a240041d0741016100c070000d0384041c0c611000190b503101d8449041c0d482c0c2120a1182c280203600c00510014803a0848003645d01859096014103100c0c2c007291a0a03001c1e113405000200703440700041c807501404400f001110403043c030407007010b0b0321114094000e10440d200000107502807820030603a80c6181d6030f00c81d85041540c3d8121280b9090a00380c07036404c041d40c052500207064030011480404015a000009800750941c074107000407083c00456061800da508040c01400142e01c0307210303e5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 627273273 1250 627272023 627272029
    0x601030905100203041a07020c13050a06120804060f0503150d1112010c081605070b0c04031a06090604020f031315020a03060e0619060809070302060c011d011a 70
    0xd68500440803210102e660880107022640256000c8881c170682900120350780407459003065001040d800609660400040440d90a1544e42000c0c003096950b0b030002007410741ca0f0751100e0f014042c104070303e0ba10800549000c1911780e0080c0a81c402240e00ca10100c0d080754030900403203100d90880a15018011040350034400d43c41044001211101070105e058101601d5500592010706074410001c02c0f41b02d044000540300e41c1000e0700620480004083e4411165001821201203540c810813100a45d551010700c42840c1c01076810007000410030600d0403c3e10300381006d041313000e028115080c044ea91541c2081100b280f0410074030140f5904240009130207104242c1200d15018012040304100a941401040c00c80c0c0c0161101004a0342d2000d041c841c00e40c1c000070b61940468107481448a0300070014030b2003202c80c0c961141c071040114100015013042c80a000310700c01954043c09254950b490500054080d013251030100504413420b5103040c1d00582c050040c0c0000c2e0400004603191071540d003080c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 627274523 1250 627273273 627273281
    0x30d020702060d0527010e1b2806021b012a0b011206050c09010503010e070c060504060f0c17070e0a03020a14090c030103050634020d0306050604030b060103 69
    0x69034040428002d8000e07100b000e01a1034401e8811722010402c40d03034004170141d0510803aa0084580382e01d031140c4629070440004400c3c11a5418071113403450544280006006021200000c83c0390b00c1109100b135102200e80340d401c070161100e5400b55920828a004409054113034210302c60700142003000c4a68400313485680313041c2c0f01c0792122810429192140c032506400b003000e0b80a803503440c007081720600c03d100103071007842d07001508071052a01c1e003903031600024203074001800340312400c01a90740850a40c1d805428022802544100103100914040c00c0c01c4008154480c03120300c0d0b1604051700300c1c880380e110704d844014621b90b01e0449481b84d1203140003101e80107020701c0e411360060340b0014040003503659003c9520050003002c80040c4070000c1c00c400d2000300c0c1c002a0001c061844140010310000d80041640c83c0c0c8512480307142c0e02d031081143e404140100002036009203040d101d0601e0040c286e0f000c60b40c1d480d010400c0e2014040da6503680240941d61090b031101801290703030180800c505620a0700 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 627275773 1250 627274523 627274537
    0x2040f080f0d020c0a0611030c1f0c0201180209071101090605150603060102100e070801060f1d150603060103290a230f0a08070e150409030c0f02030709090c08010e0105010602030d02 80
    0x8590070702d00009d070060700c1c0041c1e504004800700a9008141c40d000d6450150000c0d40c000c07813000348403d103100001182c110b160340034001e10512283c3c3c0005d41031172183e0703007000c03201c5e00c5507000340000ba916040800040c0b00940d058030b00070003046450600390801c4000c590041d54103900410b43c07011b150f54140d00420080f14603203402c0c00303030940004a44d03009008000103401034442c0515083c0c40c0c072040c0480340c00c5602100280d030146070304111540c14089214480030b041030f00d24035074965170600100c0091003030745240201c03c80a500d802d62243c880503a40c40c0002c01c2a511010210303100c14803406084d443d0544580d14100c0d03004401e04605240300400002080030382000040394481c2860b0b4248500c507009000300f814410204000017410801071070000710300740c078100015915510000c1000707500c64006050742100e48203a40440d02d080008100074a6900d0080003c41c0b41450800021812403044204560030305907610f01c80001032003098103d070f405400171498110207412a40117500500 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 627277023 1250 627275773 627275807
    0xa0f1404050a0b0607051e0111040603050901020706181a060d0f081605100c03090f080a11031b060f01060e0918060f06130b10050d02040f080f0d020c0a06 68
    0x2030300d40f1840c2e8135403101805030188204042c0800305000700c0c850a070300c003600b49800e0046c0c0c103011400500c038034030b0302c129800e60b0381038a004110b40d55901b07191800381c801e00b9001011a85480e0360303e032001c5a0903120f241030910402000c2c101c029190b8410101c03000540342150310008100c036940014050165041e1100d00c1031020380d0078240168101d0403001d455560550b5a904440c24085004a403803140d80240781d500e0500700200f40d227540395440c0d0902c000c0402010502c00040b1604128056035000303004611020441e0b68035950152880547c00c1e01940040e4648207450101f00200402240181038910a46d18000c400d841a800c0250030480940074640001902100d015a61024040729121701c98a41e1100134500f41a0140301c008081148074182d42e40c078000040c01c0503a80c0b50301c28030005d06c0390301d44076849a4500071003034000e10841e8000d240c1c06922460010b00f071400441e404440020031810307038048075200b6100340e844825035014194000c600c01c206001a501420707a12480031045 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 627278273 1250 627277023 627277031
    0x10c03052a06070201091b030507060302090607020a14030c01030b0907050a0c12020d1b0b010501030c17010906030b010e09100513050619060906060503041e0b040b060a0f1404050a 79
    0x701850502109464100050b51508402c038280120113604440900568440100c118030b107858990b04c50f0901e001d40b03c2095000150038080b42c2da0b0400303a0306035980082c0700380f4507107948146001410150b5203c0e68041e00074007024012960280c442c0303c16501c0090400c5180f40d9454000b00e030bc030341c04911000c1c144000b424410300896040110a0704084113600204142d9041c200050701051400d240398108880c01d61035a0b002031551400c503030440f44203007408202c0c0ca2043c0301c1910368103045081c800c1c10303800001c000a500021034000070212406801104807a98031800740ca200d09400b21a481c2c51540240c030505c0707011860b070344010f5100e02c4110800403200c1d01583c0301401d12000782c40340c8124848000148980442511031030008248842041242900d0002d02a0090100410250100713000e2181c103d5040120494440311030f80c01860340b4054645854440b000210649440d030007800c00c9100881c903d070340783d003402080e200070b0b00112140440e05000c20025084c0100200342e841e4171 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 627279523 1250 627278273 627278347
    0x706020915030c040501030f0e0307110105040b12010f050f09010e1005040207083c03250f0e09070c060e16090f0b0d030c03180b0f0711010c0305 64
    0x810400b940c0604400e4010035030ba2441d0600040c280c4511120841510f0310f0016101c0c8000000011100c1c00f50303211340302224604502c030050341e6074012503200100845000440e1811400e20844c0c66043c2c40c010078101294988400c01d015010301a501c0c5907400c10101300040c801701c040d8206050307000c80c1c3d400c516416143c5600218081e40c0050300708480000010528040d1803070201d001d03c0e0101c070301210107100b28207503500900030004d031b40f15000c13130104002021913070b04040c040d0040030142da14000f825220140e003100600004102d4280c00014034180f00100d06860480c01090040340d9503034404001c0e40c01134841000404a01c1e0b05460f10b03100b4903a108100341c0242846034020302000c0000030746268403070f46403000d1f510400601841b41441064090019811800030780d00141c040ca01140003c00650104100c00b083d40c03c01c3c4078541300403078004680b40714003004010aa10801402054090b0302006540c12010084010003044d800d000301c888454039111140c1d180806d0511403145291 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 627280773 1250 627279523 627279559
    0x5010816230a06050c0d080c09040f02070f0507031e03020c2808061b1c050709030c1203030f2c0309060d2406080f07140d05040c050a0b07060209 64
    0x50b180c3c405030114802060104400c2418008042101c0140c200385034607140414590030360b407140406151103a030742c682400030038640680c107a81071198003110320240103c8a040081d40c581c0c0320710003110452014081810724002a5803c00c80c02a4103800034803800f8111003c004038604140080e0120005202d1441b8014118001d00c02c020041d2001a00c4542040d0901c020000d01030207000344031391410000303450445a03281c19500300d110b8228002845d500d509108440c205c0d01940091b100e00e5400901059020204420881c02403085c0c5080155801d401c62803811b9071403400219200c0340040840c80400d072000d91031800c40c40c400e5405d803880e0030100000a40c80341c001c1c03500c4000c043d0350341030900e481200c8002406940101000c100712124505400242031940080100680c0c0c60400c1c00328003c1401500707007541c01405402216291002055580000e00e012141607c3c00031803031800043d20304244070080d0980e030010320b009103820100d07181c85000e540080102c40d0040503030500011070714 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 627282023 1250 627280773 627280789
    0x50f060c0a1e0e190501020d030c0909020a050c06040b06090609040221120f0714010219120623010e010f0c0f140f100f05060112150506030a020d0501081623 69
    0x42c842c0400d8620303031700301000240b50640c000301410038140343c640d00c0007460307402c120701200312041d0341809030f0741e10700300c190844a50007150342003045440b984040c0070410241c20541d91254100342c940c0e8489a17a600200050321000341d9000e504a101300c0c044040a281d141e50000c904c803201c0c07044800400040e40c00d00c829500c44d00440886d03810110b10541041070b090003a01030046042c000b503082482c0c807007903c150b41c400000210103110049203590158240c64105000a102e40303490040351070449402590600d000b0880d450000b039500110b0100c07980a40c0d40c4503541da405541d03c048540466a44150720070b207411054502890600c8402038407042004070314000803072640503002c4c8030407500564058851840c5c442ea2020300740000c20103603036030040041400c411500740201d0703000140c40700d80005481d5504690340140e0300100304052140182c004140784d4501d4281000f0385daa0b03070046161150740070b0307550f0101c0c2c0e88035003000c210200ca10954801d1000d094442080000c42800001c0c03444 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 627283273 1250 627282023 627282049
    0x1050913051c09180626010e011a18070206010b0906070b0403110706032f120103061a0303040302030c280f24020c2209050f060c0a1e0e 60
    0x20307030020f80520a40300c036940080d030300d520500402d008207410003290001e9030f07044407505503d0480d481d0401c1c9200e02c0940181114152060080041034402002d41d07409a40c03d21115008104076141c1000c2a2581c8981c1d51141040d42c0c051700080e420081008960707030080d07812075840310041c00050003140765030310784900807403007519290b184640c21110b040c240035030f03a404a024946000e0380307801c4000301d1045000c0521201b04800d84021401d080c202a5809030718034040450018034004400c01106074041c44180078a0010741ca0250500c43c101940ca1081e400300a42507001815010001d0500080755040e1000343d10691015000d0488a06619504d45d4094500d108500104001c820b409102604601807400da15800b101d01c20000a135551170000341c00f500811000e844e520550081510310749041d14100010f011280c140c1c00c0250f55000c49590384c0080b405580b0101e0035203c0b4550845244004a8032000f255465204c20b411b00365202c00310520a10601e0444821555540d070010004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 627284523 1250 627283273 627283277
    0xc031d040f1b03050705070302120d1407020105040203010e010603050a110f030d0f031d0303070f03180311191509030c0b040813050102030f0d150504021c110301050913051c 76
    0x8404180304010f064900161410b42030050410061000c2a400704d480c2500c14012505541d8803070b400403e4000502041e10041600b0408005100c5a140d06400080c0618001c40c024008070f405160028202e42052000030036980c01081c0c07100c000b441035555000e40c5000181001900ca00360b030082810140013a54450010b41c2d28511411159014401d4640c60307410100c00c42c031201c4004410aa03a48405020101440a00c90f110410349210350880461110320385a0704a101c401440c2c06000d0031105100e140160044501d801480107842c040111081e801c1032400000103491124007000780159882a810004c00143c19004543c1e1110031900030762180310303590350310784e5401400ba1116049420260443d003040000840760900501a00e403400c544039000580c180d00c00c0c100011484c0c01d640200e810900101d40304058121264038258040c19052080c04000704c09015035810384402d0040380c1e440880000070481301040741140c81c402034400c2007112300c0300801c2c642c0b03012400604280000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 627285773 1250 627284523 627284561
    0x612110c0105010308210618041112031b010510031e0606060c0210020619180b040b010608070504080a0303112802150c0301150210020406020318010c031d040f 70
    0x80c0d0f1080c004c044800c1e4141c2006c0710340c1d401e01d200003440e8603142458581c1c007008050302040902c0000402c000e16504010048030040301d9024065860740c012902d01c003482c00812a050007002018010148103480d42c800102c402405c55940300750301150403044c03080da241907500c118001107545c82060007500c0e00e61200c000b5072184e841003220400c0422601002c640044003031011a5a42c0f010325000022030450118416109803910b049141c0840406440040c6240600041c4500d9105035416991966100e0b036445c3e40e070f107c0540c1d0030b2099100e80c41c0540d10040c0000013291003170344184200754118a5203442c015140d02d52400d44890072901035494a0958854640f15804010340740c4200c4500100c0440340c5440e04a09095000c144610b06501ca9240e03c8464039900c02d228101e850180d001c011511a40c6400000f5a00d4002e00e081062401c00c44092440755070042440e00b500701c4e070640c1d441118102c1c054070310550000d00c540321600319490300703010a11b12801340101c1c44d2000704480050 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 627287023 1250 627285773 627285787
    0xa080c0a050d200115261f0507021606080408040b0a1206091404140c03030304051506010c020904061a0d15060e1e0606160f110102070612110c0105010308 68
    0x4a801c0400c80380120b0aa1700d4061007031004002c0354002030895510b4034048040c4080f9004402c4401c00380e07490714186020b400b0400406d40301e00111080a9440c0b407008000d5551207070400d03a5110004903a100400840f10801c0011038803980c28194424031604529040030303900d28004c4801d402085209010604a0b42c5024500546101c0d020080c2060403040c003807500451300307410f0100000740019201c00305051051080b6041041054182c06c000ba00316992454541402520340301c94401c20000d44c041c00340807441c950b10079100c60a059070000c041d04410340700c943e2003000403c3e80ca0740005162000e069441040d96a0780c81305079074540107085403c107030031110110b101122b9442d009919000e6521043c441c1c490304030901c001c480650f0010f58800394691000080a90048016032809003141004101c01c110944410341051807103041070b004030800c0382c4010380e140e001d1030090f0341c00601c081d41c12149145071900f00180c84410902401d151046090000742924400d800943d02013000203010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 627288273 1250 627287023 627287057
    0x402041a01120b030102040b0406090e0a05040b0c03040c180906061e0b0f2a150f0a090c0905100806150d08031f0e15120a080c0a050d 59
    0x4610014950400c2014500d540c000030301200300e16014218442c1d6250b0010700c5545003581150b0140081940035900c4655540d801009010340d40202c11808081e00c001c00c0c04d02543d80201030290360301621882c402d5440c000e200307100d508000c105540c444041d0354009241d509400110703078490714202c00840c0c5003505081040a948aa5201c0e943c584612402d000d1805044405001910380300c0780059641ea010610381e01c12402500840050702c00e00038006a1008290130301d401150a0708020f60340b409620280d10251244102c810b0001040ba800000b40306956903482294441d1050b21501011611840c0c1c501c100c403801c5503804402015030100f440403a804012036503001806501d20710601102c0c01c0419016886944010003050011011542441004011300c0307800c54030704804101e45540e4022140a0581130300c1c07849000c4a080400312a50030040c4002103c010038900921006010b6139440855034041d100c11121030052121000005406200005030403850f03035118111107901c6005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 627289523 1250 627288273 627288281
    0x1d16050a0e0a020c0319030b011409010903240e0304050f090705040e070e0d050a020103150b030c0915040906082a040c02030d09030512061915090e01030506040204 72
    0x620514a100c801c1001e40300d84000a98000600040540c9401341041c4540c135500400300038000c0b550900c1a6001740310b905a006c0e5221050136a9407140084a9031440310311031181c56081400a140b0103c2400880e9840c0401003d00000c0c41d02c049095440c030054408547d6150202112504005801c0260b8035041c0904c400c161401c646020312400c0021010302140300d80c2c40741c181e01540c144001608540501d400003550b0001422580c0040442d182040c1c4031058600200c1c0401d00d840d262a03030021142c1c0d407240980d00c0034401075107140c961000030710450304007241071307680084080400d507140810f0401410040c01c24242c0031480c00d08090310700c2d051001090341d10500e440c10344821001e00c01a51a0505900c0080d00c0003d1784c0383c0b0034a012400c510494041c4000c050400180c1410150701600810020f07095071401c4503070b615914108102d03201d52041041090301c82e0081406032004400004400752201c0c01c040b0500c65035036000301d400d400300341c5c030030707100c2d90400f8080009509081c06 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 627290773 1250 627289523 627289529
    0x50405070504061e0215010b0a0201051b0405011d04021308060106020a081219020f1b01110a050a030209091312030c1d04020c060f06030d0e060405010e041d16 70
    0x1442420542400c000401252901d9406155504d880100a480754001c0c011441a99460000c0090355038545a856020b40c0c44081c1030001907103808001038000d00347c24400480c0b05000180c00e407038a460b00c1c004407100041604011550029806040d800e6522440106410ba0000031041c14203441d000c2d17003508040d0164800400c0d50000c2000030000ba84c11000c42e0130f0000d81c942012400e4a6070074021300003005009809100350b1000968000c0520045c0103412201000780d146154a1246603099003039038031081c0e44612103403082c00041c00d928010000340c5500000c3e4600103003001c007008001072002030151000c0000d0b2240e552220180860700d20385003c44640ca0a0a20900c600d00c0740052526440220320004403c20b0308031401035507102d804460342d442e20942116001e041102900456003800e4480a00c28400e61032101702c421301900380b00c48070341030047c0041d043c00d2070b05005582500c0a52402e03944181e07910301055130300503810081e985800001e0b00800d202e65030622800813420245e0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 627292023 1250 627290773 627290777
    0x2a0501140a0b0108042d050319090b030a02160c030b0106090e3102030a120807080c1903111201031509051009080408070b09130204080606010c021212030105040507 72
    0x24442d410325981000344d0980140d4401030780f800700070740c42d1801301203070010940401040441c90080000c1c01400030142c8402d0013500042100745038400020380e042952403290f01034141c8240002407484c412079000d403002107000700441c541d540c034560f01c9500c0104a600200ca650074900018400c0540c06045400900000c102683e01810500da06c46481000310345044540c8a4500c031840c641d0b06c2401854103c80d0f80502100c001001034038140c01480b040303c00500001d0000000509103500c43c0726000d0082c00b400d41040e02d05417901110710081c3c082501d48205047d01c4850316004050701d00300505140383c4078041c82800f0350561908144811110350b8003600141083c0f0440c01141b404a03490510441400000856800743d203842c46150145500000d114014031200240c851200c04c0200040c40f4125884042d810150503940704a0249000300030b80ca9002c030000422031f5010b1069072102d80d00041c282c41046880d10406894100e075503001300d40069010004208138242401400d030030005074 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 627293273 1250 627292023 627292031
    0x70603060506120601021e01020d0b06070f320f0615060a081005060f0a080f0f22060f02041404050f0c0f0f041413060b04062a0501140a 60
    0x11000260b0340d4080d00b101d0080c03407416000801d007917a00800a500500070305040818106d43c200280034000d4000f038080c10380d09401d0050407105803404804940080e5407019030030081442c03648034410f010014810103030741e045c500c20f41d940d040c02150301d00348203003150b0342c0c010405028101209418104080c09115440b401410000c0c5c0c02d5503520f0507030b001502d5030f1801203c641d8a0301c0340c403000c00c0220381c411034011100003202c1d581081240000c15040e040c82c0c0b14606035440d0804500a5001c0444450021a1000010400e543c1c401d0200c120200c60a501294404a15407614000c0310428036a0740343c8240e00050800c03050320080501c802c4040d08550401031480c10344880186020f009050a03c1c003d000030f0342d10b551107000420760740c920089c02011a280d6440ba06c450521449864603144200002d086600d02e0a0840c002c000985100c2c15a0f94200740c54128256809089400f1a01d0301d203010b202a00d100101506002c001c45005100100381c0d00c80a24400360303072982c09041e21070641c5c10 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 627294523 1250 627293273 627293279
    0xa080901110a0b071119050d08011a0a0e010e040e160b040b0306100909180605011e261b04140c04120606120c050916021209150304060e07060306 64
    0x29030350707800d5100075241484100d56118800d10b81c11b00ca25807801492000160b1841002d101c00080c1808050685854004850340c0311a04480c600303820910114070703040208000c0d8240340c0725000481030795106043c804001c6207460f001805a43c0080355090302e07030b40800070100d50a50601e040c10010842038010502d46400c00e02c0c0350350144001040d441c014503e41b80085080340c800c50220b4010403074108104400016140c4120480c2c034600750580d4100c0c106030001c1010300a190700410010a10409150454580210402d000c2945001f501c080d00c11540800c90400c0c00303104a002540000781402142c07030b00a42080121140403060b080d25565039010001000d080604560903600102c00c0361010f4091442d020001e407409401004480c00280c8000c02000080e081e41001ea0b04100d580c00d89540d107170341c03400040305003060440c40141d2040f4800908004c05100500c450381e8080e184640070300c0c800101591560096800301d96481d45c03400c003e6066801070089801612041c40c051165030300d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 627295773 1250 627294523 627294533
    0xa03060e060f012319030503030108010b0a0f061b02010905120c03011a031509070306020c2103150913020301020c0d03060806010e040b15090c040501030f090b01120f050a080901110a 80
    0x280e1300c0b030414061350510340000111041c02000340011584001102d0f901e40c3c5540a0740d020700034a41105015041082c1d0115845200c54101c07800d6500540e02c8041400d0035a0050300d042245a01c140e05000c0e00540c0421a9111000020f03410b902030360042c001c8000000606007111007413007808136000c410481ca07500ca5503020904003552000c242e902c4426440301404103042240715480101180e20000d40d25080130700c045808080319024420079002d00142085011240c401120f03030012125202007095042d1030000d0505400440050450001c9030781a80480c0c226070011520043e035911a4008a41080d8980185001f81041101030002c079494031442405c2c2c180c0c00792000b00a6004100010310505a00c00c450030811002050001030303041c8001c2c6005550300500983d400641070031100d00660b8000e0043d14112640301c040460b03142c0c82c01007030a03c080ea88010403920016a0450280411010401102d6450080c0d20007907550301c400c030003d040e004003030440c1031141d0421461140810 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 627297023 1250 627295773 627295829
    0x1207140609030d0f020c18070e0916030c12020a02070509011502100513020405181006150c020d050312011401020105070f0e1c150c1407110a03060e060f01 68
    0x300c43c0381000d460a0000e01420b07400c0c035440301066a045460380703802d02410241800e01602500c503d441c2c480741c804901042c00b2300d440b421600129403601c0703070041048c070701e00c60b80c080c0e4000f880c1450300c6502410071150071010b0340c0c82541d002c00180c2c05443c05000924200d80803034010554a185094025150000a500c0c0d204000c07000024a68800008405e81c0405900780016513008004202031f1416189110200400f07001e2440c6920940d1545542494980b02d00d00c00d941048125081350b01504008440702c45046500b02c1e04403d0b200380e03820002d10100050080c041d034000e44286150b0402c0001480003081e0903000e41160b0400043c00b0301c1941201c4201002e8406260101e002c0618502041c0f20500040d480c00380b00119010404c01d104460700090070440c05290300703001c00200c0c40303401c540c0048072421078001d05408000c580f00180040b030b820000c0302000340102c044c04e9071740e03203c180440d01c1901d40202560050342c10040c0005105607000e014000100c000c6a68a101c0c082c103020300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 627298273 1250 627297023 627297043
    0x30316180509070309020907091703040509060f04021b030307120911010e040b03120c0f01060608011206140403020d0206100b040b030405070e040c1a090d031d120714060903 76
    0x10b2040300011600c0c5512903000700281d5500546011b2480c24800c400900b00c000303921500d0aa01c01d403000151840002000f100c0c12180c00070a040d0b81600d5200810181d1044507403d658090380c06c1003030088004401000c0c02c400c00d000b41c041c0d512490580c00103040101c07041d003500c0c0c1030384c80c084402c800540e10380c0d48100340800a203064407031070714440c020a0003040c0c107152140c0d1510607000c0c1078179180103039801004030f07446480541d103030004c1c0703c199030b070a80704280100f00204012400510002e41800f21042c02140038070008103a103018060000d00e0514195400d80c0107810880d80070040d69010081650010404030139401054a09603d81195004601a0103a0080c00201080c21b0010401070080940320051001246052038a880d0112140601c5017405135100700000403400c401d01c10960b08190780280900010395020f80e001c8a03031100310f605004010141e1200c2c0001c5443d0b0f442c2c00c022080d030290003481c8440c14003a80c1d0414001026901d48112002c2040000c0381e20042026000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 627299523 1250 627298273 627298279
    0x28150f120902030705130b280614040f030c0e280f09020a090509070e06100302030441060c1602012105060a050d030e0f0f090103050303161805 63
    0x1500200e00c0003071300700350440e4030043d40181d1440c500062158141d000348091482141c03502070125143d00800c2c150307c0070100394070003460611810881c00d0701070082e841001510401003450709440d903180b40c1c200c54240d0025160168a02000d114000f003401c02c140d000160701c5603492007034103411408041044903211400303005450b09294010440d468003c0c03580f1680c0140400c2c201520340400780002d0208035802c0290b441031803400a04142c2c2e007503a045c02054040d01150010700f803000c080e80650300c05001104d045255400586c020703000c0c80400c4510640e0b40780c481320a003240540f03a0007030000d80540403455800581c1480140c2200004860b01030340d0703c0c004152200340900043e0381040072140080c0705034503a04010072540465620103072140b1002c0326404d504c4d60302d034028002c40b00d440040c001c010910610821101d4644002c4801050030010700d00c0d120362402c100800c103c81c6084e40105d410b6400441480501055240c00340340b907c419290030016003101c0168000c8070965072040d140 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 627300773 1250 627299523 627299531
    0x300c0b0915010b0d090507080a290604020711060a030504110109140d050705030a0c05090c070f24090b09060906040b010e0901062607170705010e28150f12 68
    0xd049009400c440e00c00e6412500303441f80180d85500302d0303496846111007100e0420400060048003203403144060380221700305009a111f5622903062000030b522009054403085050341d0001050b507075000c010200b2075450381c1c0c040380c0d60410340380505502c05c03543c80c41814000120400d011113009030b54129103ca1040707948510490300f0341003c50811403550441600350048069000c280300c1d03c9541031080b0344050b105d1000550350501c01c0c0c0c800d80100c0d18014003102003825010086203000050114a0601c0041c14050399055a5182c0c02c40d4a0703280c045601110440400010110a00020303500c01003400203011a89003507640c0708645a814000d80c3c1c0c41c807040c0300c0031803041d180941c000e070058a2103200c0205030b1405200000e420883c02c101c6161a40308410010036141e0945607031041c00f1100c1030003400d540d42010010340e800d003408140b03250046507400c03407581a1102c00386540c171510200300f000901242040b00748806407995101008c18170211199821600303912115a06280e451440001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 627302023 1250 627300773 627300787
    0x70606080f0a060b0f0904120f03020a0909020a1107060e04051506072607081819050402070f06050c04030c08030306060d1119020d0306060201060e04300c0b0915010b 73
    0x60801c10185c1c10107908442030b0001c0204212101125611417110b41c2c40340300c10140307001000c07002e9108250110000612840701008004499009480300f45604d080c42890141100d1281d898010307603070300a1002554050f0111803505013440340350382194640c1114481c04a080c00030440f07511403010b009100884081103100040b07008045c5810f2641d180310090b0383c800d42c1e0305008a00750081a400511110740d03440c1e22507603190810300c2c0102c045040d280c00001c02d281c00100402500030003070545e5410103403912440040d01c5031145c00c0c801c8542c542e00f40e44460460802031112855504000d44035813042003482180d5440d1815a019441255004a615100e40100d4400c900880908119112501c00740040081c0c0204d030500310810241e400304800c0b41d4400049081c2c1b001c0d0700c1000100d402c45400328020824600803c26000c240c140c1010031804882c0c00001c000041280500009100389825410404a960b0480d0856041c5008114040102c9100407104c4c2041c440c48140103400610302d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 627303273 1250 627302023 627302029
    0x20a15270c05091905040f0b07030506010210050c040902070c090e0304030c0302040c120207030f0813021e0d05160807171e10020a0809060901020c030f030417030c070606080f0a060b 80
    0x100d0f51440342c00d84c0920070b07402d15241c00b034809204d43c80219040e007055000107001c240310307100e224407540d4141e00900c20f040302c107401e00c0c0040401400c48000d0b00800c2200bc104481c1a00081031000d2081c189075801c1403818554400f140c0c121701001c04250001c010400200d03c41d0220481034a804036000903c503180404c0584104010910b5114444d0000c03d0810626412130000c00b001c0384107407a600070580d00c00c07040701c5001c0b01c4820001d43c0845a1030104001c00055401c61000348009040701c41c04035280e071159464272125101e00d101081c5071070340500004c1b10600000c001800c9001c905280110b80c480070700e40707980b40030700c0c038a4011000c6803480181c010100b24498541c0f41c840001c6540d096620300c001c0c030b000e10407200c0c041d0758410b1802203200e2007014400c07928243c044401650404a120342d03280f8556101034415508c642100d8008000406030600440c0540c1000d41c00c3c1d5610700041c035140d41560002c3c0e00440050b080500344840304140400c5903000c141d4403040c0010342845030400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 627304523 1250 627303273 627303301
    0x40f170a14033601030204081f0e0f070f0603020708040612090606120308150d0f0c1d0f100f1206110c010204061101230601020a15270c0509 62
    0x10303030029044034032080e81e074440c49612002d1000f104200c00c0d030855140300015010b030301c40c51003442080d901055049050b0529803000e048095059a0f000c11a424481081c9240840c40f03640445650010241000040482095100100400c2c1029800d06980740c8a558060240d1b20a080074000005251000d0404503403108440540c020300400c40da81d1a0250101c9150809a04901141541011603400500c80d078421110920082100352603c00e41c0e914040011601c1303500300d030103400030000800c00c1040040c802080c0205904613102510705080c03102221040503000c1c1191030329182040c0111000100c809040d200d1300240003400ba4118541200104403180c40003122610101d8800c105040c103400410440304982d139940203881240700c15508807078000740c448003070440c0841200d662492103c1c003039a00400500507921411500d0316508030700510b40c8042d141c400da0b20b1006007459141c0c10300401c2c200481641ca05200d035050f83c0d80c00c0301c074002c03401828892410031000034080400408 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 627305773 1250 627304523 627304537
    0xe09041104110c100513060902060d0c030510050f011205090f070b040302041103130f0206120f0f010b040803041a040b120103030905060304023111040f170a1403 71
    0x100c20024400c41898160b282c0c3c01016039440180540001203103103081900405010b01443d0000b10010012592440010605c16100301e0304210f050208078121100c0d0312420760441d5031500c010a1b145888900d6856400d40c03a008079100e0b0002058074076060340d101e4440e060342d0148100005054403180400381ca080c0712000c440940348a440000b01b0030403020707805403003142d100b0303030b02030120315003007800001360f4003084480b406e0703107917a0b11b5a120100302400814080344d40060b1a06240c02c0e10030640440000301184c01500d078548000070300c02c1011143d01c54038014294801c0e000e05280c1040c800603142c0c1308900c2f507240d250751500d0f0605c91048800c4121401840c404009a47c0e824040050707203d406c40900c0b0682c04a054660300003400e04000003107034410343d4024006030141404e2004002900d00c003140c16110318a003610b03e40d1054800d441032140100e415207006460300d00d0a40000070001d400d40164503100c00080107811800800503294904a912954449201020052039031450089207 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 627307023 1250 627305773 627305779
    0x1020c0d03110606044215020f0c1315051807080606090603340c050c0f01020a020d1703010b0712080108060a09050a050109052505010e090411 63
    0x6050308101a000724400b2030310200601501c800e59a0319041101312001420305000080042160a0841c2d0643c0200f051607041c42c3d4603000314407000d00c035100038603905070403260f00c90383c980c0d1300440e4803501001001c80c010b040c0801000301303610b80004a8808501c00940303031941e80e01d80e403084902204206510b00900005801038804420f0102c0c0f885050304c0580d08040030902c2000421003604150040310407070700300a8211031440e2226440440c50126020008a0711900b1a44a81040c40c0c07403a05011482c280b541c0742813880202d400d01c0b505204482c2d00c023503c1140314441140d101d903004110114a160104c5c0c01110240040c140b0135040c070b0504558031000b240001c00400c00000301006004894000c05401d648081c41d0841962940420300940c0520741c0b0030000149081e8044c0c2108000c10700c90b4041d22580c010307a40c1c42909491050b501100d00382c00c501d41c8880c00003941e8255550f0344c1110a8a880c041307140400107001080c45a00c4c0c5406444110700240c1480b0b4040c5a9102030403011b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 627308273 1250 627307023 627307039
    0x60f020d0207021c0f2d0c1a03010812030c0c0708071706040c0e0606070203060a02030a0b101b0201030b030d020f25050409050a08120a050a111801020c 67
    0x1034403003000294030820381203210b2805030741045490204102c401d0000f03588040320074040c0b14652a200d07400d1a600d070251046101122408203844104c0b1031000340148281d110202031400d018290468145117103c909840c40b0500041003082c0000404a4201840003c06552a00c03810a1440c19104a00c50709140e031180120008a00d17a00041c000d00315040c010030340110341502524561943c4080e20702070016180034509208060b9007000c1981c0144000301800e2030040c41e40d02090510f80100c6640000543c08070801c00400303030a000f8041b9490040714894000c44200401070281800812101c800520701a848011640240d00c00d415465008007143c0410000319002942c40701c4e103080781c14986c0107440707a40e184440300c422001d001c0c00144542d440c42c142858140030013030201c1a4159450710071985a0070100790850020000d4078208a940b003542d1414101080648002411200e0101e1610021304803165501054272009600310044c40f52202401004078600311815510b590300840c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 627309523 1250 627308273 627308287
    0x306311505190311010e19080709020306310e0c090c13120303020f0d020901030b09060121060b0301081e1b130e0601080a110a0e0c0a03020f1c1b0516060f02 69
    0xb407c07a600040b2815501143c00c80d80c3c0300c85284003070340000e41d40c0395001942440e801511455100b0801c400c035040c510001c00c60080b2188420503902000c2c0c00080a80190040d11040d0820300070b02a40005600b040c603282c40703a150110110101c8911450110340c010f250307040c013010712a070100c1702080d880d584540d03161008200b0b0076000b94400c0002c03601180c44e02c28400110306042c452188243c3d8141c40f4440b54040741d01c9000403400c0c4001e0601c02266842d90040380c41c1054001842c041c0c101c0c0001003400300c054202e8004882005108101c4aa00602c0b402d107200c500c100019040c9401651440f44214010304460050003026001004074042c4000120b807204002441f45441805003000080c0724642c2000d003d4110054090640440780c01c0d4001260340c00034400616407e600d40c50014130f00303078140740f164010780c21284403420f8520160200300d4606000d800342c0d8814130034082404031101da43c0400030388144140522804045d1000030b1f24400e100783d540c4880502410040299541c0c91 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 627310773 1250 627309523 627309559
    0x21c03021e0301141917100c08060114040b0315030f0105010b0a0e18060402090a030b010b040e0108031204110402070c030605090d0908030306311505190311010e 71
    0x30074060500c0102104c074031a00c1602e000f0150025009034802883d000600b014405403c4400381018000b4501c1010b182a070407045500c10782004031415518014030707040c00c000041420300c0804280b02d180e182480144240b401030000c5980000701c00c8030001c6e090010101107410103101c602801701c60751804d800001c081d00080001c081c007180c29512071501800e44000c1042c0c2508070186030241e4440c81000075005d003426401400184002400488120360ba0343d01d40d40d507140c00341c004500403a800b2408100030020548140d0140a20401950900641800741910040001c10141c01da481e03188045403c2d40340c2d43d04403403400d6001610741d8551622810060701520094070820b00310311030141c4000c2964440c0da944020740f4a410007a42c03440d1106010002920501d0300d014001200d00320b0301d00d84260f056505001160075850340401c0c1300759415019000d0070800ea001e140a48034000720007918141e84078862003031341d501c54940380d82c541c41c440040b0340c94415070010b142c1200c500c490751200f5031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 627312023 1250 627310773 627310777
    0x5040507111b01201b060a081504020c0604060903021b0d0209100b0408010623101112120601080105040b010509091911040801060909030e060c1f0b011d01021c03021e 73
    0x5c000004482c1d0b150044002d020852041c1a03802c0700103911180490702d81801c005000b00040e00042001d401c00d203090000318103200c020b40f03048134616074903c9018100340d010310003a1031961107180301c9500800850081080050345000c024401d240030000105902c1049084c40060141038a095840f551142a801d0081090340640c03080120300346000d80c0c06105804c0584e1105101030069403c0c0d000121040c1c03492003c0d5152490f16000d0070100800d061020805841c43d4400d140c0c8940c030a003018000500706082c180c00c0940568280785c6020026600b2400311814503105440000250b510034070404603150b8110610318040d03050901003280001c0e5040500182d51000d402000700d1541c5081403400c860703040c1d00050100d45c8041100c449803510801900340c3c3d032034030810340b460136400c2c22074542021480360018000e103030b4403886500c039540c1c0b08103040040c070010042c10542c002e030240040d40c3c8111401810001c0003058440c001840e2003501640d1700c08030002c450516034030703d42305580d201d0313 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 627313273 1250 627312023 627312043
    0xc09021e030a0b090f04030207051203090d11041409071203020f0f0a0318080604020d03030e01050f0901061a03130314070507170303041214040e010e0105040507111b0120 75
    0x55075031200801c4882c5c001102c0e182c025a403540003020b156242c0000e0000c0311040b60f8260896000c2441294555141c2d500c1c1da1364421300c65030a4400884d054030410007212040d91854418280000412140b150700080d020203030352070320002e078802c40050301d801c030311f0801d481106003c00e0041d0200c0d2a421030001030150440b27807094966820307052645505940000345442241c20710b03070180c8041070150418528003818540203107004590400100300040c29074605803034040c0c4108141c010458080ba0078031070400074114008200d42104d61040d1458224003010707103c0d50300310b102d08c4020000c140c0641c100c0d41624501c15038003070305c45500341081500d48905e80b02d0342680604140d50809a40d01c04401c580c0318a0307000400842144504004440501036080c060a82c90010031000c2028240d02c040c81d4020301c0164160f00741c541c1848148400c0c0ca4014000105004da800b9111080308808543c20801e484403480d1115411641030048480c04021403440380050b140940c0c0010301c000103d44810a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 627314523 1250 627313273 627313279
    0x703062c0106091811060d020c0303190b15030604050619090c0314090604030c08090d080c100917031005130203060306070221030c22030c0905040c09021e030a0b 71
    0x592240c05030f071061090740034400105504900d0038180510b2501b400036110704003001100604010900b8240c51844d8030a54540482041e185445501c0450a02803030031348800a0740c001d51546c1d0300d000420b1590001404042c41240c4540000e00d650b20350340d0031030307038224920344d42c1182596844070510024404080c614002a003841142c1260b45011807445000780441001003113240e40b140c80c1122008003541d0106c4000104100d034a031559542103124039207902500e502da035142c0c050038005180c03800707441400c1001c604003a683c0700418462282540c0540a01c44825520359511801a00800d5542c0020b40d01c0b00c040b16005c25115950f60255220346000d90844450703441e0018180e80d901d0030507900e111080f810000703031301000070004003075a0440c0700554020b06002d444944441c44c80000c644911040151540c100240418a00c503500201304150040200e400d2946611040104d5806855141500019042e0040000f034038500440458115a60744900b0400203030740c0540320b03005001d44 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 627315773 1250 627314523 627314531
    0x9170f03100806010f030210230d2004062a080c01050a050c090f01020a0f05030703090e01120602250605070e0f09040b042103021b010207050703062c010609 69
    0x2d00300070000340d000c1c1039400c1c4030301c510700b0186560700704a038050b0707a00c000c18100031840802e0310196a08848020028848124060300c42401d8205082200d1255a56000c0924990804005130052600303c40580c0c41920f404075541e640460210504400c1002d0f8146140744001024140300000000e00034102c40d40c0700034400b40c0c1741e000c0c041c410307600103882ca005401400c1150b1100380c07134032010740804401c1c1030047e40d140b40b4a680321100d0350a4041c60a0710340f604002844400c1580c0304c00000040c058050001c1c600e54104188901c00c004c0c0c0084c01420654001141441812040d40841000308007002c0b62a42c10340c1c510702200508130079296070700803410520001340c01c0d02e0001030701c0d41d0303000000c0e00302c0c0d089964603100d00e0000c8401401c142c8104800c007045101b072901d84030740c00b46d031010651030140e03540351080340c00ea100f040541c044001c5030744140b00f00c400040c00481d0f100c0450750480d001042510350780f02c010320003075042c2c04185400c6c070407810b0104080906400c0300048480c201e60400c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 627317023 1250 627315773 627315779
    0x15010803130e04020a1e080a0501050906010f081c2715030c1e090b0d0e0c01050a08041203020408150613020c1f1103040506191b0309170f0310 63
    0xb8803074402618000c0d44070541c110284291a002c05000c02c20700004031800b40515561007a01c0c1c02c00443c0c0700c080d42c1030b0b51103404002803850104035690040407801800c050310341c40c2203c400e072200448140c00b000c01d00100000c1010b42d110782482e1b2080310174100100c002c041c00e88407034082c1284500c0741c24880c07490f83c4410740300d45009218021400d0b125844054560308442c0619604211182c006010700444144c0032410342c4c015030241050540c030309800205040a0b210041c940b503c240a1241001000c1142da10f055078000780c1c00f508698000c550500d4602442019400382c0519044050644142e06030007110420551250380502000e943c2c54554002c4070044009a105100448104d50700c68a107a01a081400b034000000c0761503580c1c0060501c0d44664103000c0c0317a00642d415120b40c0c0c0480c0c1072081c41c1410300d03125881048074610422460302c0900c001e008540e000d0401030141940c41c1c101c5024400302400b00b41d400300440c0d409a6862048a6030710742c0c0303a00255140005004040404 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 627318273 1250 627317023 627317039
    0x405090f04120201021c0b0604120308040c0e010612021608030901060e0a0c050405010f02160902030403110604030806012010050711070506120c0904060b1e0423031501080313 77
    0x40300d1100c000680ca040304801b002da1900505128005150401e404000c0000da0155180405074200c0c42270740d45000c1401c0605000c09040394540082900c00012001000300d180c03c1040c80a540c12000e0015840c1c0140f103143c003c50980f031141c094040b410000403c0301551043d80802e0070f0f109090507008540c1c650100da881240c014010b0000810010003091085c1c0d030240e40d4480d000c804501c1100c88040311441d8004503803101c0c0c1d2048400b6a000300c10f0008051308101400b8800303818a000b408a0728241d2070007001c2d400b014220b64107022401c100004004811071011240d030680380c0413a04504520428940100000ca8205001600400d00d45111050120b44e00040b14030090945080450441c00400c4010740541820910790040003120301c140c440c1d008480042084c148c00c40e848500082c254020039222150844d40402c08200901400700442d10b9241196030002100b40490250404680741c1035202c01c491003e1200c20000040841c0b000000b00740d0480700316a0000400d68030816 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 627319523 1250 627318273 627318277
    0xc0709060b16170d09020103051e15030120041409012409170d02010501090b0a03110d020306040f29070804030203090d0303090c0806040201050a050a050405090f0412020102 76
    0x404000c44400c0240b000d98551100c181045180102c6604070700755520340c030500041c1d200040c040000e98039210103a0035580c051260344d921400b000c0c050124801c0510828040510040c842e22075101c44200408080d2401d500a00505c1c802d50903000c4040d006105202007600940304040c140e902da0405811141804002c85040b02c160b035500100d0100740480080400b0601c407180c40800c481448001209040d000c038000e0040140005440507000c40c0100030f007500d805030000040c1c80d00700080200c46448091071a030071241c00400e249400d620201c000f4000d00c0a101001c0c8d030520485040c0004c2c0010b1260030f5541601c03445400503a1220002085036078000c40314800807100305000002c100764002c0400c254421301c2803040c0c0c3e190004400c0000e400c0f110420040d000a65a02c1c1950100710782c100100f8007030480300006203d80d00e00359000070150b1258184000402c800031514421040c0110161409440003c040240902d804050b40c2c0c142402140c098540902003610462003d00601c2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 627320773 1250 627319523 627319529
    0xe0108010612110411040603050f0708060d0b09030f0721031a1017101e08120a11030d050f1302150a0c060c030204080f0303060310180501110c070906 66
    0x10b00302c0311903440e0351154401c1520b802100c503049900c601c1c1c0c51545040103402003000d000151030000e10781c14401c02c0210303a0340c80140254144010350007404419541c8010406045500448070011130fa60480c859046001396010604901c101040c2c54003080000c82c9000ca0358015a40d090b820340b00024011019291003003105401c629000740200300f02d0802c400c08030826001400d1001c000600a51001070700442268030405040c13840b1018814100c0c9411814011814000c2c0c0c5001d044c1420022500c59804e111030140071080010b4409859001e06200020300f0808000d41c1d44910700c2507184009090104c906040c1c9176560000078000015800a00a01c180c0280101100304080000601d5940c41050b00d90184010000c0c504000341c001d001d200000e0b07119540160310f47d80780030040d51924158400c844c8503a0028400c00c20300703480004015082042ca50804114407180010100360001840000b034540d5007024112411030140c0c00042a0103021982203424283e03640d2400030440b0340f40c1c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 627322023 1250 627320773 627320789
    0x327030d03320a0f0209031204050a1a0f25110405011e051005090604030c0608010803070b060f0406170a1b180507111f0c111e031e040e01080106 64
    0x2c0481c0f8038800302e074401c900130710310904010314001400000030720317060390348401e480090030004042c0650308203459800f0090461628000134905503210102c89400341500c2c0203050f00011402000c80e4140f040a5224502e103041c1c89000000e00b4244a041a1441008240110704100000071542d5500890031401c0b20300480302c0948a00f0b0a0400c20642c04034900f1000b003050078404d40b10b5075988c0074001c01c000d40c410741901035071a1402c4e40c080c00b002c0059200f041550414060340000c100d085454550020003201c292040080700000070700240340ca0b0f0030090341d1104800e01d4101e010070000702110958050341d041e4503a02016403141d48407649601500075041c2045c10403440c0c105840d0059500955541001004504c04022051a1250740d0b10f074500400150b04068aa00c0c0c6107101c0d51020300c2051600d2526000745129260380e030040c40c1014921400603811500000105100790380d184290481e24070300d420306d440b40c0554150018001d10180c090301c1000003903207050511880c3d040300d240d6 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 627323273 1250 627322023 627322121
    0x109140402011b05071a04050a0905040209040f150f050601031104080c0d0609050d050d110a0f0c020111030a11070801050f19020405060417060a0506030327030d03 72
    0xc96075100c00f900528408451034890f005003c03551403403c80f100314a0743d0300000301030b0700c2c1c51504040080765005607100d01041403a04084c0320141c0c07500e0300400e9005810a20a510310040d602d08100c1502e442c4401e021002c0c94500d10780030510f2a81c003c40d000351005d9a0a00001101d450511514032a6124049466010260070762007130a0184003010010f0040000299103109134840c142044020541c51000a40018a840500c18907204107060000170307001240c10006a540054001041c00e1804001e11501d005070204680c443c80707001d990721244c031007076070346451020310060b00d4801e50450b500350f81e0140300c4020540ca401407140620401001c0700241071900c40c4644414151014030084401e00d408000100300794840c6001000100103018200c2c06000440010034184840034005500b15828042404121343d0b0000588030f042003000000004201808250700510f45a10f140a8040c0200c010503c031070342d050751201c80352800da41101c1c400041d00006c03044118a038015441c400c1500 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 627324523 1250 627323273 627323297
    0x7050f0f0d110a080d150b070b01030221010e16350a06020c100f050403230408010e03210c030118061805060f0a050105030415140c03010914040201 65
    0xca00400c1c8522000d04090311014111500d07500c03102e520501d0b05241e00f1b074072214209845d555001444000b8501481c401c0d041600b55916401d40300e10600c0007a228041d046084e100d0000c481d80c07a0031540040c20001c06c981e51400390311a8403a100c03601d00d1000c1010b0008001038003181100100003283d400d00b01c140e680c01e07905ca2045100c81e4003400186c0c0900c10308010704001174a51000346030045289004200203c113902c44070342514025144401d0481c00e03c001d00c000281c01508c6407000541400c1c00c032003011140c015404c014050b6038044190396081c215408a9520048001e001035004600e080403407240e0b28040209850f010b507903651100008200420042ca007001110850f0210340001081150f9207206011a0710345c000072900c0b201ea510014000b040c50440d401000045041e034422601a240400203451400020409002090140907040c0c03820300701c4c0c1c000d0040000d5010505440e040506100c505500240035042c101842d209005400420001d003107403051307605944035012684 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 627325773 1250 627324523 627324527
    0x90c0a090e101a090702010b03011a060d09110406030b01080c1f0503060a090c020309010e120d080c12090a060e0a15020703030b030708030702040b06040f0b070f120507050f0f0d 78
    0xb10582102d01614030300351149100d0341c1ca41c10300030702031817599001042c410103940c105800c41307000e0210941ca280c18044201402c0e100c0d00140e4400c9481190006515895400c20b50030f4003c08460407a44545041c6000c005c0142c03050403103050341c0640080b548001c031204240070382002a003520000c88103c00c40b000c5175052281008560141c006800765080c19917809a400503180d00c030950740b01582001c40c003641d6950f03001240b40c8568100b1520040820003800700c4075201d440100139101040468000550140060802ca50721320045014801300344ca480450f032a124050444121466030038081e0102c40620000342e04802d4507008904184040c01c2c1d005000c0007984110b004400781600e543c0100c25039034041c0710340c0c001441c0c284090b40d81c6407001d2040000300c0314081e000610454003880180140308142040340d0076644c0c01e8040a6595502c3d0500020b400c1ca0998028002003131102e8481c069940440034200302441401221200c0300041d44140d10350403011a504500d07800303280191103040c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 627327023 1250 627325773 627325781
    0x7030e240a18170c03070e0109110708030f040312060302060f16020a0323070e0601030209060408070b2a060f1302030f0303011a0f07060207060212090c0a090e10 71
    0x10600b0a000e2201068a1203200b0001507400391110304070104039556040c909001c16441010120050044070741010300300c40002c101801031a9800b5610b020800210140c030f13044a50150304451102c0d203d103020602101400300842c1e0440001d00b4251000e610010140149010340781d00500d000c2c14903002407440d100c2a009855668802e21941800708050380769528241c0285014080e180030090305074a00c46240144986100074070750101c1d17810011522617441c815041002480c1c090703603c01401c0700040f80b82c000c60300421142e0143c980001003c041920090040c014500d0310f041ea00140d4030401044801038020310011604660002111030000e030410030741c0300c0c0d0a1140f4103132142c55600442d191001404607040554800030041c00507494120000329007924800b07003107241108202422109004e8402c000b060240c01003012001c0104d690107a81a0500c09a04803105151001c007060fa991a020310090103018240701c0403680d0b14807800345c055030086c40001803440c1104500124010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 627328273 1250 627327023 627327037
    0x50f030f0709031209170703050a1b24020d050702061b1e28021005070302010609020a030f360611121f031208090106031707030e24 58
    0x440000200002da0300300c2e2a039039030010a5035000c117028240078903140d540f10b603040b40c0300340c2d075000c440204002400024406003070b90303004281040e400d040105c088600780d02074210048015400c0f40c20b0112015400511711a1025a42112240030f40d6420a40d071300e100f030303040194100b8130030040b014005015070440f1142d00d040f02c0460310680b846261084034101d1110030314001e900031468003589017000b0341c1a0b200b5040091450104103465900145068120380c1c1c152042c003a0100c0c040c0140341c001c1d40180c0080603520019555040000e80013402441c0486540b0149850306d1141c241d0603a00c01c0b44030203e00b503840c920083c200d011040c00f041c407107100d22040b03501d07071344039080c50385400b00000c003500c0c8089160010010320709000d4400e03012882d408504080d0038000f000c0400100b0b110710341a9050310301600f4186820b44500107900c4c050005a040980142e1030500d0340701a426180707005000c0c4901070b83d502c0d003802143e9000c022a1900c203084c141d60301d5a8540502c146440d0000041540c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 627329523 1250 627328273 627328277
    0x40c0501110a0803010906140603010503150c1603090512010b010207180b1e3a061805030307090e130201050f1b01061d04120e190306020a020d050f030f07 68
    0x1540da0f59900c0c0140c3d109800007010961030320410001c001904440122101044908904542c1040c01190b41c441c90b242c108850306090030049083d1200b0b44088aa04c00250341c40304a520443d414041c2105500384030b40381c00b0300b0a0208100d003103801071141e03620070001640688203061034000714102d208505501070890319540c5034848543c3e592000ca900e91110320050000120725084208201c0307090400304590714a0012004c000355140f044400c2000b140800c0716030005001e5800d01c07400030044000c4d04041c02044a030140e00307004c1e00101851150382960b41d40d03015540c44a1070148080e100f69045000c0d005201c845600541c002c9010700216190000c0d414140040c61003c1d0000340e0b0b640c18614256592031409000e41e840491240f142944031444240450400e0f0b40c4200818504d090f4a10801015281010b816035503500c482003c0301e00083d604e441251070341000300c0254442084c10000d84140d602d44e4241601820554144c2800480002d0175a92601440110000e0040a10341 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 627330773 1250 627329523 627329533
    0x15010e0612030301090504030e0306070c0f11040f2c0309040903020102190c06050f0f0a050612120d1d03070809040f06150305060a05031f0b1c0b010509040c050111 72
    0x6401c407001c001650003440350140100c0d10741002d060107802d4241c1401c2441c041c1d0415410090302c0d40d001001e1241107540803808404103942e60404055018160304003590050801e4500745000c04140c10030b1035034a414009440030204429119141203100c9610090203404c00c0c080c0306010b203010361101c1c55145c00303400007628107104060007140342604080d10001142400c50310100744049445400e92018484c5882e207200d08083d000c1c1e20b40700340000c001c0320181e5140c0000400d40e89495001801c4142c0304000c070340000c02400b00040c544c0d0806440d403810300f450311b02da0b041020f1041d00d890a00201c104007030742c50300710162126030566018011280c0c0041d106c08003030140d00d0f05441000024001080c100c40f240c0c1c00000d0050030345002500b414030a6108100130f0040e0354000c05d0030a0716407030481c5001c88000c0c2c020684c5000c1d00119110343d600075a646000032541c03002024150b03489229203600c0009a8a81e010060340380c209803009062614101424031865005000c280c100ea4112002c0f50 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 627332023 1250 627330773 627330799
    0xa1803140403051507030c0207140d020a1a0c0c03070e042607030804150c0f0f02120d05010e0717060418050a080c070b0913090819030b01080915010e06 67
    0x1070b01c1e0004c40b105101202c00c0500030481c00d04d0707040c031a10020400d40c0c80981041460600c0d0240e50136144480a803080c4c18940440b0215039401e84580001d04045444010700d00b02d2965281c8260131084c10395055019510310f684040c5400308030982900c4d02c00c0c80041e46500c2e551282148a1750105101e420200f01540440ea02443d410103444d406110ba03071541c1907441c1500d4255044d80484030104080750400290031030307003500310100007074940c5249004400c441000508031701c0c0020480111429600c00101d1070030090b02500050305880d040d201c001d0341a02c0c0d4000031208406c4001a0354607a105031008503400c0d00c0c15401200d00007131140c000c070f00f940c401030b11480d080000112048030382c100c0001d020751641005228510040c80700865030340c2061104c80204184c1c0c1e01030030b5050416699101d440c0100030020003035a0352843d07400c0f095004c11ba42004040c00905020342150b01003041200082c808030740c0048c0c1800010003064015010742d01e8802c01c29040000030f0400360b48000d00809103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 627333273 1250 627332023 627332033
    0x30804050f030f09010e12060a0f0b0411071a0f010e04030e030d030603020102010b060702090109020903011b030207030e150a0309030302090d050a0b0f220602071502120a1803140403 80
    0xf4100a11084000680e244251070001d002035140c814807030b00856400d40c00407445000451542e50005044a0114a06410b219940c004040b100c012503401443d02034808040007441e070140254034450300c0301c400200840c1c42c2549030008125514001009180c005000340503407030160940061190804c034000310f0200780083d04041054ac1c05400103603484408100307543c3d0900640d44074480907a80c4a00d40140e94011450800d014040e45454980000d02c038541504d00f584030303a04c51181c00c4051419020045030080295001c0101540001c4503041050316610b4181811802450101212841c1620716001134018005c00e040c16018942c3c20f1081000343d44401c0c080714080c5200c1c0700941540540e03480d00307246100c00542141031480402040040e4042070307030440c4012071003405146800048601c0d14001038418040b00400b0065603074484400307107200380c016100361440890381c10011394550072800211241c08038240200310030303502c038440820302861018801c0d03464040030503e0103480b44c941e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 627334523 1250 627333273 627333277
    0x5060304030e1c03170114061605190b0403020105090303150910090203010902090112051614041a270907030c050c0601080309120109020d0210050706060602070609090207020904030804050f03 84
    0x20980106117240403082c100300000100c83d01520400808429480e03207240070a0450140f03040c8055400e044891810910004100d1035082c5020110034880106ca640350004201c10180c5045001d07608120100e40b01071804000e80c3c0c4110030125141040d00c07100410010850000b414000b150155581c0109100d02d003400154040c000011015035540c800c0301c00148903e01d4240b80d8495289000c05206400c0790a0a2143c111140c51070000d18100e03c0c01d1001c03441c0d01c140e600045001c0d525101c1424200d4009002e002c1c0240e07055602160a081e00c00c00120542c040460f1540c020800000034500034040d034004692a5142d213407040c100b40745c80c503049107455800e8200b80515031001c40e0000386440d1200c040340307094480304001d20102c0420b13804201800c6038004003e118550054444c02080e204400341c0e0345164000b9001d1040c940d03201e80c0651651124000e8900013040940c01054061150084601c039940c0544845019a1540c42c00c0322070a42c042e0040328240140419142c10340b1003080 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 627335773 1250 627334523 627334579
    0x6010806060126270a020a0e0c0c0a0c090e16090e2d2b1b1e02010e060c12130b040803031f06080a0f0204050406030b0a060b0405060304030e 62
    0x8031805600c52140c483e52810004d500032032150780c8183c8500c07006803030381c04010085401c0f10440b040e080c1c0b074a541c581d03658000c0301d81301062403142c400b1100c24032180100c410308940100c00d08000c03450707061400c0380e110060310b00d05045030f0406a01c20004184550b100f5810b155494088d2801a5004d911800c500602140d1181440011401102d0703180302c00c0c8007030a6110a900d10034a8040300e203400751003021014030b40c0541400100d50481d0419001c062908442580c040018141c40d5407a0944d6541c5940b003000581c0011b140b1440311600342041e504a41c03c040d03001c40105000101c01d000c41140d54495140d074103021070460400168100000b016001914102000c0c6480303240500c002c40c404a90058001d0306401c1e040410006c054006000a82100705030001007900003a0b01784917402303031066502203904146021400018440005a820f0003403584000c2030091503034a82c1c0701c400714000c0d8051294090010004500001d0045110640e1300380c002d8900c0d2488004101619040e00e4094 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 627337023 1250 627335773 627335791
    0x52202030c181b090321040e0f04060c080c04030b060f031e0c240304170408070503101416030e120c0d03090507051e030316050d0206010806060126 65
    0x8802d10034031443d1010314400c41c845a10015040c5002c410000741d07a541030140b9000045400144581c84200641c02c46002d008220000c0e0b0f00c0b42000c00748410740300c604903003d90301c0b1458218a5064980b0035404180942451001941024103507120041000e60152030707a0b91041c11501604141d0701e05100701c04200200100d0886241c01c9580840d05150401d4201889a4100030300070005d9040e0841880b0700b030548641c40e544035510b910b4822104040c0029142c15541c0c04100040c804800088420039602300341d017070300d80c54080e1320b1070403050702d8654104404040c1c4840000701c1a1290a1080130140024a800310f282c001d80205241000000128040d01180001e541d485051041195206985507031401300842c01040d1600c80c1c4401040c010213214a1030b000d43e27030319821760005800b88402c8004058076034503c61407900c2d0b00b014421003000c554601491a19100d2a0700100e40c090407560148041c0006590343d41c01102c21803580c01601c40e0400d18402c0c0d104078042208807041c8200140 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 627338129 1106 627337023 627337069
    0xe0f010b090d1b1503020403170913051311030d020c060307030b090a050601030b0a0308030705070812040c0f090204051c0c0b13090f052202030c 64
    0xc4001810a0520000f040e032140081c0070500c00b110540c04c0c962808505100c0c0560580c0282d12001d813000e282c400d0b20202020702d5400420304544003c0201491a5100b03c41d0f80c101c44040e01c6200790802071f07d14410401c402d480f910006041b088000381500c2c402c1010095982846902ea00d018200220201e60701600981010032580d2001b0700c1010070b4a05414414010034007299460300180c10007411081c00e0401c507a82a00392500010320522b5662a5901541d0541c1b003c107049a00550800a4140c400762280c0820300440c070801040c1403441c90000036403407001c07654101084991041101700f207242da40d2000001000b1268800902c2e4521501341140c1804141d400150240710000e20825075040060390031083c0d0f00c1c0c0d52401c0020304401411102103500849011541351030040143c1d41444005a0361b42c070b030a02c02012030303482c960032401103045a200e10480040190030b03 = true := by decide +kernel

theorem cover : BRFrame.Cov 627158273 627338129 := by
  have h0 := BRFrame.cov_init 627158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 627158273 ≤ n) (h2 : n < 627338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
