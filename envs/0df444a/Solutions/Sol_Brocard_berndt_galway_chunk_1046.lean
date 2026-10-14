-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1046
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:59:37.429735+00:00
-- url     : https://prove2.me/submissions/57ee905c-e5db-422b-b7b0-e46c9169848f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 187949640 ≤ n < 188129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 187950890 1250 187949640 187949647
    0x60703020702011403070819020d0c0806010216030f140f10060302040b0612010317070b1311100525080d14010909020f0603090a1217060a030503030a091502 69
    0x126019402400e125100fa00ca02e860000640d661181c1130000710780c100007283d103100c00614805038004080c40701101840c0010700308030301d046040c030454a00710b01100205038100c0500450b07603010845040d081c0b884c140340e060040d0542ea51148401c1c07907100c0080401e40ca03c481c00d038508205000c00c244801e00141100e4041e0b1b8040b9100c0c014000300e20013a0300961030140304030704506040342259500e41c2032508101842e482d40c3d0b03962001540c10003080301440420310030840000e03d4035480c18094000000d0f190b544403000d0030709220307125000c1c0c54641304410807d07050140316008410b4030556028003030111605c40d0080f2400003000b0343c808001700502c500045080c641c03201544000201f1070896042c20051f80c036410210211009c10802952001c2d51402c1302c01286460401142d00110200542d08400095507c41c1a0781480341401d4010916000554030302500709852035500000464421180ca0302d10b07110300c1d44074800644209a801d89a901610500001d5800d032244007038200411581c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 187952140 1250 187950890 187950901
    0xc0308090105090312130e280f020d0203060406270504030c0b01030501020c010501052b0215030f0708060f0105030a090201140a050405011107031119090504080405091e070c03030e06 80
    0x1c190701420900034401b40801001c80c08a442001d59071141812880d20a40c500ca492003501004252111411080da2a010b4a0315129158009041201014140541c60342444010001600c1c2c42e0b410039400400d0224a1210b9820350400b84610b5042c3d00c01d0000c1c0c661600d080844150880c000c01604c0695500000801c000056000301060140300c0020015a626501040800715044114401c400c0191001e06056422114508001440189a10032428010380e00a00d550401c46004c00031440c82001c2100c00d581024200c1d0b484030007154164101200d56002810a0101601426000d83d540003c1011a405100c1d208940044080d03450f443d00c0c00310000422683c45070181900003090b00d42c51450303101000480600760380d4440d0024012030310603010300101d0714924140d68280c444030800001c1d4106a881094080ca01885082e0303070f20713803e20040c0f0401031805010f51941c2042e041e0034542400e00611407a4201c075240c50070700140480c1d070408401910580c0014600e074082c441c180031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 187953390 1250 187952140 187952173
    0x3040605030a050f1501030c02030d060603140c0301051c060b090405061b090d06050601120204060e100e1008070e03011407090e0c09010e01090e2806030c03080901050903 75
    0x5100380038441082c0029079800710701a13485881a1070b076216003490400343c28070a41c007a070850700c01e10350180f040f242044d0801d42031900395440c660040700401c0c2d03200b51381501002c6200c41680e005c1c250f8070005140d03501d004003040720841041804603000100181c03c2c010404240c01550903001e005105104608280c14025164a07003580c4248003013040790b11301d000ca28600016100082d0b40100341a0303101d0419102c420140034010003450400c003c405035030129030140c0c4080d10290082e5690300f038490704100d06118802d440c8d6841042440060402e00440e942c60401a440040f200d10b01204a501c1d003034001d84400015a00c05030b45035091480020b480941111034a22074005d40c0c0d1090142c550710b003400b41740d1001c1503a00500303e00b020050240554025039440804080600d020f0004a40c2da400e0040e44401c2980c501c80d00c00551010740d84400c52024485008038001142086100e01d141c0e10001d00c040d0034030000380030344804100c9141c203a0084042d54200d10014007600e140000306119407 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 187954640 1250 187953390 187953397
    0x90306100e070f2001090c0b04030c09061512110c06060a05040c090909031e020607030b0102010209031015031b0e0a090308071b080a02030a1205040b0f0c04050303040605 75
    0xa850740180040082d00441c0300e809800d07100c4989460300c81e41c0c0c400403921948081d0841c806015030707648418002c00080c05065456008000511403507440307034254a02000929000c0d0701000320b09017130407020710401039218a0035505141c541040e20084c40e0001c10710028110f4002c40e9010080b000c24603040010022489074802c91045440c540c0050700d5000300811603850405010004010701070a01c1100413507841416424000e007440e0400070006000f6030403400d4801001001a00083c2c2400030b081d401d80a2050b0540e024002541840e4060010941e10741d506d085952649888140740c25091502e5120071000c0c60300400c80001c4080d5070242107000c00010700c102240a201e83c400102190030070b10071001d4607070f80f654421f07081c2e171130b503e00484103002039050045000b141c2c840d4100019044da0010400142c2ca5009951100302c80800070300b8122004518011a5040604000024500800d41a44001e0000d00098191100c0401084c1c03809203070815a0076200000f40412503d4102014 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 187955890 1250 187954640 187954649
    0x905031902010e030613080a0c05030a03020c011b080a1a0d0c0501020706080408030a02180405011e080111040e07020a0c030507030606240503060310090b0901050c130501031109030610 81
    0x80303d000f00031007402e055032000d089403014140840c8600440004070068001e20100b00d03140703010b0302c00d0b200d02d03100d941c1543d11200d01080800c0d80020350700b220900a014503021040540302c403020311b4010344805088480d0050050020503a00e2122040c1c20294214061000a014044540b078540b00e15207030008140364082c0a000d4810104009416841065164401d0781d00ca07100c0790071034032641c0051029400a04481c028441d1403d152070103504c85212707250003403104c2c0c141c1c4120b1043c0c400e00280454105d410105185c2d0403d64100d4030f04100c03000304d9003200e136419204031441d56194004c905240118000800c05e0b000e444000040c808001444c00c141e03405460104815a640e851341070310440781916210742e18824049003840c0500543c040c5034844c070054199042c100c46c401004c0c00315030b0b80d1103040360401c0641040c068180d10034840c19521080e0b00303c0d120310388111514214085c400512900e8101511400c3d003081c40c030000e8060700c00c0b540e8080e0450b01c00d8100124507203080030301d0340078 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 187957140 1250 187955890 187955897
    0x50a0c060806150f0904060905040506010311060c03040e06150d060f1409040210090503030a02011a0f0102120304030314090a11100e1c0206070302030309060f010e0f0403090503190201 81
    0x414403524040c64240b00f007000b4603007010f180a40d506100d141c26001220f0310f45e8010340d43c40c40041c043d9424010248240c0c80343d0041d100d158118a0b050840c6c0b03040840c00e500034603041c030000714403650001c221001d603000b1708880c108955404002880010001400704284180490780c200c03e0400d680000041d903203142c0c07450708141d8540c156004045444540035a0100165000c2805070900c440c605000c80400e103402c0c0c0c0354584070004030b841c5030300404010005031343d1403040c60600c42c1e00c011440e40d80041266031110740003240300003e40c1c40c030058280c4d60752102d0000c081400c00d80203038840396450380030080b007130903130314000303240d42d8403500c00680540712078100070500403041c03825018001d40080c0e16200d011100c00064240103007250054074103e9096010844040540d0f60f0390041c04449202c1c2e402140e40c2e107404955a4140000600000c00d407071707050401400580c00322903800349d0000700b01c0b0486405640d03d090031a4020020b500603034060082c100c1c0812003c800b002141c0c065030007a207 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 187958390 1250 187957140 187957157
    0x52d01050a050d0c020c1e0109140906060c011404060c020f060c0406030b040e07080109150606081311040e030a111203010b072a090c0c0f0204020d0603050a0c06 71
    0x5503014401c0c0c00444000072010402140c400040da0704c1045442414411207080d40e105402040d03408020703400070070007404242980d030b000f580c2c4110800e0140a462041980d0102c1d040040399200b513020300320900c10580807443c18210b1074254880d405405a1301d0f138107552400c0030f08105000700040d207160310040c05250001040792b080094654020000e815105182510b8032170102d00405900c90400d61007503c500a909841c1010094000940740400001400455501c2c1c600410400d01c004800070b00c0c10000100001c83e00004680c2d030040c0d001010110141d21071810446244080e072001c0e40c401d141c1f102c0c004e0540400000750a1610940e11582132043e007051032a42d0b03c0c0c15082d80440752003001c20040c42017207030680c00751420b148654544400e80012403244440380c03200c110301001d000c030450020403821055008583c030040c140e0511000c020001c1e1984006003080742e50103030040f500014a03e204180690011004680207020349290003042c3c0780c1458800e00c9071056400040004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 187959640 1250 187958390 187958479
    0x301030b13030f0f1106160306120818060408010c08071b0228030510020c0c061809060303041809020f180711010636020306010e0f030705 61
    0x11480301d450341d0542c4030b06880c14841081281c4540b2506400c0e000c010024254005044041010502542c203800f0209010021190f001302100c0f610741c040502549843c1451303001c10300300c4046800c0c200c40d40e18040c0d809042c0c400413480764402c0ba4410701c00d561801c0403440f03400f50f00c82d1401d401000140d480000c442401d04240140c40c5601002035441503041401d020f180e07003220500100d0b910405400703200e60b0380c0c9031201ca09000110074642485a000030380c07249200c100b0b01403000d14110485041d4202800741e000c0d001030551482d040d9029110010119a0540d01017082d500100703600040d60100104a49004000d0080800128000c0c0c90059040726149005541041d000500d10308454099032079240403940d00318155805000e555135840b0114981c085001c603c08140d2402500d440e00010805024070350604902114815910600901190780c0c2e0110059010400403101900305103016030020b4100710165000c1c135400714031040300100701108128a41c14010355440c142c5d01c0c85184 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 187960890 1250 187959640 187959661
    0x30b0a050606090a06080604090f0f0309081507080901061e05040612030c0206070614040b01051f0504050d020a0b07061d0109050a06090f1203270507060f0203130b0301030b 76
    0xb0f00c100300e640481c91060601c030b0544602e0301c1c00d901c400010004543c40340540c5a10302030265000c0d09880c1a80681c5c0d8220605401618450061601c1d00c0200041c500b4041c080c5594030001e0406400c100c1d951022805c0201d0035000311000c0c00c9140f1003a90850851600841a03007141d10070035001d141088400039032a10781c2c50300c40d50010740603120202c1071903099081003030710b9014a000302c0f8419a20b080002844142c1c09080b441280300704145a010750415041014000d08440103d00d5038103100205c0aa0940c00030555003102c40aa4805158683c2840000d80080f2150403d5082d600007140310b0302445000c1d006000074245030f101c0e0030001000401440c0c00c0c3c4081407000f5007580d02003255200003a81c158000c0d0070480c00f4040c0d0f483e409103940d8031071040b0000703280b03401c000a1f00c4c0d403e040f4900d8901c0c1446411003100c0c40c000007426035507940e41c640b50401882a1820300c410015005107250087c001c80d41184d01740c1021040d00768844942d02c1c0f8035002804152400f210b072100003a0000070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 187962140 1250 187960890 187960897
    0x105010914031002130807090f1103060f090c04092405010c0b04022202160201090906030c1a0f0403081e04140f01051b01061403030a140c0115030b0a050606 69
    0x4002c0e000d000c40c1074003440014040d601c5800240d0010b0b22403500011079203020f0040d08080c0202c214041100e0182c1050f03402910388801e8020111541081803080c03a5071000c0e428104507400f500d080c9210365a020280d42d06010340e612000074139040c80f81c001c00c42400c0100640350720500f200d512060300d4460004683c03211400000601c1c0b500c074980485c0c050328020034000c803070307010b1003400d030403000c014041d0401640c004803502551a00e0582540c0119a080b0b121070000d0400d142c0200f00851650f09d030480c2c82d150a104154400c940860f02401c0d5060794030032188901551056181d0b5160b44c1c0c600030886502954200c0c0f010f1f142000700451005006c41290111001000b001442e0b8107128104000640080001c13414002c04004034440c001086a010440c030b48580b00008000c1d29201070860340c5140c54889500c80d400c10050308441070b401c0022501608100504541c480c511000860300410303d0720031034410607070407040010400c13a00c035a680d44038640e24141071100707888403000c0c45550301 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 187963390 1250 187962140 187962179
    0x606090315092409140a06140601050a0305060607020901080a060e010c0906051c0501091d01060506301015211107020405010914010b03100303080403051306020601050109 75
    0x70000c020310f041c0008074410580c00e05000c02c0d0000341d03402e4255502c107521590000140800e0b04001804402e0000718440c10000d2080a6a00f01c050302c0d105000920034421000c0030001d055848000c030700070352240004d50703003c103a000d0802000ca58590382610307500d00c07559004030340d010b04000c00c05607450ba041c0a82000ba0b0003545034094414100b07041035a4903080004000c54048054072000d03100e00590042d18000d000c0700100090a40344441d81d11400c861b54240c98589070f0401c107040250392510f4003116a04071490300440c00b210710142d8100d00003503010f540801500d01410a21000000704807460045800040b0840341844644500355196107200c00d66a4200810340024800385007907400c14070519981c01640c500d00f0003180d00040072114280c2264090968074550f02c04002e00e006001c40c090000c2e50030842c198580f545060300e414000340401420004410003090400d4007035001e881c0348900103d00241c00b540c454400954481c02441aa80000c82c0c00c600000c000002c0070b0440d0004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 187964640 1250 187963390 187963403
    0xf0f031602010c0228050f040e060402090612120a0f02010504030905060a0917101113030206070804080303071101060623090f060c010c030518190312060609031509 72
    0x5011600199180c2600d50b4060381c0040898815494030107610031284450540fa05e05960181c3c14003040c840400b850f004441d0180703140c00707000c3c0d400c4000003a00c5a4400d5046601c6245030b42c5800200703551820054900500384a062240b00a4290500140250025079902c980302c00040940c220300360b034004c0c4d0b00500442c039007113401d000c1400c15200038004515242060758a040e80e9082c040a9400000820380054001c02500380c01121640078445140b8030b00c030726590502c4050002000310000e80d1000a120310000140c1d030b03040044140603a001030103401c05680c1c89180c0008060038083c0502c1e002d0516500e001c0d00030540d280240c0da04141c40030f503284070840c1d82b4000110100150700690410340e01008070480c002d810340e540383c01016040f040d0800802c0c0081d0245000e02070f108007805440a96420001c84e0740da18000086250031a161182e034190134003254201520032941641da0f00743c0580c20510081401a00b28402d442241d21a40c1c1455456513204001030407200701c0e12004054 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 187965890 1250 187964640 187964677
    0xb0c0102090928090c0816050901090c02030f0a09030f0b15100c02120f1204030b070f0c020609040b09010f0611010216020d08130321021f0c1803050f0f03 68
    0x40f6400b0351110a140748182e0104c02103d80380d51400d441d2680040c41d44500740c43c8000248070301e0070102841030060240e904e050007250310030300d006912401141c00c03d4030304110102c1c101d06001d1044002e68000c58010500fa405a82c89043c03070200b4110803243c1038011054510030a007641000c07043d01401d607005503109192492070350f08201e0090240d20741400c003445800300d4440441d8050140380300402c0b001e000c3d40d030b84501d14030304038250b81402020b034400c0c0b1814030134510707a141c2c00400e1031071400d074125403441d503500d01400010001d00461071002d4024000c2400428103403400c9144d2015140e00c0c0d102c3c840080da900340d10600342e1058060300280040b8500040c3c2c0181041c0301118516480f841d90366081c160907585800c42021184c0c019209250461440000800c000c2e4216040b03807181d10252481c2070301c8034109401241e1242000070150f6490000c504a517110747d072601d4450ac0a01c0020528507943d00f0f1140d9a6003922101c2c2056015004032006004400130403605c034076900b41a030940 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 187967140 1250 187965890 187965961
    0x91203020d14070207140604051f021b010207050d210e19180b0303040e0c070c0e04051e01060b04090204060201180b01060e0112241706010b0c01060b0c01020909 71
    0x6c100c2603603190365003242045c40301003120754402c090500b851420300b0800c507144011000080c605211445181004c003111081c81c40e407664041111420383e40c059400505c00c2480c1d1030018100505000380b07281141118442403210b5a0191250700e240408841c1407107101d8042c02c4184c24000240300d07059415103881894805181503810921181d50010181ea0405989200000d0520303011904070800302c030001a40303410001120b441c0000750003c880440724625040d0744032a9100c0c2400c15015074100002c1d2802c0003480250411b10103080800200c5031a06e95235542c00010350400e0041c180554200f10403040e405105d035070046c3c2643e801407081d540e5030746800030503075008842110007410030802214075003d8030b01c0c1d402654004600003004202004400400e1000b0307503da81c00c800c50ba060a8045403951140000301581581c001a41141e07a038a80b480c4141d006007800e03071005000b100040b422071040141035000d48005a4180c410204d25078030141642c00140c0c00c03940a00c41a00810101039 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 187968390 1250 187967140 187967159
    0x31101110f03150105040f0b070b1003020607020d05010b0d0311010605010f0918112b0b100318020909030d150509070c030e040614011b02010806090703091203020d14070207 76
    0x52000418141189007517207e040080394030602c0d40080d1560b1400280081c104094402003a5106031b101c4005403c050030760b80054000d21800001910486407594400b090020a5018180040000f40041e0f1810754628000c0c0680d94046419103565103001000a155400b94070031103c0103d4550302c401526040180e11a0b500c1c5005801069580d40c07010684803000703d410040c40400f400d035649100b00d410401e4200394809401c0e00c0400c055051521016203921054012404100d6604010440e40496015401541000309010350312440440030311907400307004401095422f40703560060100c04803a0380d1100144c1564402c85070042e1994001440c018031881e0f86446051003442c0c5800b1140842c00050b0039504241c000c5210403c5441000c4082c3da0011080c0c0c11544041a119051401a400103014100000c0c1410f004518040020381614400e80c01044510750241000454801a28000380203400a041d6a04a1450007184c00e065010786105030b880341e5074581c02000080e04104200 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 187969640 1250 187968390 187968421
    0x31b090406020f0a05040e1e16031407080f011e232d040504051b12010203073f0209010302070602030405010b0f0618101209031101110f03 61
    0x181d40303050b424055038035000c0c42d0900030150001d05550305600c0c5da05080d044500b03610702810380c800a02d008030303410102c0c254560321203600c03c841451204150780050019005010103940e00c2100300c4e207072401c01000c1d607008a070641c003611140282d03640036a00c0d0301804482800300001c03940c00643c041d03003c0201c565550340314841110803804000c860b20f0800c0114000700800420019050b00a02420382c50382e01d0000b0442c0520001c44092186042c6900e0b0f4580b580b04400040c06649400115500152668050311442d014000021035591514001c000c1c540703007680f0f0304401a04841c941501a80006102c2040340c061081c90034402c0c4000307120320200030b61082e9040303410305809100c80000b00c7d50070300c00b4520560141002090303102f00e140c200002856200c02e01449818140542c000025240c00500303000c0b0400d81e6141d00c60f114901c0e05840000e0b2040303401d0700e20b07818208070310101640000384039001490040240880c140010041c8124042d9204001c4030020600c00190301e03002405a0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 187970890 1250 187969640 187969643
    0x51204030905030604060509250312092102030706050304030807110c0a03030509040f02070b0420040504050c01080601110a03050d060e070504030c05030105010b0714280c05031b0904 80
    0x20071001e941c1d0340800e00302001190182c544d6980c82d4100135086800380002e050780c05200702440c6820301c5200d034414092040340009090400c0c20500313624500d028042400280a0700d00e1002400c4035034070114501090740702c404034003034040c00c01c4c001003060180d41641d000b05e615486201c070350745c3c4243c022540b010040c01c0c42a024413540010740104c2c6c83e954400b40145010f40c2e1403035a81c10442d010300c01651005505d41080d20301c1082340c1d81c04141841c464542041e0b010481840500445620a0340b031180d0034020b5a0242c0341c48144001c01200042c080d011800c02c1e01c1d8202c055440710010f403a00814211804031941020780e0340c3c00081d2060740107200d0752000c0c54000854503242c03501005403200484104010a40000d410b105100701160fa2200800c130807002400396604003180030030755000305200100900c0300e00000b464214000d022810000000703101c0e4518216156514080c90b441441c000da410b01803140011070701c0e003400304820542c140e8412400030003512000500c141c05100620 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 187972140 1250 187970890 187970897
    0xc0c06090606090f0c030e060f010e07020c03070608070201051b03070c02060d0219020f01020c0c1003020d090602030114040b180c04090501270b0109031209050603040b012405120403 80
    0x1c1802d4a2038400d042c82c082130483c000440d096490720141c201c0d5605880d141c11a4130200810101c41c0780440100d055038200005032626495901d0240c0c5000c1000203a05d5260041c0302011400c103510500f1244581c41c964001e1155031101c040038140554208038000000000300000b44100340034079001101c40384044d01103880d0680060305102240c0103142101c0c0d118002a5440d03100c154100480e0304642100402140760007402a5882c0e624186950198040d10503c0259110980a941660f2602012007010b201d41c6125140480081d4024090502880001c50b5945000d0515100301046000301810700b001040d43d5001c400c0d10340c2c4000f402440409020030002c02c47c0c040900a0a00800f45220b60b410b640c030102c071181e8402400c5515581c0c00600d0105c140c451aa48022080c0441c0e802149105030603410840071900880503801503a08001c001051104000726200c1660482d0300030643c540c0c07004603000d01c0c001010008010080000c0c020320040f000300d04103c15440e085407180c103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 187973390 1250 187972140 187972151
    0x302270102071a13050105190f09080f0f0f0c03190611070c0e07080708060d140d090311010e030a0602130504050405010c020105070f020709020304140f030705010608010c0c060906 79
    0x205803c1e4400d006610903000e0030000c99004a110241010b480c00303003009080c0142402d980078100c4102424003008241080142c001d40d221140c050140070000c0c02c2100c007940c010400e968002a52800f00091030070442c4a4080c843d041c144000c2000b000555005000d49100d0706040350303520700c8512140d001e4400d295190a21000e0103910801081c440c3c1c41102c1d842049450039040000c445001890742080c030841000301310140f40e21040c01c682c0b082c8100c0d030040014013141084134500118003000c15107440340150f282c00081d04049101d04aa10401d003d0f240e44401c00011500c10410114140d016402140c1000019065401401c19134004604c02d60800d5038541c0040d00307407603042d034003641c60ba5500c41007441010b90a000381c5901c03440c58140b4045482c64603038020b54651a43c170a0720191039011000c2020400d0420311a0090a4040f089902000c070741c00d040d50f100d6108910441d850741ca001400550840180281e081c61022911000030340c2010f500c9100291001503411100255500b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 187974640 1250 187973390 187973399
    0x1403070b120702100209090f150a060309022403061302070203010f061e05090109020c010209030703050c0102100608030715090203150a060801060e0a0e330601030227010207 76
    0x401504030141d40ca8401c581c141041803020b42041d64404044086a00400c806981a00c5420025810030717000300c1640b005a0f21003603507212006a040c00760f640a44c420600264186d4160001e8106900803210140d048620995400742c00c010801c900c40886030a000150a40c07605214901c0300103101c1802600c2e1403030719400207084450050420400503940c0c881230004180e0940c01002150b034040e25290b02070706100010318501814440c0581da40e4001900211052082d0140c0c3c0d50700c10040d088509454903441d02607141c640a08000f801441001502c0c1409009070088a00321040a40503520300b4a041e00c0c1d2a000544070002c0c001c030241c03600380c00b0005840821990007410402c070300580603420b0206922003070300c0c90395102d10940c3e81400c0b01030010405401d403080d001049100c0004010040101c01410302c098032000210398102c40c140c0c14001c45441c40050786c03801009014040c1070740c860f0015000c0380252a0304601d40b030f0100c501c0314000d270b40f2481d4440380300340140100c40029a46 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 187975890 1250 187974640 187974659
    0x70e0f04030825031a03030a0801090c0513030c0302030c0901030b06010e01211d0c031002031e090a03030609060e0f09070801020f04050a1a0f03060a1a03150a05010504140307 77
    0xf00310601e00000e0b503511100c4032201c200140c403900a502140614646000254002d0801e501801640354581d0b80f5880d05245501030000c0742d110107500c0d1100070070a82d40e800e22000300c000c40d200c113038001c0c001c0321410340c198130b403000301c15040c0ca0b400300c5480840c1c3c403200300440c2c02c20141d0b0f2502e4107100e8400003901d5500d40c1014107041c00b015040c00400d0604074a1058040404215640d40560b07109405e480d48583e804550043c42c1c4107824030060f2070350b480f4428800200d51900000d5640b0100c08140301d103241000c103035501814005c1e102440402d40e2003003100102c3d010361056480d03071390411000c07a8007d8104404185c11107803c50403110101e890301d07405400c82e03001990341c030198840000c08004900300305000c2c10043c05140d2a8040c00041040741030101d1051203030403181100000005035140d030343c80c0c050070050420100e0790828041c0e5401143c540758800e50b034140c0c4c40407010040000318a40210450165081a510304d4201480c0540343d400c01441c0311a0b05515004001010958040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 187977140 1250 187975890 187975951
    0x17031c0b060d0e2b0e010f0e0405150603040f0311150109230709090617031903110a0c021f0210020c013908070914030c1908070e0f040308 61
    0x300c020070440b07500000d00c045d15450710b43d00301c2414004c19621802c82e1581000c4101d01901d42540c1c04501a90303803030784070040754001030102a440030b400720074002400001114104c09074483d480d40300d03170003841039141c0b0307a0348134140c0e00881250b0f401c00c0140061038040e088007814088521109003540b4511031150640c081c200c8440002400c0c0c0d0340c00300200189402440300604001c0001c50790b04044a0740207449101e00c0207a881c0d0103840c0750150201c640f01c1d0344412240c040002c81e4540380c0c400180001d10b4108198802c3e4418407210756416a40c0c0320401d079030100700c0601d40040005c0201207044901a4010f0510070000b0355a500303055108142002e254220034480d440303000c0f12171654404d04000c6aa820401a0400c00e0b400100224250490301c450161008020048008011000040d1510080b480790503000220040c800026040008400c010f4504c240b095486041d00d4404440141004480e22000c450280010070f0100303004101690f041034203002075081c445a480400000c004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 187978390 1250 187977140 187977193
    0x4050114040f05090606010c050a06020a02010b010f020319110a050312090105010611070509040809060d1d0d051b010212151c080318010617031c0b060d0e 68
    0x800e1030391010316440c2034840c00c1e100d00002c0a08110314200740c0c0341c20f59101c500501146c1803096511000c014880d0812026891700e601070070a40d03441c1810000240a072026241d2240402c00c0b8250f060707202c90010094800708501120000c8030b111100000b02c6884c50350041511040c0981032400010400034070041811625400c080b03282401d00051041c21100140c0c0b00300e04014845003c04400c0c10040340030011160202c0e041d018586136814000614414111100d0344404001707490001c580c240e42091218815114143c61a581e183c10841d49416001400000051041010a10010450903152038404102c40018240b0700c003c507081e0041c0109840e0150454110104030096103494030484808070580001080c000da02551944a80c0c00302408010ba000c40f0344850100c0548251701040c010030340c42d003644a0610200481c41c3d101d034800d80d036030800c030408419101c06c0b2005030300400102c00c80180841d07140035010008800101076030112a48140902c1204200800e0a07050b50141c21 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 187979640 1250 187978390 187978409
    0x803040618080f071403280302061b0406181a0706050c0412030c02010c0c090e0f0a1e06090209010b1209120a140d050403050903070f03110f060702040501 68
    0x4803214110750124404950001d02c480c1c1c80070701ca203501d03a41d001c118901215070041d0340c40d00d0300201100203800d00030b03420f180c542c0d8160a824021100215000c008880ca03001c2e40a564180c1c8450003c16009002c111503440c500700208010000c0320b200e83c0214140d0406003020707542213622403107050400c01c2c10b007840e200c0301840418510140701803482402e8021300d0300d0340024900b515180110040d040b2410000d81405501c805442c00d40e4000c1d441c44c560541e02c00c3e10840042c1d00ca44105004011802c0055194031174440c0c6040344140002e60f4608407034001015086010241607c840c42d2807140c801100c0c01d50325201075600503141c0b010b5040c081c116a404c265124501d81401031182c6030000c01c0c40d407803580040305104640c00580d040b102c0c1e001d00b07860640e0440c110004039003810322a24400c0344100c0d10744410002410f034040050004418210184d038003590b51074865968004003404040c0440d10001400b00442c60b1a0303c85000b8080c0c00b83c08141441d2143d00024100e42d402d0740805c491 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 187980890 1250 187979640 187979657
    0x309050312041407050f1e1011010606090f030b1b0f0405090c070c030b13140d0e010503011802090409052a062106010314010603060e010506030405030a0e060408030406 74
    0x800841080410f0910080d800074010b1915000000f0040c0c807401c10707003500580382004209028401c03411185c00181025280354041b504440b402001020840c00080c0c095192183c00b2480e60300c15900c000c100d900342c40603820150b04541304c0001e180c001034625213500c0d26441c80000e0080000002e007034503502071140380781c882c0e140c601404a204130081480304201020065000001c040b414900152900803100d1025030392450801000d8084405014100c80717503403450344101407400503e800c200a2640e03100d25240c004480103444500082c01740b0240c00c000480400c001e040a640507204880c0c004001080318100d80e19610704048c2458964400010022030300840c950000e0307408011480705540d000d10742000b520290a4a071b6042035902a140c1c45d850205031140e11a8003d0700010100f00320072040e035659403c01400a010078031807940d140392881d0000410340b07445403e07a0b00c129001009545440381055003120884188000264000411300020840380e03c00c10103000a000f00c0d4480841 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 187982140 1250 187980890 187980893
    0x10806040c1a0a030c05130902040f0b03091905150109020c0601060e061c0b1c06050106031a0919020c010209150705120f090d121701080d050a030905031204 69
    0x14003416041081001e8094159005030b041d034408545001005107000a942c01030148129041c0c400e480c500650400c48104c0403d8120751130b8000c02c1280e9800d5a2881229035540d50708425010403114417581742c02802d42c85940860300008454464400c01c29a00a017a0344000310401d41001c1c2c002d403040310703400300761011080f01c01c0200d607001d04a141041a4161150800104d9074881c10581c800c003404c864492004074602c40d046004030080c0140b469200a15011001c2c0791000d2448055540768189000003414a000c0c4c8241d031802080680c01d607280c1810764080c4980084090700e040c0c1c4a00c814845028440d80c248060010402d51100242e51495404200960440180e209041c3c1d0780c0c003042800d00180c80010319900741440384428540f11140407001f2040c90003007100387c6402c805568005410080c6d02416070600d008241c42d030003000004c00908004040b400d00039a48143d008000d0000c03014000c902410f601ca40304e10b400f04680c101c9903121821604244035880011002206000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 187983390 1250 187982140 187982153
    0xa06030905060601081009091b06050a0807050405090c0a170408031b09100807050d0903020109030f0305100b1c06031a06060f030f040c0b03070c02120c030a020405130b01080604 78
    0x940000f82480c140e055410100b203000b41400300c038890499126034401101d0200204198420495084221280d07034241c0e503070002401940c4840c0e90030002541c0c4400241e0b065014206a9054550207402450030b95160a0000200c0d8001000601440f031942c03601d8035500f170788440c0e003481240300e40b4034151a400d0034100441c0410840030b058140310001d22110a060300d502c0180d084404440c0f85ca6280740e158003909503400d01c07540e10340c0c21b0300710b08040c4d0500c141a0150041844248240c2d140c0f02c8e2401640c2e412001c640c03054500304542030801504005c2120100041e1205900000d80d0302980044150400111045035104848030300c1201d031181001903068904583c0038805445d0f05143c41048111625540700003400000918090070103d0240043c000b4590041c08410a0481c0d0740d00b041c1c81c000d004201242c1c401c034840c4820143c1101c0c84400420760022030400a002400d54440940c00c000103020001c0683c00d81101c83e69034107000c1410700038940d00070401c5c03d016204604090a068 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 187984640 1250 187983390 187983403
    0xc02030706090b0322080c061005090601020d030b010203041707030501050619120f140f060703150308180d080a0e01050a0c080a0c151a1c200a06030905 67
    0x403001c2c40307900c180400000000108480d4800f20301c40c0c0d28040405540c5000300f1408800b14064040d17038020941030421000020300750b01454084109144040d0740f0001c00c00c2d50b070000c6900f09d006801800c54207048501a800c451081401401a0713400e02d40c8030b4042490000214100f220690b21503a000c00c1407020038403031075400080659190644c1e80012054140c140d42601c81c12402e68481d5118600780060031000c046e4466011460071503660300c1414140c0e40d0034400c5400315980c0112030204080c0e038028494185006840307011a46101e03e9a1035841d4950007150742e00300c00601d404180500340c5c2c1c0d64842d110045104041468907080101d80040ca1001004003241c1880410450b0030034207134104058801481d40880c032543c0d00c00f42c0590488008000c181c00811030281c4c2c103000ba040f42d03002c1c1c1201c1841c4140440c43e4807800001c0041103507515001d000303100b0001c69064544040303202a61400e6411202610720140c03ca400700119030020741503841040025030b1101c001040100500030b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 187985890 1250 187984640 187984649
    0x1905010e06040308070b090319090617010320031c030905060a05010806040b0a020903070608011802030c18030708100b04051f150c0209010b0d0e0d080601140f03070c020307 76
    0x10039003072070f0850ba110342581c8901c0e040174001d68040b000081d140441042250101103000003119150700400c900949141160300603040442d0390743c11040c815a0b0542d500d181242e40000c0b4004126503810349020b0301c2081c03001010b805d4022414010321a8540304010886081940d0300001c03141c01c5810554100b000c081c1601d02d650f801c0100400c0141c0e4001000d0350003a03004000300d1965129126140d00900c41c40303e40c00e4050084990014103250415003050407288000161500f900003031440310f0883c0f10854185142d09418854400240007284c001201c1c518050100d4540d03948403c071075441c00101d40c813542c490503103032500120241418099150025509094080500c0124600604002042c05540200c41641c0c1c00d000700c0500c075400580510b500501003220550310703000510200c2d480b0a01b8442d049040c0040ba002494000400002961140d960200310391185001180d034104001c101c01c0504c5028400e0501d862142d400447c0160116150302400d4041e501c103142c2407502e80c2d0300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 187987140 1250 187985890 187985899
    0x8130309030305030a06090f0902011209081e0903071401030b01050403020904110402190302040509150a03080d110d020901020c030106060e010311120415180c0b0c0c1905010e 77
    0x1005400650030980035400d80e503050500541326035503126080c0c0101800c1d844801401d00700500f2050030342c0940e02c0889121b000381c0e00d04c84042e2140b2414002d8502d4a038000b8081c1008000c1c104917001449401d84265220840083c070748006035000a242c00d200f50820b150036a00469002c207103682601c124460f448080c2042420646503800064545130010006003814110788031040c407a559660440e0207401240304590031015100000800940240c000d080c041d08051000c114800d800d00803a003202031008029100d41805c44c2e94980550b008038400442442e250307510040c81c0007148014000b40711908000503160f001800c002403030013100d03403401e5000b0307450244184016940201c419007405070a080100d03034450085601741c054420b1050302034501c03410700700388000c00413000c2c289104990420740c00c0c44079034079121081484025000c8020040302445400700050459003000e40885144041510040440200030840c0d0500344c01e0040e02140041c0b070244015a00701340b000c202d4030340546 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 187988390 1250 187987140 187987171
    0x19060e0c0a03020307020f07080a0b06060f0f0a05091806090a1401050409110a120b090309210a050d0206010501090801020906090114043203060906070302030709030506010e0708 78
    0x1200305089104800300c000c205074001001541d440d008104805c1d40c145404210f034039096860000d1a218810303c1021201c80c10f107400803c80c10314224099520911401072080d24141c0341da0400c3e802035026558a00a1000c03e0104604a0f41e86000c0d04240e004c032804240d820b03103004405c001c207000004104180c1c4620f880c4166140581594505065503016600010b140c1e540d81410303c3c0c00da20030041c850b0301100001000c42c06507000924540c003184600c2e0912010384407082100d450b0f0183c2d01d0b00f07035044561415524040c0d200c0c041d480080e00040c0081d51000c00c0350b601c41c60300f80070081c1800e00c05640524010003455a10461100060a00400841c1002c0c40140050103510411000700e040001030386e91000b01c0041c540c03c450085c48041e0a007140040320846110071014114410f40f14107000100c00e0540f81004a005d078403481541c805400d4a580d4001c05071300030340014050f8000c0010b00a00440011f208200c86406007440e40f80e542c0040c5000c80d402448000000c0c540d030116000340c0c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 187989640 1250 187988390 187988401
    0x180b013308040b1b0301030c08010507050703020d080a0617010b03190218060402040e090f1606020613060608070306020c0601150206011512020f0703020d0828110319060e 75
    0x689100e402a50141c0240b1070f540780c103520044100010070700440358031070000c000010002008641800c90f2140d1b002444542d86415090710a03015a100141c0560010750729000c502c0d00c1400312035805240e209000400c4d6444082d00c2099844050120140d44e40d2030000e03070000e18040007003040c100ca00c0003600203108203a070f02295003644d0354000c2c0841901d2000220318260b83d00d405a0b00a400003045c2e403c09882e002940302c1d5200e88030140d05c0308034001c040d51406034001086081007641c085400a1046840302d407002054102c1c415070503200590f036001c0c003040d1044c0a0180c0001140103040140e280c011042c6000d042c440d042e440b024034070b020342c960500b4403500441c0c01411100640c81031542c501800105844000422880d481311a03c000341d01c01072070b41d1205c080c004490182d0f0031200940602002695000303800d898458440c281c442e210f41e10207454112458846400520100c1d100c05d50900b820225001170b100203024009504090400c2c134035500c207640c0100078040d41d11442c0d0426 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 187990890 1250 187989640 187989647
    0x4120b0604020c0d0c0f02090403080709120803060105030703060510051206030a021c06200a030c110712051911130204050105030f04061b0207090b0307030507050103180b0133 77
    0x2142c1300a0a00100c460460184603048035542c0c007603500034110714602d1410f03140040912074102c0300c003030101728507030b01c01300b4844e107400c5100100c140c0c481c10b59451510740c140103507200e400c020240d50825880d081c01007219251008500100b8069444071a1540e03007000f4120242e10000700058002d5001a901c5000342e0f0b40c5d101480881c40180348400c24444044c14076002a0800d4100d5610b80502504c8024040850343c00800d07440e079051390700700b140924540741168440f042e04011502680b000c0c20a1050383c0b01100c03020403a600c00d500f1120381015015010719102c080c00c000717840c1014074000c0144c80e428031400403551190f03180c004510b001c1c20100041c0170380c0000f8021360900b50007040060200825a0322040e89801c0003034016506441c1c0c810700035540c2982d4041e101444c0d040c00c00141c207a00340000c240003500d6014024080d01070a2000442c018059a0b41c0d410030302c81c42083c1e510201e44102626070280c07400d0000100c2000e40d410a25100140101400d803800380d0665900110b00d60 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 187992140 1250 187990890 187990903
    0xc0e0d02060a0507050a0803060f03160e19050f0114030a15110412150e0c2d0a06030f0b010c0f11010905031902191203050a090b04120b0604020c 64
    0x14100c407110b80300c0300401070456860040c200c00030720b035100d0000070303909000807480514440d140c222072500640705614141921040b4800c1108502c4079914003d0014002100c851640031452200ca14940c0c103000803a24140c4a040d203200919151820040c40215619003440f08200030542c024031f07146007259074584c4011007003406040d030380d6580d03a020313000c44440404890003404040c42c0300a1510326806c040070203140f00041d80c82020700e04096003510140105070110252401041190a4039981040044d464401816079544021072002c1084983e00c1080f1075003c0c0400750790024040c03034151515021a0601526141445513441045000800c2081560078856110402c10b42c4220080011b0b100d0385407940100c0c2d818081c120140038111102c00c406c40d01c80e070084034040108146854541954032130360046505100d0b031003c00170f020900070001080d043c0c0091901103c540e40d1100c82d4400b039002030300807060511030b0085407020b020301c44100c540c101100300c5007145401c0821040c81d65504 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 187993390 1250 187992140 187992143
    0x4060c1218020f0a030317070c0b0103031706101713020d0309032a05010e0301062d12030512040c0b0304030801090b0a08030a031509050a022502061b16030b0a0c0e0d 73
    0x2005400020b42395445a5581c45600e070344148803a0b1903503180c1c40c014000309040327048050403642c02c4000403241d2a2402c0342c2101c686098555011181d804030105085e4000104072440036001c0a1a403801622403d10060100d07000746c0e10080f065055141a14105004103075411000040560307108800759169800c40840c1d00034205124070030320070400300e4058005680890107045002c44c000c46143c0c224100c8580114a03c2c505080c1140c940f500303604002801c0c4400750001b0f2081c022400c1c41d1200c4e1903034a40040c0140a0f0811140e520104c90308540d0080702c00701c00042c41ca00042000025030b01450710300300012102602e0301400c014059590b4007603003801074100b60300d0310198450141e180102c50301070120103509109a1030601c00481c00795003c0c01c03a40301d008024840d4480315400824161801c00e6000b05205c3c6040d8200c103612400e6182c10140304078500030f81e180c90b01b01c411140515001548509001071480c0342003400b120441e11581d43c01e100740412100382801c1e07079072191810300146 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 187994640 1250 187993390 187993427
    0x90102180609040e0709060f0f120609050a08040603090218130b07050c1c180303210e030c0f010b010203130918050706090e06040b0904060c1218020f0a0303 69
    0x60b00310a0004020740500b00e00e506050189200200f070355166504084183c82c03468280581841d0b40311044014a86113115008030320461414582c00520315400025406004030126460000103889000d51503002c0d13403008011171780e90b000681c214100b20403140e4890039041030749902454001561003004c0311041d00188025600000929018001c9c4107944030b001084040b035081640c0c120001491700c404d0021000030446c9a03024a01c0070344521601c4043e6540755446848004101000d003540060100c030882440d40c9424990f8400712080000e00210040c00000b0b141c1540206e0025007141d148460180c1190410041038048240881001c0100c42403014009010615079400c0501c010f110103000f8001d0044080025502d07500c030903c44d080d50302c6c44503844541d4840e04204400c903401d04e003800307810501d5180003c0c046001030740840030794440e85c100b601d4000948100c01c0100e60700708420403045c00c14400c605007507042044181075002025164801d1807030842d100604404540a000c0380e04 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 187995890 1250 187994640 187994647
    0x604030809072606220818041103150f280b04030503040e09010203060f040b1809101a03071e0503120d0e0a0201050a03090f02031b01080901021806 65
    0x48000c01c10980006051050780e8448060112010241089005058143c980b1032a40499a11041d64904419810701201c04140c010516a80c0703103401c1d003007914403003541c0000e01c000e4400d6071110701451004140000c03a40e42c1e2880c1200101c61144405807405010301c8140c403c2591b141c641030000d100802e917410030180803405600480000c11740f1508454003441020500008000740080a0001d0700c2c0ca40c0d00160b8680da0b1205054200d0104440c030640c014070580d03641046003002d40c025007003120003412010f8200134554101000d02e100350303651705059008021601d0602024410201c00b040150300081024091074000f07a078812403402900751171030303406140b0313003000241c80380c20740c020310700981516204c1d000740d00c0151140d00300d4200c03079240c0c505118500143d01c03804601105c060342c1c1611100c2c00c105200000f2001080788103000c030b9281c01c10b000c0d41405641e0030410541c3c01489aa81c8580400c0404001020041c000c1c0c202000c51380148135180e18a902915107c07042802520780a0700c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 187997140 1250 187995890 187995901
    0x302010e1309080d090b090d20100509030a020c0306040b0a0e071a09010e0f0904060c020106090207081812070302010320070b060906010c03020718020702120303010f1706040308 78
    0xb800b0202e002081c160001641841440442e080070140600504d1400a10395032140035a8551240b80640000980350450000090001621154445007080c003102d03040c61485000c4400c440307065400e9110b5074004280b0028041d03040050b000031000a5020b82414241035a5015040c5406000d4008840d1100b801d5528044100700000052000448090b01d250340915890781c0c07584211003603800540340740f890381011b0030400003103404403a0151058140340da45e5150b00c00101980380d40c100c1103548910000542c01c0060000d032610b035015229244d07a503150130280d0034125000801c0c05020f240100d011125071071020a040b070441f90203080105035800d0014402c990104030000d000400031003c41e0100c10301080c00d03045031040b1010349054240d41c450030010740380c42000300801001030780705180070300c0044c0f000c1c2401401c5a03040540982080066400aa0840c05003901100c183d4001710041056094803001d1500030504591600c4480c102c40c50000e4036404010300c00f40510940b403010a5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 187998390 1250 187997140 187997179
    0xc030d11070506131106090913061b05040e011e0603050903070b0103060e0706020115121401060611100c05090f13020a030c020f1605010c052109030f070302010e 71
    0x115101d5210702900d0551800c10003581440300e441c0c01c2078440100f424005d040701e00b4400d04a42c80e03540003c203c103c880d643d5404110300b480684078129040c80d1a0507603a00c83c1003a00a140005003201d480b425121400d0102e0800800b40580c0800c80c2e2a18035000f44428491b146104010349200385030100b101c0d900c50303d002d8694450f061004140c102c82000000511407568001a4004c1050094030300c0c030389d03543c0c0c0101d00ba11062803054918880c041c408111040030042243c003000e104080205810555110a0b07003112130940c8100040b4a80103056001013109001c4070150000e07a01040040418100000703180380600d10a0074081e40d801c219252040e51413443c7e042e13002085800075980c40315601d000a000d003030003507140c0b405441221301c10303000040c0104181d240040410103031603100f49810011610100c5a190655081c040c40c0e20b40c0207811307905542116003401d501c4c01595140040b000b490700d4a05c440c43c006076030b0381000400b400140ea20003200e012203201225001c402041c4c400c40311 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 187999640 1250 187998390 187998397
    0xb0a0504080a080405030105090705011d0307081e0601080a050303150103020903010c120f090203120319150f06021c0509011803060c09080303010b041806031a19020c030d11 76
    0x12040d51082c402e0410400414000500540f8425070003402a51141a18503036190549c0c02480c2c040b07001982500e8290031602c101d81401b14004048a2032641d13a05605c41c10b10040784480021040b4410101d01d80301410000d2070b0040502400074072030a100b64480b00e45900016103072541d0110f40d0603125066a01c03940680304520401402001540d07083c0e00003914406c00d09111001e0242020b24801d444000da105a17214140c0140180112032000c1d108240181d10040c056142a40800d4044840b048103125042c2861342c5120803402950a00301d112580c16001e920017000c55200c8942c1d65500d00c1942040841143e2500b040341d118003a580040c1c41101400c10008003030000800d00000f8040c0d141c0010011038490f49170019a40d403240000d40d200e1109006c1c9030062001000100311626108804280e540072a981c0010059107a82e24106000c01d45040800c0e0b80000800f80150880210300c00c80c038a0821400c00c618002c3e52004040d1240518440f00540c0c55441d00e00000764101c42c0100c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 188000890 1250 187999640 187999649
    0x60118051314070e0c090d0609061d06013011030c040e100b06070f080f070c08060601030e070602212208070914010e061207180b0f09010b0a0504 64
    0xb010003a8685180c26079941c0700d540314260b1050220000714900a014034229035000310041c4c40500c9907421601e82034003915903060122881c958130545841d0940c0e04940342462043c1901c00781046501d4540441c030b100c080e264503101e44c40b80c405014002040500039243c0d080b0341c4140001c10f500d0b00c000c002400e000c0c20400d050780080c14109050a250740100d800b11254011035000c0000c05801800d10075140508100100314062074629000441c08081c00361242001c0c01041c54a444026a41c5948004650b03100340700c0ca80c08142031040940c2c2500548000124000003021486d1518800960300c80c4414a0480c51801080b0100d00c810290703011907d00e1100702c0c00c45c00a4100482c034401c00240144582c144070300410307a002c90030700850301401c0c140c0384010a41a820364200000d200d810324005d440141e111816440143c14110248a01001000c0f03607155442c00507510108401a00c103141ca14600c01c547d030b010441c91a50740c0380700c1c80d030542d84c001030ba0326181c920580f015904d901c0386410 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 188002140 1250 188000890 188000903
    0x20307020102041d01031a130f06090b06010816050a050c03130806010f0b030f060d0f0b070e04090c0314030c06042102010e100209010314180f0601180513 68
    0x100041203805400070f20880721300c40c960a2125621024107a0365100078000240744006c2c0e5005031003184a0302c2c03900c42d004400046880c40d1080e442e81d42e840c541e2500182210456292003601e0140f00c0380d49405a401403080c200b01d210781c0342000702c800303855652110100502c80045010400640b0070400c0d030380700c00300c94401c072a61441c40d40f120001440709841101502c1c03240c440041030348007514442d00200c440030070109040d6102d50301c09040062009107000c3e0000b209a203a600400c0d01801d4410940380030f5103114511b4100f80750020030500300340c0c2c0042d00581c10012000c0005645410316022030b50004521403c05070000d902c1421031041c0221a40c00d40b1401050009015110b02140c035160105040e18042304401d80c002d03070980c2d52907404210b058000b40412000b085540d0000c0c180000140f500107140c8200001c030000600f010b40b10403c11240200300070401c004200300e003041e00c2c11004010484e541c58000034000c1007200c54400600142c075403001c45c0c10390299025a000c0d41d0703403044 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 188003390 1250 188002140 188002147
    0x21050a02100e130b09130818011106070305070908070803042903010305060603010b0109060e0904141209100305040c0b0706020f0c030702010f03050601020c090415050108031804020a1b0f050102 85
    0x4216801400515059a22031315100b80030402806d00d2180308004142e02003c11428120f040b501d0007034054582c0f8189044c00450780c071408002c403040c40450312031481502c0c001030b541021440180f429119420214a03a03105000c18440400004213903400c4944118111812108003400489400d20812000007845808800403081100114032203214403c190000c00100000600442c1d20140610801c0d020446d03094405125041c013a103199070040c01240c03135103074822000503004e1400303203061140d02c11500045801034091400307031004440c5007418034060241d0b0804d03403904013800000d031181880d00300001440c07004000e000e40549022110698407503441c3c48111890341d859510000f81280001c182d20a480b415038000d220b004d020701010b900401c007400b201c2081c00042a4050070944800794075540103c00c0f940d090060364003030003017040519240c50032030303118038510706400b10310703030f00c40c5006005d1071608a50004d13020901541c0903840700b400350614148a4096040074501609030350000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 188004640 1250 188003390 188003419
    0x80a150b0303120a290f01020a0b0a0e1c1407030306030804030305040512010911040e071203050a080c040501020a020d06140a0203010513062d0b0406030621050a02100e 74
    0x803450b6600ca915488014020041c1011903102a0780c04c2c0799240b00c821054840901c2142024100c1b0410000c060040702d446250719140c50940f0801102d05c200710b192140303211520b01c0b005200e8048a501c03008100010005101c0e4003511690042940b00811600443c1c40014548a5000b48009640100b06140e40716240c0c1001406079116000703190280140343d00480007014144203009009130042021a00550682c0070800a404442440c51080c81888004036807822001110070a40f40b1a8941036502c110701c060207400407034000c0c802d60903884244410030032640c0202c1c0340f05070300303a0444120b88008402c1ca001d030010140802c1e0300b02d00662810401c03c964011703500075416220101c500c4111130518091103015282107004500700d0403541c0b104504a03030502a2030102c001400c100c0c658200f80c5490034400c0a401541c48600000d8170307000c041140d04100265410055060140314411802d15110320344d03210340054000340284640010340c11545d10614254168110081818000c0445d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 188005890 1250 188004640 188004667
    0x1008040519060c0833040e1608010506030a120804170a082205030f03151002032206020d082502010b040c03050708010b070201090e0a020a08070207080a150b0303 71
    0xa0183c0800300d0f40c03540104000900d0310b640d40c0b10070003210401041d0214100040d81d0000d03d1501c5141d00302d6166000da8403880c600303001920010003840f0780400600c1c60180c0c402d0a42d1405001ca03030003900100c0380140407640195401d60000b0039402d00c000c144d00d0310300e40b00030074504c200001c00c070950003c40d1001856910091440c007550014003031345125040e41c0c031725444091a2120040265008211525500d10074201465000740c2c0030701e03190070400580b000b0840c03145500b03505c0801a000090b03401000f0b11700c0c003944170314074442da0f16101e40c02e400c040300a9600c0400140030424494072100256541036600400505440c44c4001c10314a24030f0098080d02030b040c02c0d0040ca10987c05c00e030701215560711900c503142c850b52907a50381a80706c0e40703000081c403081d90200304168100000c009000c1111256144624010003068000595030156800f0007081030102a081c10210b4029407030420000d03d00159440000b034000c601d0700740b44113078411130000501c41c410200b03416001c04502c41501580 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 188007140 1250 188005890 188005901
    0x7030201091b2102040905120d05130305030f06030c100e0306011a0403020d0f02030a0807110102060106080a0209041407020106081c020706030c0c0b0108031b010b100804051906 78
    0xb00d02c4008a100e1050000240440d199029002c41c928094207800382c040301000c1d602818a002510004403c00c15450321801c040111074452880100015503c103005000c0c800c050340140034840d01501081a0307070300184140300280c406004030515102040c0241d40600c104462240001c0c041200141f60721400342050000200152107030103094000280000d180500d41d04a0940c1449036182c0741c2141d08014041e24070b040141e520000703050701ca1005072010009010384074001c90034907440e50b1461405c140040e001000c500c0c115006100100600354000000503080f0701300090146cac5401000740864014404910f0396828181400144200940c040d40400e043e6100501030300c5e00c5464110882c82c0c1081100b00010060f07018160401c4214030a0340300d000124001d1030b0a0124144039151180c412500b80c004412503000040c1e0203220f07442510070024071040e848020311403841030b00002900c00342441c41c1201480078400000342008000d12070300c0101503d21342910b21840c0340d030600000920 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 188008390 1250 188007140 188007143
    0x1502150a0b30011103090d0f0908010c080a0b1002060a0f0221092a0d14010f0f060f060804060b030304080607020f150c1b070f140405071e03020306150703020109 71
    0x518004010718131081034000c40f403151038040d0082a003014038030b13011990100921604c2e010000c0500300440c800d20203002c2c0f00809440c036a0780c6401c6051642040b0f007100d1304001464821300403603c0010007070f81c0206105510500e600b0b80003480766403081d48170020340319504040018020415800000c82084000301d400380b0b40e0706c0115440040d044240b14030003841c1c0c203010750204041a401451910381040c0b901a01440758000700c403180c080590050030344650080c480f21680d00d4000c449080101842140001c1410544503507101d480c11a028007060710280c0081c2100361202c402c0c682503181001190010b0a800d8102c4000d45807140e4025150800000001e5190198108105039111003030403441c000c8042c1460986401240502c1d2448041444004036290045000015841030421f2150004054050f400c035a0310351782c1c004000844500a01a505001490200300003810401c0855100d00303030f05040041c0d8a494840c00244102d001020b40c03695140c0000d5220704055044d0091002c03035 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 188009640 1250 188008390 188008393
    0x304031109070c06020306030c04090506040209160c0311150c1206090c0a0e030c030d02010608103e0706020406020607210c0e030d0305011502150a0b30 67
    0x11100c020001c20308025615000020410070112000c1041c5900039604040b0090407070340d20326100004142658142002074131242c00480401043d428404140343d407003022aa031525090080003130143c1019202c1c600907007007000301c8480d90f030081003c005035880b00500f0500c46800e4648101c150400e94041d85030f0703200c000d0981c40420b400f400d101d001240034003035000c0090b007401d10000f002c849045a001c5055414440d00b526400c0c50b0700c05002000c090a666400800ea042c1007043c0c2518090703240960011103171909441c5184045200d56080c142c0f084022072a4400c04003034003100400411103c0102da44000203020310801c851a0700420440302a0703001d0320081d42e81c10f01c040d155600d64031a028150392040010300404421075021008840d01c9080100c0b121440801007480c01c0801203442e800300396600010300040e000803201020390b600c584018103080200850b070ac40401c0c80584071070083c2d9290020700c180c0f0f584240940651200400e107007c0d125480d064202c422040400c4001c90304e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 188010890 1250 188009640 188009663
    0xb03070603110306040513060903030b100815010309030915021b01050909040b130611092103070b1306021602010f05040803030402060313050a050105090d091401030905030903030c030403 82
    0x1080c0640035407200300b03031100a1a070035070341c2c0d14050002401c401805182080c00ea80d0800c17000500e24420403151034025580011454104000d109912810031000414808603000704640002e030f10500703240c2070382d080c600400d44003054a016101942c280d08008012100501c5802d1002d44c0060034180da41d0380c1c800111500010f1000544081c1305916070070341c001030400009070208a19866581d0404103020030304050301000d8803042c04403011030800306152000040d444645182040307045003000c0140311590b00701100c040d00f8650380d110310301005181031022000a1440c494800130340700c2180d0003240a55484030150714021403a8082c142c1203001ca210b0041c0b080c0f04a110b841598291001c1d0300040d441d41c0c80703035002c00c440340d00001c0c44100b002c045d8023041400100b06000314440340d880b42d000480ca50511140441c10a520744a5590800c2004032080041d001c0d100c002e00070710202803c000940004034201542944540d080d800d80501c0006411090040b00000030700880740101c051801 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 188012140 1250 188010890 188010899
    0x1204120306090506131d0a08031e01051309062a03050c0301080a0f0f08042603070206031f0b0a05180409030203040b0a0e030709050403031506090b0f1308010b0307 72
    0x454000383e41a42d006000c041100d0303c0e0584607071105c0800340742004c940a420341d007000864a001d001c7c0c003044640301b42c04028080620035032019119070048080031440d07150304040104100c1151040c59619981d01c07003002009003e41c41c1c1c4005828031a44480c0400044002d403072041d1400e0b1540d00c000001d2804000409501a48056905032541c030006801c03288103030303101d00c480fa007903640b0140c5e0920140b02d0b0820010b045400244000d10786040041d0900c41c042c0003047c0790720580a041e1130180c004001c0100140d8605d012203600c0a404c4901004a0701315819030b000e0856950040e041040307000035882c81198001d0701070f1803040909000c80c0c03960072544081c00241c401d00d4500402592080c8070600888414002400c44480c49241c8800318024500000703150268075844100344d944d480080c0410716034180101040800030078480c0384580d24048008185003000e05c00d00030380c100081041c003607440c0003604448400755080b9030112555203894400c1d009141c0307142031612a1180000025 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 188013390 1250 188012140 188012159
    0x30c0f0d0b0111010603030509190503010204080f06070201092319050714030f060103030528080708010501080405060403080622060f081b21030a090303030614091305031204120306 79
    0x1d06490b41640ea0a042070000c4090102e81c1c100000d40480001cae088a01140303d0f242403024100905a0b84014140c0150810b00d160400324050300510071a41010003000221380a203507140015202101522100540c00e00c0250828421458007644050b08030030590a001c00060440c050f5205900c4000c56504440100756850b090381d401484560406001000800e004030040c00b0203e00d10346801616401100042283d4104030140d10302280790b0b40d044c010030607880051b1502421081c01c10381242d05054450594541c0d0003000101045140d00020385d090b02c0340c084800c4102245143c4a5401004500d1040540818007a0413005181d000d400a4080f5000a036002103070081034425003030036601014884c0180101d41ea84103080051a9440d01054040000780312000d016694012140e0031450001c007a01c1c056070000d0030300112281d9005255039004051a003065105061176011080c5141140c1035014940d561840c441c2c18004100520081501d4801b019000f690100310780c2d5121240c40 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 188014640 1250 188013390 188013401
    0x60a020a080402040905150907140406140909030d18050c010c02060a03050601020c1206101703090405040c0302060309030a030c03090b060d1502190210090b040206030c0f0d0b011101 80
    0x10005041c0c0700450003504255102541250196055900041d900084800c5091081d9180b200b1648040820030101094408118101004881c24030140345000c1040004c848041c04141c4954020000720740e8080f07007042281c540b4480c1020a0105155a41860031040341a04058409009400e0801000d40c0f103080c0c22041c15600621690038400c2c4444124002c0000605050642c800c40c02603004c40d5940710340f1114851041d000500480c50146c007a103130008032646c0034610604c1e50091081c00c4400100542c1d18491064500094035030300da041008043d43e4550001c2d400900c00002e10800000220040c040d0b150f040c1c07024080c01c01021000c50403a100142e0161070020310002090051a0005070004401d00584071800b0100900810784120783c441200d40d9808c082c4030f0301c0c0c480d0254060048030988902c0c07403c20024041a130b12082404180100000e11422001001400c41c81248041d200d40c2c00040d6041c6440c2c6586580c4080100312140216001c82d420000d0045911414090b5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 188015890 1250 188014640 188014657
    0x30501090c091a04050d11010e12070b090f040204030c030b010e090c0f03010e101508030c06010b0918070305060a0e0402130c0507060e060f0c120726040311060a02 72
    0x240c1007031501c0d20300f0000c0c07012a07404030342800f2a01003100040301d0350303041c541b440814014600c1480303910791000090818500c800406014032507050f0115540714000c40c00304200d40050043c25900d528200003d15440c01c084076440e4800c0c80410084240141c45035030805892054002a2643c2d80390701e032000d503462040b180d96645034481d10411000741002a410151603001400200303074101d88013070301d40c1007200201050341042ea40e0140700b03494450b031840c41c400402500019504c1e00000004c2d80d5200c040c1402528806180000e040c9115126403091031041c603071040f00701c0d505050030b040041c0a40801e8a0007803081c18241c20100d4a81c2c0d411403802e0086a0042c007402d454081610300780040d00c5100324200500c031050100c0408510315002c0c00700300500541c007404461070b000120400f16070020f4402d0014403001d1240c107404485030501c00703810050a0401d141c0307045480f030420500c01e4407000034030a43c1100030b052008044d007120700d0042100c3d15034240c030804c0d03071010060401c90194210 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 188017140 1250 188015890 188015897
    0x912020601030f1205040302061801020c010e0a0e070203070b100e0c09010f080a020d06031113200705013305011d1c06021204050c031902090910110a030501090c 71
    0x5052001620382414884c01c40203508003d0b040c2681d9800191f000e0f0400602406410103900180c20740390303030600140380c8001003420064102100000421124030f854040c1455145000000c94040c5000304290f070145984140180a00e04d400e01144242441d103200780200c04003801c000c10b08141194041d503e0300322040e036030034940308443d480498070742c0c2c005024200029400c04c07200544240c240074800107140078042c10503552854400740210802d0320030003040074914065a070f1840492035410141800030b1010500d85560740c0c1d040080c010700300414000c1180480303041c555901410801c00c45010a920b6920f0b60303159079100019500000300400a0300c0a20f14010722032400d10f0044102d07072514190000c070946400c55a40c4400c1241e110402440c21000b052040100300441000801c0c04410142c01510646012681092800400c004002d01c2140040c0010b5600ca000700018140107071501e4062201904284071700321181e120302e1100000900f80000030500010500031a118420103a4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 188018390 1250 188017140 188017163
    0x60306070512190c0c110901080d1215120b07021f0c05040b030106020a150b030601030b04050102070c0608060414010510050f0d09110406230f12070801091202060103 73
    0x42d1401e00c6804000c202000807540400449402c0b91284511080807400703071640042c0c000107007407144990142d600c44900c944456801417042e0000841c14004240c880c1c2410b0036000c02c02c00304400a41102d1443d00500540200c0001e8540740d580307035091800d40110010005c0352660725040b40c0b036140a88c42007442d40660307902c05640b015254842110080030f41340990400792a000c2e212a2a402030380301000591040c05100240484421200340e155001c007400c000e815170030400710b516944148005042500325400080a01c40c0039012a008540d012500310025074481d000075081d20010740e0410300a030b290149100e80b00307000300b012030b0507101c1c0102290395044969904407816071094186c0c030343d000e0b01401444400040383c002c003241c44d4460040070824440b500c00b44412180140d010204810003100f03075804c00960300c00081c150b07210584542c180107003100042102e0f00c1248805d21258030031100f00290300d42c011f42c00072000c0c0f44213681c10039a0364503088080380e80d03010a010140242003000e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 188019640 1250 188018390 188018407
    0xb030f070f120204080d023009011e0207080d030b0901030807030c080a09081b130e07050604030b040501150614030403031407023403080c01090221060603060705 71
    0x4a550710007500c882c0c540007000250700080181a030300b1583c4031198a0740050040380f0266014010791810070100043c0c00e080c604e0484182c1884a02c0d030152500940b000a01c0d0561a4400d41c2020060444d1000711070442c07001007402035a4203481e200b1502140503a5440400303c610a0140d0151888010a00c2c1c23126401c68403205210307071040c20210240010ad09440000900d900301900e07072075000346c45427030354949407502042c20006a8600424601940060080e403950fa49100c42412850940c00240012802085914125290300055032090780403900200300004d640040e44254403890080c0120340b50645444580e446600030200032030480f02c2000861170840002d503070b1041c0079280102e01102e030025542e0740760708165100b10058100030b4800d400302035200d060312143c17800f024420b011007503d070300f45401c1c444581c00000e202c0500080c0544401e2804d4100020031500204008140c828010524184200c402c1603807070203000e91800142d41c3e15000c5040e0b4810f51179925010b142812a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 188020890 1250 188019640 188019647
    0x180b0601200307110d0605010e090c01230d14010803040603111e0c01060e0c07031709030901051606150510090e0406020d09051204090b09040c050405130b04060c08010b030f07 77
    0x14000d1031178009103180180000305405004042c000c009200388500c1074280080c030941070038081c0b000d06042c056040390070510010004074040e03062a4419041d91504d160500b600c025102d0410317182c81200841001007490350020000303000b00e8a02ea241000314034441400038549024107090114156489090300c5010110000140760510000c400066800e03200c0100001d036031401d4810138410303040400c2c0f0104040d00407402d80c00303e205020406d0258a008181290381703102c2d802507030741000f0002c21654012043d151010320440e50202d801d0060048541c0034604446491045600c43d03550030f0489680d040c00b4a010000341c5800d1a51440d9079034440d220a0041d5104902030048141d4032601600425000c0c0b0681c040d503225020450b03992803801800f8002d680304694203500c2030240f00140800501912003000c00c41e0f03800d031008507040c0d95051104c04040151140500100440d13400c01c001c016090340002c41da079800e9120101c942e40c03210f00000e4140400c4842c0090100520702050000c0d02 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 188022140 1250 188020890 188020913
    0xe010b0a0f031e1a0a0b0301051005101817012a0309020609040c0c020108010f0b030412231c05070507020f13020c0304030605010b0703020d12180b0601200307 70
    0x7401d00081942c05442c0c2d14103003040c928188280c4030b0b210407000e101c0321170154018400b20b09000c4000348400c2c10306100d20141c014140c415240308400c003003101c0b00c005006110283c800c20f91042401c65007640e80c2a0704030690a0304803100c02035441c0028401c0c20280d24040510500e1201500301c601143c0780701e0a400802d070002060360b000c1014401113140399218040c1903030008290f621409501241e10001d00003150603002600c278021090030130b004100192050300c2c0e0064121703103c000d2129400d10151004168054811022035035001a52044482c6000801800d02d030b14002080e8011a00c0c4900f04643c8155000000284100111009440d00600090b0610002080c4895a9004812200481e070081201d804590000b0404000784000d610940d801028402c00c4685000364a46d0000e4981100340091014031003108100300c04108194010081c40905134a84180f00f80f0b14103008003000380c1211124005041141e514180d2050032100380c0318080d900009600b0b01446a03204900e900 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 188023390 1250 188022140 188022173
    0x14060708280507020a0b06030f0a03080a090b0705190201020906031617100e0a0b01050906131508150307031101030218040908030603061e0a05150a06030e010b0a0f03 73
    0x70000704000076000911415010312415001425004403924082c454900024295442034202c1000192902408141e03954901e6051816103001c0c0e1300d0102000041c8050308000c1c2140e07280c4230400180300e40250081c0140c0d0030b10130003100e010070b58010803803e0744194140340740c0101082c00800ca0b4104a083e0400e85040035040144110341caa0070080e40c00e0600321008c2c15048070101e0200700a006d050000c1d50070a10f1481c0500240e080d560001c7c0c0244145c060b003a002d44d600090725010850385c00c1c6450060050301c4004e000354010384900030200c0000b40c42008000d22220500740251070b0002e07058040300c0c5d001911080c0b004607480150003e4011504022800580b4511420795542d144281e000b02c51040c00c900c1e40345e04041c400d141c40c0142c024044200a8100e0307000210411310420540e50001c4855008a45503841e14a0030003442240b05005030080d641c0e007404903c1035055040b03da41c41107010001c000501101c020002c1848052064102c03200011000f4000f00789488820382c40034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 188024640 1250 188023390 188023441
    0x19030e090a09150b040c0503011505030423010903120e070306020f1201080d03110304080306041808120105011d09040b09010902030a0b010501090e0105060a030b0f030f0a14060708 79
    0x100c0c2c8603241c9040c0c00c0d0040100820300b640d103180820030707403625100d90081042d00340350050466041c01c0ca90300c41100348050000c28080302000290421844502c180940501144000035120b01c81241d0341c060a1702c07100403804100030940c10302c0101c280b4420b900260340c030f480c002d0200038074503211a0001e600540d10900d45a8040009071450085080d0f050f00800d10180100030310034100c20010201c81c01c081c07030114041e00030010300010032214420ba03908140212400214010400103d4003030813030520b00100301c2003011884c92000b8054081c034604a078403c1c0c940031152030300c0294034040840d400440c0d50f4800480c90209010443c540045540174482c8000040c0b0600c0940000c2e01e0b0080b40803044900d02c15640043c00996800305e20f41008141300c0b41c06100780d505000c00110b203401802441c03400c0554407100341590b40d0700c0d030031855000344015050301d0f41c1c862031006603030719024040703000e4900c4030f88040741c2a400071000920794031030b900a944000c840c1c0c680e00c082040105031303000d608a11 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 188025890 1250 188024640 188024651
    0x10b070b0415180c0315050610030f09170702030d140711030c0a08060103030f0f1d040906021303060501050d21090e010f080c0f03060105060702060d05090a0519030e090a 75
    0x1002c1c0c22031283c005008540721900c09286241c0300b60b002c080f82c0000c4c18114148004c2c84816101c1c103020030700ca0b01d410705011954485007140d1100800d20b020002d005508128000c003495180ca00007004c440d4026000c0c0c80b00355243c08801d403410f052211440c07820450420200020500070202c003c0c0d80700b40203050710403d40d26031002500d080600d400400b85504000010000c1580011150884098908202c40314044058001d0400c84a0220003513107070f040b503c2147c1d5030359200d91000740c01c03c0e80500115102c2403580e8000303080c114640011520340c0d01e80000810b40c1e103012000392440e554000c550652810148481c01e0001e0500b0900300c0a1110001740455102840d00d1903134041d1007070051007208285003486080c603101e125610a03000d0b41c007a58030000c16840205655040d00c0d010b60722203903224020310103d00b40c1d00c100889013524926000074010f1a2001081c203203a5180a20111500100c03054100d4810503c034490040100701c452598581c1c5051135503285034400b4910800144 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 188027140 1250 188025890 188025911
    0xa03020d020c06010806070219020105042309040606090b03010b090a0905030403061b0e091902130302060c061509090304091a0607060b090c0f160611071109010b070b0415 75
    0xfa03e07900381c00c0f403581a003003a020050010f504001034500d490f102c0100c18503200250b0000381c403911850140161003000302c0c1030ba403200280c4290601e00d0410140c4081034030315050820800800640c064101a00d040c50030010a501c3c050185c0a05104018441301e99515800318101c000e0158500c2280c85002c20700c0300101080180c8617528161900170101da5104010000c010180c464000500303101e00c0d40782060040849910b050300c0042010042c00503521005941e5211544505603c025031181c000503060004240118110707006042505001c0c004205880c00c2002c05c1c41c048507440380c0d0358800d1004100c0c0209940220408803a068890003d082e0000042002548102000c0d2105c4d0b0701c0303507d160001d0800710042640841c60700515818042d8240702802c90b03114121144101a4021100c2428003220380e0080b840b07103041d1401d103036a9990038981210b00c03550040c042440b6440c40c80002074050007200c11511740c04c3c2c1c4203a01001590b280da0300c4440002d2200342200c11a9940c010000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 188028390 1250 188027140 188027143
    0xe060105040902030c09040c030210030203130b070908030f0408010606030b01020a0803040204060306230c03060d23070e09070f06050307030504030c052d1c121e061401080402060a03020d020c 84
    0x280564008c00c0b06840650031130040c007209002d0f114840081510400811240b1603101d41100e0845900c50780d400c0c0c250300c07015812100441c45da04001d601e4040014a59401350039000204100e61001d0000e200e40342d42e46a040e0f040303e410103d15405070300403c4065000814820065a2040c4020f00010b103068503900d13003900300c80001ca4400c1c0b007680c2003140708043c2e0b00352500036a170001c640f00c040380c590701d052030205804920302d010003003420b41d0340241c882c401c4c0781c100f1350f040003800148215607134a60388048100e01c0140642e00011a4002d250b8040341b4040131408110030750701e440c0c450518640314550200e004040041c001d404100c0000760703000014005101e001c2446082d50581c114101d02c0031400c4524581f000c41202d0717a40d101d4041c034107030517242d01c040740c13040841e50811581d03107994400598080d200142d1149440c0b54610051010b00b4000d5000d801552003140c4900d0010100e0001525001010f65001e54083c0c0180801188140300342c0050411040c02040036003485000442c49 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 188029640 1250 188028390 188028409
    0x90a0b0403120f0903020f0607320304050c0114030403050735092e081e01030302060103230c0f0604090e100b0a030b06060a090e040b040201020708010e060105040902030c 75
    0x80d6400b13502d4110350414564100605043c0505000117000f00b41080306000d0094003104610502c6024040b0300390000c1c82e41e510841c03400f8a04000110755910346841c1080e210360390180c4007400300700c0000080030012500f006480c49507616440b100d190070700c2a100e07540702d50020030300d803145103c840c80301301d003102505482010f4440300b2490240d01c4140030b4040205d20002c0150240340702c10f407004002034840c3d407140150020318503030800000507240c84655149404a50383c404541400c01e07800001010390020700d95040702c1c003c00142680c008400e580800810b0510441c400075480b4642c201e9103454030050954002000415283c98103649012090903100728040c084695005403010101203110b80c05601681c100442c1d802c0c0440d403c0d66144c0061620240280340107940100340404224043c1046101500c0342488883d56803a00b860141d21510080324101d00602914100240b042d00c14014202001c8401c40600f00c50380c244001e01c001004d036108240e0b410f200380e0000003016250360a85 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 188030890 1250 188029640 188029661
    0x150b041212050a0206060d2415080115120303200d060608040206180303090d08040509100803070f0602040306050c0901020c03010209030d080a021201080d1112040e0901060509070512010509090a0b040312 89
    0x101302007215000c27180000c000c552106030f81c0d0b410116940388010b142c01c4864141c0b00c0150803e03480044500b0200d0052000c54241c0301c0000441c00110040842c0c0c902414040a00c0314091103101d442d64400c490400b0b050740e00035007200081c40b011045961100c0310b00c0910101801701ca08160000000901010340c0b00ea003600c885400040500245c100040403940c00001520000304080c80e258280da40d0380b080c0d081c0138216207540d070100c43c10816140c0442e8020741d00880c084c44941400c05d9a074509600955005000d8460300f1f440081d00d0070103009503248240003c014100500c5645815202c5210040c0049910787d400c10041a0440a83c500c0c0c074007a1104100070000c5075a4244042c0080c0e9905501c182d0329400300c0098403400c0d02c010211401e569844419a115449102c0304a02420007604a217a00c09041000c1200303240c0c1c8000546905d000da60400d24039644d0319814441020000d032422209030700001d8220000c100701003103894200c0c0c0b203803030041c54407803929030400300f201c2d907140c030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 188032140 1250 188030890 188030963
    0xc0f0602031b1306020c03070609180603020303070303050f100509010924091d0a08040b18030111090f120c040903180602060a0e01140604150b041212050a0206060d 72
    0x3c050096650400c415401c0b003070140d0042031590b08040f0040d12a50042c81402c081c905052844410b070100c071b40004000f550702600b00c0351545102d242c06009803200b114040d12001028000640c1e02e480720000303030125040540020590303402c00e600388020b41700c46241c2405103004030000c209200d10710300c0ca0300020440f46c040010315160011003a244081a480c689549a104440c82c2010403507000485040b5080c9651007642c445840040002d12100b0485196055107400c2003016900b2914004100f481e104940741c884443c10002040060100800d264440350f101030098542c9040c0b5a104d054042c0c0242440c041e581400b0100c000900b1391a0054030060700030105200b80c041c1706014251200c00c400c8001e221a070f01605e000d00c0c41903001041c241c40346484943c9800900051700144000e09101c1728000c1e034494030f4984080c220040300c01d040750002243d0b07a0a00000e4851015500c007520958080c00054480604000482075280e40641c2c00d03001c40c41707c00e09075114010250340c14000900 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 188033390 1250 188032140 188032177
    0xb06030a0b100804110d02011202030a0615050c0705100c0c0303020a0302010b3304082a01050a02100e03130305100f231e07050408010c0c0f0602031b 66
    0x101400042d61401680b08148100c000600c0001945032407240d14003002a524208140200d0004860425500021950040c400002c1c04009011500310303209590661681400004509004803001d10510780382501c180c100c40414851407611810083d10070840d803030200f680144907140c5044940980d0300440150f80124080c00070141c081c040d000540f8003c440c01110007412041c460701050f01d82518800381c00842042c25803110030720003610081c0c072880088035100f82010309081003500401140c03156109000905692940c45007045568910407640030b03095a0b0701224061025040091240500740024045542c002600d00c1c11013006501800040000101c0c4080840844102e412096000c90400358406207101c0351002041c43c03820b001040c180c0c01d40c0d4080301c00c01c1c806e0204540f00110b113a9181401000740d8070001400503104034000800c0360070b00d011001e4400580100d8024400000d080c2c070170000c52400e41c0955806801c2c0c00900c10b00c16800c000c3e103000d0358050581455030040d4003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 188034640 1250 188033390 188033411
    0x90102070e270d0f0302030c070201030b2b0b0a0c05040b0d09050d050d0f0606050910030906050906161d100e0a030311160b1206010212031006031817030a0b06030a 72
    0x140d596013491506044c1140340d8203040540e0303040742c415054003a0502d6290f1103165101e1f2603000300e003e2808a501030b880340c4484440c581d00080c0c4c0c0003510903a03003210b0b400c000c40ca10703141911610141884030f445091501f440d10848a0060304081c0c481c43e401c59550142601180c410f011107851401155a0103655202c40c5c078800c0308503100740961032100d518240042c065a0313000411190100d9003220103036400701241a007200031f080d500f00010b0003542000b06014400074006000c42c001d030905083c140300868000012105031440145401d544541030904ca5020300300340c41c42240c442c01e54500f032074101a090300480c0054003e58422800601403208012100c0c20601410b0034074064072058188151170003c0c1100d03e409841465101e0300958404103500b40c2c0208002c41a090b04141050b8591900d0540040210418490140841d09002d01510506c01c0358841e40312290b801032454042c01d01100c03080f40c140d00010301070141f150b5642c2c5005115512800a50301c0b45000742008100e50418 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 188035890 1250 188034640 188034647
    0x30f0109051015030f0c050c061906090212040519030c080a090801050f010f05040e06040215090a08060a0f0b09070804060605060d2909010308130b0c010b0114090102070e270d 77
    0x6e9070f00b07201001824072000e5085000803482a03000b1041580c4034030900c0c14100c40d1002469541d1045003014400142c3c0d2040490507407400c0e1145010707006985081160800310720501c2110380b00200001c11000740000020314038009017030110f1451402c068400c0d1145100340c2198000c0e544d440e0f242511703400420510358801607900140c84240ca080c03080c9c10a0307980d019070720400500001c1c801c950f5004142c01845050082d01d000050040410340090ba50301640364442c0420303030340040c0250420011040f0111103000b944040c807400f408411982c1d031005000c0380c00180251080791a2074980c500090305644007405009200b46001c00000d69844002130300c060200c0e00991008500380b840380e00000d69488896850440f6000010290744042c591459400c0c1d090781c3e00542100200410443c480b06015800349580c0d98007a02c3d01e0645410b40d032614112401101c1d01580103070b01c0108103020f072400d480c03451a008604030b984200c00720000c04000e004404004589055584110030b1400380960 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 188037140 1250 188035890 188035901
    0x5010b0a031b0510050a080903070605010e1905010b04120203070e1807080705010206180102070609031124060f03010b280f03110d03050d050c0a021002030f0109051015030f 76
    0x402c407400700156030380b528090040c0c01451b0980e0140f001010010b0b040f000d0074000c4801c5168802010801507071500c0d07512082c450b09844031090f50f8500c5401c103104004910905041e561040b01c40c1c0e06042c035110740010640e030540000c9805001d04800095035911100c00680698440800700d41422030820f44c843c90908a640100050345c8100801c01085c0d070041303030086e0014912526044801d270400c40307240c003911070118018600780c605034801040c1980816100f00303610307040c0151142002d154290811040d07003440d02c82484000c400104074141781501d2400701e00b0b1006400890094036030310000d024000902e8020b4683c101b08100200e41942042411000d05480400395070f24030f06540b181e401c140b0300c0041090141201071840c00074140503600382c401e004c2e8400c009010742d262820381901c0c0c0390414481c42015200d403020007a1503541c540245c920549081070304102d00c0c0e18141c0c40f0f4010b008044d0140146000441e00403a501a0030092000179102d40e8402090400305010300000320380 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 188038390 1250 188037140 188037149
    0x30c13090c0f090e06060705070e0c2a06060906030a020414070f1b0201050a0302041e0303120b0f0904140316050c090903030711072d0501051306050705010b0a031b 72
    0x141040184130100c00c03c4005030704480240d0ba0541c44840900d00305243c450300382c0107074080c506603a0412100c20001401001c0a11044690f844402d211030030107900c0404e20400224583c0003580026840e051000c40780394400b4008044030703164251b5401103411514110200c0c01401c2c40b074010405096004502204100306500d0172403e2164400e44005000908440081c10040c000458042e220b01c260150341c0540055803a208400241c12805003a0304814401240440c006034101015802c1c607200c0c0f0003c070b010240c6031640e68150a410440c11003002031003140c04024908a8407482c030b03010000b03003851808595100303160000070706025150846824096110318441c004001e503128000c02078070b40021060038000c0e4000d0043d6011820071655402118146400103481401c40119640d0441550b103581c810a00340364a42004403200d101c2c6401000000b100800c0c20044039101d44000c041803402107000180035460300703002a03110002940305540380d074560f101c4c400007805100300100080 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 188039640 1250 188038390 188038397
    0x2030c0a0303030605041d06040f0f02040606020a0b0c04050307090b030f120c07080105061c030c053414010f031401030b16030c1b0f05010e0607020609070f0308030c13090c0f 77
    0xc191f1440d071a030f407680000c00003800d4580d510360140030003c0c1d180018070040e41c0140180880c1b0b440340c80c001e6841c84182010d452046c5004041061456140101d0f0280c1d032025000e056010308124074100a07020030380704141c040c810215161403080060140260981444008541d1460950041464401e09030810b584503490f18080c0542561b8100d01401c1d024243e0100c450803d00c142025694176080706e0000d80540280144081220401c3d148034400c407801d075480304c000102d03d0740ca40f00313550300c0c0340a01d01030001c84110b0100c032507005440082101650b0b180102d00110f10410101500f48213900c112031a0384814180407108614016010b140c1c20941307010400040003120052250300d101c1140102c01d03100c1403000c400d211408241c003090540100c0240070004100c0c0c80903550750000ca9840d4014001c03003000c44d940c44c801040d00c0f8200c0d20000420300840b0304603110f070380040d40040c2240d894030204000148203000b0107407154000b003a01c290009102c4087c601d001d4480c88103070f042ea1040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 188040890 1250 188039640 188039681
    0x14030a050105151e1804020d021f1106060310050c0d02040303050406030b0f0d06020c10090803040209060105041805070318050604051630020604090501150807020d03050402030c0a030303060504 85
    0x1d83d2650300740d0760310441c94009203244503186c0c0d001103809000c0e1131401030740110302410a03100351112240402c0e0032000707940d1b82d0800202117801d602d4940d00140d90440e41504050004031307150b1030b1038002d6034001b90028034440c902104554040300b02d0b400360b1310840100d0f10100b0208181ca0b003612030340d001410113942d05440c101510300010000f40710b100005120307030307400301f40310792425030820212050036a030480410880c9400c0c00c0400c05d075081100c0407841042c007003000480c2944694160b40481300004606080d034807a04803201c020b45401860b00c070803d5030f01ca200c144d4001003811100c2020b4000c002409240c00c06043c401d041100d8003d13641103500016000b00100d03801c44d02c03040ca80391840481132210300754003a1440c500d1700a680002e54030000203d13000c20142c03032540c0000c0c120340702d07200d03021044a0541000d072661082106d4260250700004001051a40280c00c0700b544544010281c5180078010070000b54140810703003095000942c5c4441c00d00403030916100b1041300080443d41401c0703 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 188042140 1250 188040890 188040949
    0xf0b01020604061a060d1508030723010b0d0308040c050108010b0a0806062107081303051b0c0603091005010b0c0a030c080c030a0302030a0f06050a14030a05010515 72
    0x689070400307403004200c290342c0c0740c1e080d5a01400c501010b02c107050042c1030964070311044c11203002401440c4900e0326240700c5144005041d400c0042144c089961152034071058290103048048440e58051410842d9500c85c4400d40c080e988400042d03c00a119446462584c141414044007150349a04550306000c0980014440c481e40c11068544120061420800542d183c8004c10024011000c011f030100c0d5964030b05003440301030005500d104900a50b81d1020b195190007029821503d01480980802c2040140326003103002d408451144500010403281040c0460012903801c0c0e2084948a0301c90300114188504040c050052030b0042c0724140c0168100b1803601d4596032039021100e401005c4c02030030300301300c0300700802881500c80d07000c2c070903050740d481c1c0c1d8510002802a51044400fa04014909407440e00301002c0341c840c04081d98030142014030540d00304041c1200310780385030080f00e90501c21085c602d00015000d0003180c3c890a511245840700b400c03010180300c2c1300e8804886a041041a4070200788 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 188043390 1250 188042140 188042143
    0xa0305180309100905030703060204150806011b06021207121d0706050a0207030c0803090108130506010e0702031b15010506030114010507110405040b011707120206071110120f0b0102 80
    0x254000310480780540340382c0d40074000395130f01e4110380d02454060051031030010600c003081d030141045800290441e01400d01c0018101d4516008079034860120b5401c07485180c3c410558403c260289204503801480e062403003040298042003100c14030300142d0020803000c624403503030040c0344450000c0b40c0ca940c2c0341d102072650240c5502040c0242d00405c0008901d96003128801c100707020007142c2203140440116120402c1e56100c0c1d00501c042408200440b000c00d082c40c600341d50b40103006030000060003050b42440da0041209102405d48030031403000340315510182010112492042802000514021207855a600703040c0a0503440a40700b9403051004205c070104200c05410740070001d107009039681c642c500d86030344074034000300348590050701c2c290401c41000300c7c50b103965040e1000300711b50940d03403000d0301c05450741d8603828003da0007a001080c884e0b00060800c00043c21800384200d00380c028a200760780120355880300f410f6111000812001102c16000e000d441411000c00d01200240b00340103031100040d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 188044640 1250 188043390 188043397
    0x110705060406020a030b1306031101091503090203010b1c0209060415060c0201090b0316020c03010213030b040204020405041e1a0d0b1b0f07030e09040f03050c0a0210050a03051803 79
    0xa0302e1950000303400c601e110710a07440000441002080450008030f800c544400412075404101c898103d0485540716035030156805004440c40c1c0c0301803800c203140c1800d0880180c000074108907019921100b400e0426920012080d043c4100b0204030101c14042e401000780021004c4c0c5501e000d2440d01c405540300e008162100000d4400a00b880c607d440401d01c0102e801c0c2c00c20b42d110003290100841400007040012030301079111861b590031101019401c40c04c0500301d00c22107004c0c00c5031420745402000006c1d61b450400c1c1d40540000d10060601c1d64400c08241a100078080c1c003050300d647d011140040e00c10760b115a81d01341a503000118034400b03d680109180c0d000300200600941600000500003c10a00c0300f1001d440032700440540384e007240078220b4190b400140f41103001c10080f1600c03081c1c40c2042500c070f40c4110b40021b0709200346410b0752401e8400e5404200408d4290107005810070150f1030300180e140b002e010a070390342580e4810307500b801400c5400181c4824503100d001d220b0030007591030000c241c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 188045890 1250 188044640 188044643
    0x30b0f0912030406050a0c02160918020312070203071403060601050d02130f150512160212030f010905060f0a0501050a092c07092d03050102031003061107050604 71
    0x118140d86490001614202850791200c204007000401c0108200d06038000c0c2d40503928103407060002040d0311a0590f11713001d04066803240c1560004040121240c01d03041950441250702600c003050685070081ba0512000c104c045241c0300002070814110300301000ba00c002000c00b84101d5491203010f82c0083d4980c24003504007410080c0201e1480e040021650489000c00004106100003540e1401c02448140722032080c40080850680c240320003d0290044840c0000b0701c2c0340c90441d81e621a104c6640c5400380c4c01a02c01103108250180301c040c0c440000a50140c0c0d03601046070300641c0b41800308401c0d20001003815000f0120006151066211170b0302e18402d656007400c0041c1c8819411208503010741080c1e02c201003072400f0491028600c03800140c0617011030f0400720003803040c5d41c400000707451100c2240b08110a4070b10111501450000c286030440070401e80c086491619552607e0341426a0410b41d01252004903103c4104100701441c81101114032150724018200b40c450380300c0c1610380100920 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 188047140 1250 188045890 188045911
    0xe0f130f170412050c040f0e15041e060f05070e010806280603050f0907030f08130b040602030a11010506030a0b0406090203010509100c03051512011b27030b 69
    0x4074015055888090310041c080d0083c00c1000c2d60b04034146a82e550300c500314442e0055140a42c9222081324500640106030403002c0100500c0510b840340058200c03000b00141d6005100c80b043c4c000740040c000803070a41d070b4001c0b21301042821000211070300b01d840181000742030080c042c61400302030742c02c62100c540c000402c80c1d890080301040040d8a9074000c081c1201c0d0440303152a0b0b0041034840d010b5214500504000341c9950180c3c0da040c4616540e0519404060a44a00f00000c034002071212030040c06040303101d03a00b000f00140c0c4d400c500b402c1504240c02c09000f682022440d401c216038032011807940700c10104001c2c0540d0410001094980e00c5850025001c4e0520100060030b1105da40c005940c0d10b40e01400802c03080c0703041071040d91900c802c2c2102d902d5050525450010452090240c50f0150303d030344511290010811040003205181c020503508595221000c4508480c1001c52000d180402611092040103800503550010703c2e142e12074110340101107a0034000300701910703c119407120341d405 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 188048390 1250 188047140 188047163
    0xd06050307183318050105090c0c03070b0117060708190b01020a0210020d14070210050c0a05060403080601020f0f1b18010f0302040506060306032a030303010e0f130f 73
    0x241d02c00f0780e190200450983ca5402a400b4038840d48400c40900c00b00c603c04080e0040f0000442c2e40c0000340c80003803250f21b501052610101e050410418010300a9503111400c5038600400c41d9180455101d00b41c4c80004003204060607110b400c0410b10400e50b1050452070101042c0c913000301804d001301c84003510318055030394400c1900c20a9008000480000350010304070a00c44d2042280250360b1504e182b01c00c8001811075a114030441084000d0f00c4205900502030080e4001e0306008403083d800111000e0b110b84074407240000402c0040c0082c0380194007a0b500c0c0b551518201001916102d6a101891042d07400243c950b008440045000c0e052200e080444c200e850a8160021341400c034181c0290800241204c00040c42e84000c01c10001164403d80e42400b8a59482042011030301048800301e81682144020b0b404031401c0b00414001c01d40d00e00c982c07840c40f11850012a107180c0013604032000c0c0361202000d2001d2040c1803405d19500c61420400e170550720190ba92081c82007400040001d10310076150 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 188049640 1250 188048390 188048411
    0x1404022805060418060602070b0f0913050702010b12070303020c0d0609140102041d09030a030e0f0d11010b0405010305031615020d020d0c0806061b030d0e030d0605030718 75
    0x44224038010030300140456126501c40d8400c0c1c88403031520078190030080c603000340014220b0000c140c60044400140c00e0600307007100c56500d140c6560143c28107a9102c040741c0000d0985020500c20300d406000c855000003010030303125051200403200e46c480e182c1c0700d91055004100190740062035216400054400c2000d5030b0b224900000601300c8408000c11502661740803540742801503000e4000c683d030880e0030010864a80700c0100490505075001901074000300543c20005000340c20140256888000722030004030103810090400d18041d11003000144449140000100300340151800406c04990820039540345a882542e203100c0c640401020942c078002030360a200020089001c86100140c06664481139402058004d42c003010284082920f003624061a41784550000d45c8139441c041d090f00d2903c111403090f003110040a441031a030394482002102c10840c200e0040304134040c0d16400440c0c640802c040e007081540d0054011500992040e0303c100406080b00e44e20301070255800c540003c101810 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 188050890 1250 188049640 188049709
    0x60127020708070218040b0115080601050310080715120c05030f090703120818070b031f050604060314070f080f090f07032a0506070201080717010b030a140402 70
    0x3c540d0069405a020f14001516265458149201e02e100b9040b2410503038941c50000c02100b080307114100054078401c005641c41d4000c00c0116089242001c0400712a0345d1034000514011250300030390054120031328030340403040c1c0180503050000719500041c084017427065002030160000074080c8249446e07100101320300301d00501541004d0740d0040a00f1010420049000d04182c1003035920303191040c101c0d182c41c030f04c03103001283c40b6081e21844844145951500e46500d500308150040742d10f040225440005060340c4e03044020700042c0b0305900c002c10320f061949812005008020040801c1c044860a42507400b0781c0071000303662050300309120040f40d46403465001d01c1c1c001503403003c51061190210110a00003200168000e401c1c000e0f074400c070105200050503800700d40710312039035070031810602c4004010340c01000180e44c0000c152515810750b070965181040c00180070ba104081e941c200109100402246000340c071002045a81014414206603010603010305101d100300b0310301a0702c03070000b0000011 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 188052140 1250 188050890 188050897
    0xc0f0109081009080c060c04061205090c0907050f0d06060315080d050d0b040903030b04060801060b0d02031b030403110c04020306060d0b010504090c09080d020c0a03060b0613030b040203060127020708 88
    0x14908100e46c401d00d425a05914030340c0c880d01517800444c0014121032008451030040e50310070001c90b0041c1c82103581c40800d1168084002d000c9a00b44401485418048808035000d00079401803924082116441c020b4098111070141a49071000e003070b000300902a0781d000044c0000c502659103002584c4a00c0c81d1400e0f80284120004039500608000b100e10500d64907401c00c1140030702c115003c1040703643e1076500500b01c5940788a0341c00404801d00c0544d00090140d4091a40021061486018515448003076101ca900407a4110042080300d010242d9404042002c000512030a0b60300310f185040c150b000541c1d600034048903441c0251120242c030820b0f44a001a41c00a242c00e010600c40c074102104090310f001c9840c0107074403603442086107000d2194030014480e4040103014009001c43c0b8195114500600864110a50446d500308148980d503e8440b10700c02c020341c040c02c80b03820b060900b4410942421010703401843c059003601c8010491500c0803952544072000c2080c0180c0d61005880c040e0803500 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 188053390 1250 188052140 188052157
    0x90204060303020a06050c04080a1106121e01060905010c02100e03100902040f0203070e100905060403030c14120405100c0602040806071e021005040201120504050c0f010908100908 79
    0x303040a000004050300054601c07180e40c07140302d007841280d03503110200000f800340e031103148007036400001c250f0082903000321012040b10b00036150500e0b02c0c0301c0342c051100e0b5840039520720348016814605000f000049101003409054145403104500346404c0001700305203550300006e84201a5002100d80350b07070041102040080000d001d681d1000e95007502d071381c001c0c40072081c1070313010700d04107085800280c0b0580f00b02c0e4030801c003c1c0c650103020010503040c024009141c00b1920300740081d03044003082940d15200900000c621a50320010380c0394082c60204041101803900700100d62181c80d1101000541200b90b50569405884941503e101c0201c00c03900d03400c0300103003d40a188001400301e01104003060300782c03140140e5154a2840c0c000c950b415484031031100065401600400418052892581c104c0354000380140340480e0001a01c0d542d0b02d0450300150703400c540903405284443c0c0182001c3c0081030901e8800d080c450a0240340c110f00503100e0002d2911420050f80e00c940c688104101c80068596a4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 188054640 1250 188053390 188053399
    0x19050108010209032803030b06070b0a02090a140901030b09030d0e0706030501060807090e2706010314070609090f060f030c0302030c060c03070b0702011e060509060d050316060902 79
    0x15692100381074001d60000081d103000f4050340e682401103174504201c0140c0c0c40303c0384c08a40c0b4138101a40b02100101845003480d680020100103020100707000c031b94414003c0030100401a03030360100c03404000c4c03010360740d5001c40e8000d101440e12440725500e000400d411a074005004105568480703109504501c10250703400250b40c078050000403a1000056401e068480d00d071401c110703598865609a4009504031031903000a044480c051082030602c03021903401c05c0b40c0c0400c00c40c801424480004603608080301b45145036100a00400034019000e41c0e078446160804082e100b03003824400001c04032001c50040302c000c1621005041c00a02007580182c0040c5032141c003400100d43c40c1e1402c210005100e1006a109110703d5400700501c1c9000c404542456280c10011803512101d590b4501141c4001801503080d5581e0300c00b0340d001900d01e811191086521400000b904500305420000c0100010b458140110714284c80031000a0b000012207600c2404040500c000da0460316200010306031440000790030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 188055890 1250 188054640 188054651
    0x3040f02010207080a0809040509010b0a090209030c0402042706080a0b090a0f081803122b0f0204050a09020309070e0408040b0406110609010c0e060706200901020607110c010819 78
    0x500071b04101800001e4000c50342488651071302c2d030f102400d80d0b408040065001380d00b00803c028807400780c0d00070400340324081c0c01d690b68086400001707012608254801c1c00ba80650502c1c0c0c03090740110004000e000300042c4c80c204480c80c14503100a0b904c564000c03004089214a00c08070760317440b06c104056000c06501c05220110a0319910f803000c41a00000e144010750381450454400c98540465803500c0c0304861640c0340c2c00c085c0554842e075803440d00944074035046201082006400c8005000d1001d41080c0e0000c0981c0e560b18000500c00500342c0d951040d00c07031501c140f051260b09000800c0702012140c150032100780c140c403582451682845290f02251a0400c000380c001547c0f6000f500180100040382e040d0f604035a24001d0082c02d0392101d0061a000407094a0303c4c90083c5000340292407c140034600000340102c82c544c001c2602c1c0c8041140d90803501d008501c5060320741e410000140e1001c09881e1036101c030601c1d55016a694920071144034184104680016003c4030b41d14201406903034555020f00c83c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 188057140 1250 188055890 188055893
    0x406300605090a0c0608070507170c0601081c090e0a0203060307090507020624011403100305120919140f0103090501050406050702100911040f14010803040f14010503040f02010207080a 81
    0xb0340f950241e100700c545010241e070000e00703130307020b61003161090883d501c400340b8080b0a69a0b0004200901111502c03840007800900c211034020001c1c1800380101c003008291040012011404031489013444000300036041c1c07003d001c800200126030ba004090303400e0260300d07611a0340000e0704040b074981002117542d2414080040541d4000b60403401510032072000840005551f419420350b80d90902c205010500d5442400d407494100001503620240501c500800d540e01d90344d81c10f080040040030801c4008020034014200d2810604100300f46401451003110369241c0021601d524414005180c45002210316511159000b50842c040c4140d201c1c0003001180750a02c0e050700203050030b841c07800c014882c03a5031008452460340300f40c100d201e401554110032501c00208000c003520100b00d44203403040d03c80843d100301c1642c0c000c600d0302805009015540702c5040004107880400c0d02d9000301c03200703001c0d042c0e9605180d800004903500241c01050000c1038144500040c4e00d050625030081c8aa442002ea2000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 188058390 1250 188057140 188057143
    0x30603081206090a02030402010215060301110403082502010f1101020702060705150a051504051803040e0f060402040e0606030403090806160815011b051606030614040630060509 78
    0x52103081c04031003507003c68484401000803800308540c001d0142c3d11941d640d50300003e05445140d800040100041824241d0900700c50703141d00b00394000c40343c00c00003041201c01e590303403007039150714903011941d04010040168000905504005200100f4003503620a041401a03080d01182c82c8990064403003a9510235030b1a0455860f41510413013940d00c114040422004007990041d07a0054103801c034152070310301886042100910f400303080112008070003c605462070400b400030740010415070300582c1032464040b20700021584001c10a621036841000140003031640c1001144c0c120b10282c405503283d0fa61481d05840340c0803d03400c00b00c2940303c2c107020000b00701b0424440000c42c800694031180740344c03641d10721000e0601c2440029400f0038001c80c41c644d128039605a41000301c07401035042300d4419a10100b4540c40e40b00c10b801620009884400c01d0241141d149901c0c03114400c00ea0f01003010714a04480f2600c22071108140d1095180c0143c0d4152007105000c4411580e6030b003201003003105060440000707 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 188059640 1250 188058390 188058427
    0x2003040519090f05010315020a1b06060f0b0301060207033810050d0f02040504021507050105040b07051306030b0d021315050303120109020d1d06060406090b0a051003060308 76
    0x242c14a003050620941c3c02d01c6030280ea412298844081f081c2101c2e00c141040c06034001d841243e041140b400c2030301c0b0224022003002e01010340113241c0040c040b420803118200d0f032155074002d201d401d81c08000400c00d260340010007004503030300040510001d00500c28580e03031001410840b4101c280c90840b00d203005421200403907025540900015242907910424084150741880000e051140c100c04c484000d0b080a4001b107511910040c8000e0341b8070100100c44506030001e9005640d640e40d039904200800400064094000391503041c03d03802d000070442401405422030040c1403c15880304070582003030325024500740d140740d0300a1405009002040100c03004002445441003030581e1098001060700b80401180c140c520171000c094003e81c00d1031140006540000d152031b404a82d60420980540c110540904a40c83d0200142c8a07608001d010002a28010740109092524000340c075030f516603030f001c0017804079002525005c4031207074880750035801840d596002404686001400d070302c50f1822100078 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 188060890 1250 188059640 188059649
    0x70302070608060f030a0b060102251d0903090d0804080f010e070f050325050d03050d14011508090717030d0e010207030e0609040902060d1505030109032003040519 72
    0xe0182c075644a400300058005440751030398054005d0a4044081380424108580c440c9041c011903041802c080705210850040d02d118078400c0c00d25400c1480480d01d00c4500304030b50420049240310314108076002c29100d10414070903e00c1010303000b50038000c100f08601960010840b01c0f00b911582901882c84601130092080307010303250301400c0008110090304143c11401d940000e001010b69040c421142e910810105264101020f03a5a900050301c1c0d072401d4203807030003510a568243c1c0b140117198156082c0d8482e003c40301c0f00441e00700b0051040181c50110b07000d414241d072a0550080e1507030b0b01c4503410a00c103504070002925003086099014000003000703080c01e0b40b10103402c00c4072400d5220032034202d010320100180010210b540100f911f182c9440030b410b035508028800264000242e0009600303501c400f150401640e1178100001011000e50000401088282c0081c40b040c800f5a800419004c004100e2045029907008020740581d030800c1501c1c080d00014000000c0701001d0030447c038881c100f5114 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 188062140 1250 188060890 188060897
    0x121111c0b0906040b16020f0d030606080a0525031803030606081015050315030619140c030604021c1a040c030213050f01050c10231b09150703020706 66
    0x316034440d40008410b48071381e03000001030302580c80e030200d44214a041580d085045225031003951000010500c102420304540d600d00045d16850b1601c05000500002d01007100d0b9440c0c06c00300300c0084d003a484001e1526590382c420300207041400100b0f50040c081c0c1103c108413246100402400c143c4c066104070152040d0f519844000e50ba11000d0300aa5001030140b2041d4540c80700c1e000c01c20702d01410280d074101802c01102c45070018140f0211340b5180044825040360044808038141d0002e86110302c000d02d5401580d17072036a07454143e210b001c0901c400b070704443c000d0307600164a80d0b44030b011081412401c420603905001110010000018020450b0745081c03140c1c4c602140401c146010340300310b4a80d03400500130002c05078a40810005d18030182c41c0101e040c0700e010000313901400000c0c0b00143c0c403c07920040004080c02d403002d030100290060b0010b540500c0385407003442101c0640e02070b5814000188040c9503502c410300004141c1400b29001d4000e0344030f6001c03802000701500851041c050320490366 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 188063390 1250 188062140 188062163
    0x10b0405030f0a0302100c050d150f0614030c1318020d0c0c2102010f02040b0705010c0203071a060406091802040e0705060406081b07050a15050121111c 67
    0xc40e982c60f4076242c03c2c000c015a21840013011500901e42061000b201c40c0d083c401d0074000d001441c101543c00781c0c5104803200b000300750240700780d0720400100b00107031030303d40b40c03c030704e84440b40c000c0301c1c486c0c1300207410001d0421000c0389010026540000c20340c06002846907a40c0000d01504a602c040c3d0807000a1001083c1451840350700c26104008401126400110088041c10703814409604c111a21007003408554884218850441041c0001d000070202400b0081d5a4502e5080081c21a045c0c500d0301c004641007001041c0204404442c2185002d01408055046884100000d4024513860348145c2c409801d240e808080d481d02903050000e46da00039a01448040e0202031110f0b201c43c2c06000f00d50740400c1c10310082c003506225040d40b0f6030244042d07549400070328000d256000b180d008078134201c4481d44001c14000c1004190940700303402c0b40640380140b0103541812000c2c00c1d801c0d401e807298103900b61100a005e050161080021021a0300680000451207078104800a03e5061002c1074a8141c1c180 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 188064640 1250 188063390 188063413
    0x71715060f0d080d09320706050426010c08041511030106050708070b040c03121b02040e031306090f0e01080d181503090c0b03190b0d0b010b040503 65
    0x407850848074a8000c0848a08000d41daa502e507582c1c02071258802010750312465040080c40420088100320681c07001e001e0042c1101d203c2900669500031303040c0d41130b003100d8003c01025410100361001c0d6060f898500003519000400b1b255000300d00c403200612503007042ea40c00300c81074200160314061401101e8140d204446010341d9008d860f8403424081210408200400003648620040c00398a80305602c401e28014168a07504000c6000b91015115984450000c10400010005c00c200f00203a9013406200407101c1c0300403000041c1c0031000603005540f41c00081d40d94000c10720488105000c08161262007a4030350740003d03c01c1f001800340c02c403848582e07003011420481220040341200c0c0440010b00b0300d10101401210f122425444640804130416030110703050340046600702c0e04940304d0750b00040f901d4041c1082d00391228903078131050410724200203008407100c01d00108007000c02042400708840c0105008200f50a0301004d016242907240b00011405507520002070003194012402c646d000002c5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 188065890 1250 188064640 188064649
    0x80603030a02120f070b04061d060405190303020c030d06030203011d0c04020903031e0306010801050a0e06090c2a06060306061e010c02060d0903140319020c07171506 73
    0x9024092002d40e200c2090410a0402a0028441000c138007000504028183d5211480660180e408460064980c80c80702d581d1114202e043d0001e40b0340d14000e00301c60070607855440c0c03943c081c40035001000074144243c0e01814040d8048a03091210744003101e40d95160707030300000020101808128840d5080c00c0b01800c03101c8510a6840201c120100941110745012003004000c1d402a045184c150205010300560720031885024024040e10320340702a80c0345004400141000d00c16007000d807242d100d1840c00c0c000e58402050490b0b00c5003055540380b90580b40d00a0251042c09000c00c000c518440644034880c00c07a079810003d0170030402c1310040710340903190300c400c040d140c80c1c0c102c5642e90072480d240d040f8107150300b40e00800b00031f07100181000c03991a03c080e004615907502c6501050b0b0200e45a10300641010340c0005c10000c0c0820140b002410b5081c0500140d2912964500c00e00d000c0b500400c003443d0501c4140515401002d122900d900c1c50b071814070500351503800002041d0030700184c800000c0d20b070f400c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 188067140 1250 188065890 188065897
    0x20607050c0705090423070906080d0801050d030905030111130f05100c06090506010306090b090a030519031103010e011509080706030f0f1515050f04030b0402151908060303 76
    0xc568010b03044240c14001404401c007002002074601048807a81d000711031191040201980e018032000d449403a082106850a85229030701c90380066001401807844130364080c0f440750655804443d41d000d01220340c1002c840200090700402d0307041d46803050a01601590b0700040420b101e08075000c2403104e6580307000c004554100d00c600b07600302c40c165040c007a841d4883e041555900e8414800000e982c0070a031030b22490051700b40c00480317002d56120f80d04001e10841040301d035403100240005041100303d0355402021401000c0c0c5c01a0241c100b500380c42c4000b07000390060118003403042d15542d00d07903a60303c002c4039503c0d0342886030541500d0b00440d4040305a126036040300944035084001c1060740e142142c00c400405d5040078400485139184450b9119490b24000c40c21052101c07640d03001340f1418021044031400701d001c107140a000c410054003c40c1c5101c01c0540c8c08803500a0810141555540085000c401106040ba00c22500008010300824100c030455100000c40307949210107565050306050f580d20 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 188068390 1250 188067140 188067157
    0x27030307020f072426061302030702070e0a020409140f070f1718031801090519030b04050109080706060f0510021c02030c010603030207440c06030a0c02060705 70
    0x50401400750380804070004030f20304c06003500c1c0070401c03002440907801c80b5042c80c031590450805c1e89000d00c84103141850300ca00a40708401c5085103076003403001002c0d55546181c440e010001e8000350002da410081036054400412424905102c002000300b1841c1b5030300002c540414501054101081c4210320812185021800c251195000d000d0300c0030a41c130800381c0c002c5c030301d0080b020b4507040182c502c0028070161868045103580070345102d000c04000350550900b81c0190f07020f00440d810303503100b9030220000001200d03086450303807150352140d0400c94098803c000c40030300840d20005a940c04c000203079200004031043c60030045d07101c03a107550030004407007070304401400103911007008054400b52800c01c2d010507450600490789000c0c60320700840d0940ba8654000d4015800c00c420130020704d003503001c0c40740380344882005c24444841030600040c2840c0700c05404010a107501c00c543c00003404d0421481003012402040240c4928041001d10094030140310880018001c10010600b501d004006855011 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 188069640 1250 188068390 188068409
    0x51206040f1407090c0e130c0c03120204050904030801030507060813020603061f050c010e01020a020a03050d0209091005011b0b1b070605070302040e01080a031727030307020f07 78
    0x10759107a124007412003038864419036280070b0300000042034075180c071031194825030680751080300340b080008001c0c03810168403100130114203081c601660613500c140303c400c4155041c201290b0003240c012103e00240103a400854000380c04400b4003082c9a0044803030360480703102c2d80407900e005440d80811580700c842941c1c0e081d2404d8410220790010300c0e215001e1640110094850603036080c0e9100c460444c0c2009610001c04070340005000c04a1003820b0080302d1b4441190310003036141c4014510b009548080224000d000c001c00401d10040002c202c0d01240c800101c02410310209003030916445c281c60740644030303841c0452270000c0070311440020301c55082c0c081a00035103a44013036030316412021300c0c1541c9103079100404042002503400049003403142c98000e5070580e800507181c6040c441c41101e00801070300038001a03401a0041000a07521007800b2084180b00600410300340c9a01d01104070100350780e46001d0141040c400d02d2640d07040008051131040e07007107900b00d5906200b48680e464641030240a5850032 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 188070890 1250 188069640 188069663
    0xc030315100f0203041403010e01050f07090503280312060b28090504050717090303040b0f010806071409030f15071103071412030109060f0b03010e0f0406060b070501050105120604 79
    0x30302005985421908a001c0d00100340c9d40f400c40001402c4a00c11142040a95805000c2c0000e4a61040c2d26a000c1d281c10b40c000c210503138403400580080450740c0840c040e80c00041c80c812042511840c1c02130100c901500e0140003940e00c440d9a06140d03000881481b54215000c528400c00305d180100c01c000b03032560b40d1507410b0800d0406003400050900106640300b802105058684420425642580318418240c0616100d06203850f040c401d0f03035405041c40103455000c40c0140040400440c41e02d40149480c100a1150a2090100080c5009140e0615170502402c510b6281900300800c0c80f00380d8000382c8561125960310b2002c00e580d100c001c0039075113009a100344080800206190790650124003280c0c1100d00d04c0300314070000c034030a41c0240c01c28002c990f16028200120096450500003902c0114039442c103542c10f103400c843d071843c1c008140714881e484600109041c03208641c0b003000a03200c2040c1c103c0d0346042c0b07400c0c22806440c0a100d1240540f41882c40c442c101d401c0804c80a005503030240c0750480 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 188072140 1250 188070890 188070899
    0xf1c031b1b06060b0412141534050c0105060102010e07091509020426030a2a0503030a140a0903080103032303070801140f0a060507080c030315100f020304 68
    0x108522821048a41c1c03a51044003113544a1554080d10007030807040b8540c2c000102134580000d01d404100100102688461005907840d41042c1240f640108000040c210300d080b81030b000da100104034000c800444042c0e003024101582d022006001c03030132032807009015644440d0012030803a51252800d0a01d904010014440100203030460002c4190203400044c2c2c0b9501d8214480c1241c0c0301e0b512800d600110070003c04c0c900c1c00501c0a800d4001010340145041c011807602c0a4800b079240b000340b0740d4011000d1101b46040a036440e00150864000782140d8403458150366a00050081d050111007000441000602c60b041034060000c1c50750b4141c0c3c4150385a480c41c0d800f0741c2c5100c5200c44682c094190f0118540d09a80303128081c43c07003400a60780d008000c0d40743c2070700401c000c40c00c0c00c0300d2800341c0e82001c1c0c910540d4450146090441d140d82c039140ba035921080c00c3c1707d402e074024008000c1e03040c04000700703012200d04d03810040c1c281c64404903034101c40c11940303081c00c3d02d200300c4c445c0300a000b40e0070a000401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 188073390 1250 188072140 188072177
    0x1080309010c0312022b1a0f04090b0a060807080303010b0a0f0c1e060c03021306050306040e060f0403170702071e0801050403020706030e0c0f040b01020f1c031b 71
    0x40000d2003030500c0c94030f0b501c02040313900a0341c2044801c510f028002c4068060102c051039a07040c104822040c04026107a4070000100441e15581386141c06541c1d80c01c0c050b1143e0f04e0b5030340030140707094029004041d1803e0103200b0f08080d094900c540e401910a401c000304108101101b164102d500810b07590345001e80c0703550141e4841a0b000400c0c010311010102c01e00115600140e003103045424964217148800140c9000c80885950701c800808040c41800b080e10b0b8040c014621074190f8a40d41440c2d9100d039079800025000c0c0009001001d618000d0000703024009520094280c0900d209885254200c4689900c0000025084800d1030060b808036000b04107823004183e03d41c1c5c0007040072059403510740d10b461480303080d01d4050358100d0051740069802c120b01d91b81845002c00d90905140a4610300700c0101c0010301c001da207003c00910071540d403000d0880503070082000c400400080d0090701c4c1e141c3c188000701c3d44035160700c4001308042401c0104120151210890303203440c00d90030b51030f0150500c0b515410617 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 188074640 1250 188073390 188073407
    0x10f050102100c020c090c0c100c0e0121020c0102030405120304030801030f0c2304110901050a032703021b03030322060e1603030e031b1203040e010e040501050601080108030901 78
    0x108150301800400d944179031601a0650b2041c10703600f00c07d80ea10099006140c1c0f0304030010395035034000c2d80b4083d0303100441540700004428900003440e162003440e20a0461000901245c00c03c4002c0920000f00c3c2481048190080d52095014000359244a403060280c0a51f82c40101c40050010795810b005100041c560070300c508815020390311140ca25901c4040000f84d107000380862100f0306488010482441c6000d00411107007510700d020190604a040002030228081c2010410505485901d4240c1e01229002e103d010b070404a04c101d0182c034444d0401a40782c1004644101842540c07003000d481c14140042120b00810b100445604000d0059600c011003460482c001c0726480c2d1590807244103400c04000048022a01514040c0303041d107540f034040c012560b0b002d0614000e401107400c0c0121258510200804610140c2e01d0303a1500040c4221181148100d070003003589410440c002203003c11610120b03a104910a80003044141c840307400666106500f4841e8100e15130003041010215445803408 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 188075890 1250 188074640 188074661
    0xc0f0d09140d17030c0c0a0602040503012f18060d0501030c090608070e1302040c020615040908030723070503121302030a03030c030e06040503070b0f0108030717120a05010905010f05010210 83
    0x10981441c03088001c40382800002481508c00d103401180c140981c0c5028499045440f0302561345003004101d540301c05004000740040901d0316040481e041e8600b0000f2000d41982800007440f20f641c45a00406d4280140400c3c001950700b01404640072400041c41d01c40c24041d9000140102500d83c03134148000c0006000905500f07804407503d10050040c0c03554060b0704029061600038000900c0c0c2410b6a181001500182510550400d440e020106552034122a001909071900304005c01041d101d03203011031113820340a0403c280008500c0140500400584149202d4200410041c1c4940303e040b03582c00d0610401a615030000645000041c2c02580310301041c0030b00303050124003102651050b5090190444c0c0c00c0e02c4903000050b0b40c1040001d64140207034440d00394848081c41c0d50501c002c0c1c69907401505402007480307510b08440d0505400b4030060356072031601143c0483c5503140520851018107000e100c1d4042e02410000040381013040e0011107000d881060b4010181000340101d02006091403416 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 188077140 1250 188075890 188075911
    0x50a0b070f0f0b3405070b09030403120e04050703020f09010c060b030a031707020708120304020301090c0620011803051308190b010504050403050405060c0f0d09140d1703 75
    0x200301c4000780c1c107000f0440c41600c0054095002c0d500905203e800396019030580000045503803030310440b044c0c000059502803504a810031205e543d07441c09651451289030009003094000d4400ca4001540c4620080c40300c0c0701c25213090296031240082074081c1d000310403001150358010310058010b03501c9840d841c0d46d0107019102c017261001440001c2410010383c000150000f4015003040964140c26080550304003030306100500456152606036030705c610b1483c3d901d1140101c000085015035409420940b001900440140310380d5a40c0c6602500e00700b00803500645600c2490003050044006104110049440500801806130303d40e404840a501107651054403c1c15001e0100708104200711210030803074000d002c207290340440d090803440300005905ca00e11032414a000c020010303038804151000c445080d601c10780c039006254085820305404500781141c6204e035000721000154802c00c41000c94104190206164085206012400f81990006070128101d2030342480300c0c0c040c0308001d40d0b01810072075 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 188078390 1250 188077140 188077163
    0x28021f02010b060f04051e03120319060f05180412230c0102090a080604150216020907020c10030b09070c0f120c11220b0d0b090304030b01050a0b070f 66
    0x3c819070005400c0725194000402e0030b0020b41010760801880c141289204081451070400003a900c4140e0418802c802d003022003c100120750301481461101c40d03d18052090700d480d4981c4a101e080940304091103030884103c1c13039078100070441a03a03004582020314100111310310350054494548907080802c07600b1002c03281d44048026100904003c802c1e05c0e0000d640c40250710704218900311180c0048045402075424800041c00c490000c030f02c902820800584c84516594006840207085140603402c01c0ca640c2c01c00c02c03000e902080000b600402110388448007034168070114215507000355a160001d060b0004070303000b280907003c0201080c9c8503a0800810000030350b038051540000702540d030007049880104004002d258940c07204881c0703003901c0c080030440d08146102d003400c07410014207800543e201280702c1ca503142d00b02d044002a822407034402c52810003002d02540c0790b002d0720041d210492007100209051418019035000c81c0c0810109608cc50a15124400070647c4280f048030f00820b00e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 188079640 1250 188078390 188078411
    0x10f05040f03060203010504270b130209071106130b0103080f130b09100311070b04022d0405090a03050f0f090d060b09060301021c0509030d0e28021f0201 68
    0x200c41c6000558441c4401607101d515120600003a41c00411035410306a41040118000300890000f00b00d04c00d400840c279000680b41d01c2c1c4d40c440100b00c10440030b9000b210000421004d181c0000f1100f600c502c01c041140c01c02e96946240281084c0e030928002c1c40c0074051401000800d83e40006031030031110440c01945440440d40c5040070202040d408800c0c83c403000700305982c891501c070030400700c0300c600307030406100250980c84141014454084001d080d50741800c013040c2591100000e03494408103071494000340c40c9406445504003070180514901c1107003410700180c1843c0022406982050b0b150312140e04090761000302422a8210b041070700c0080074144012402ca940b580c4046615500411001841212550502405040040980340a80c2c010043c0e002c0c183c041e1100341804c640741c400e0010301030f00e46641c01401c5128440c05240f200d0305204044440c500c01007070036201c000641b500c400c0d22414081640301100b14040703000e5804401c03584950040e08850002c9804100103100005850010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 188080890 1250 188079640 188079659
    0x30114040f0b0f2806090e070e01080312010302270c0702030d021203150307090207032c01020d0302030a0e0a050609010e010b130b0d081207140c0705010f0504 70
    0x45505540045410390301c00300b4800c8942007550400341c899a00c2c5528038010307a00c00a04d15a030f0100d004150307039100c454190300090741d00401c00f80c003000c03605108502d40c4254142d9106002d004c1c40084114070000041e154100008480d219401d1540310700d2503038a147c0030004e40d500b0b074000482d070b0ec2d4006c0030010544001d9201c0340e481503094010207600c4c0d80c66801410300d0213001422640656020b01000c90451402c042641d512814031002501d10070410000b090030680a1303801404100c0c008905030b000c03d900031a86a40308505402144040c0c50b500802d16807501801c60002e0243c5c02c40e455085403248a074000759400110041c0214094445048952600410200680d06a0020420b10209180c01e006401c102d0710204020b1040c0800c110003d04000e882c542d13001d050540e103407001803042e1901c40b01c0b00c04481d00300d428151603440c40250502c0e08101100e2400004120b122040340c42c1044106980501c0c40c031600400c0140e08000054444d0704401c4030745028000140310014402a0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 188082140 1250 188080890 188080931
    0x1b0304030501061401080609061c0503160204180b1906030209070206070801140306010e040516140a1208091504350a080f1e072402270301 61
    0x4100c000150941ca8100441e072004c030040521410014904240705595540c50555a0044012034200c17100c02404042d0700030001e8140b00040c0b0600012460790300e0014820010415a4000d030b90a1007500ba108485c81d10741c080381c14004000c501c0c41008078900c5080112031a0550440c241c00242240d165000030340010412146540160f10040c108401ea687c411f800074010001d05556170580728902d00082c1c1c803241d0500508908502c0800018240074017009003284d42c0102070a11595075494080b0304807001c0103841018060104100002402403400040311815604880110b0600a000041090540a5022911903048184000b1940c0300729006a04011651203c000d4481c185003112a0444120461181c120350000f5400001066035107081b18184990740180382d41d1080705000d02c0340303020490101c2920f030480214035442000f03260b0b8003941c600c015100c9001c081511469500046e4443c2c141c00c10790703003c2c40f0031508001020904004c8101c190080002c645d03004545420404c513407 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 188083390 1250 188082140 188082143
    0x6080910110a030b0f0105040b1c0903080702070e0f0c07031205070c0b09010b01080c1b03070b01180606120c05070b0c210f010e04081b0106060e0a0e0604021b030403 73
    0x44005158600c2d55010712401903025402d41e0440660012003001800302c0c000d51003109801400011000d4181c0e040c10741d04100c460b040407080202d090603040085c158081254004003520951030007044003250705805c09c0c4241d4070104a00d05c0b560341c0b56021a02e035002000103c060200342d05a59481d01d00e28011207100300c07000c3e41c400f02c03511b40c00c2c14900c00c2d42401a0335000282d140080401c942d0740d00800a6510419405c0d400740d4810206a50746820465000303005410b0001141d514104140d0400c0d080c102c071600d0002089100ca181781c0d250480d00e8070b10401010824600e4804003a903910f070461b032501c5059040480c144111500d803210092800c03214815084800614041e500c8541c07039400004010811100c96030b4a00454080c0f200401801010080c080150009041041ea41c08481c0602c0405024051490700c0050050103016180204030110700d075030302c5011803414840010000c860000394038000d40c6d120982440001d501c03002404202001c901030404d1440410070041c801075 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 188084640 1250 188083390 188083421
    0x10b1b07180b120c0609060c0a050c0a0602010b1f020f100c03061a04030b1b1201060311070b010b0a180303020d14030105031b010e03070611070510050406080910 71
    0x5000d49146508440c2c44000315403250115020b01d0040210000c3c0c44941801c0c280c0741c080d51041c912001a402c0c4c05205d419030990f1140007118810070001160000160406844541c56207071600030603400c1c2e07861628000c2d04071901d640c40010804a8410b10031103c0e20600540305010b1203c3c241d54281005004040000c94842101440b21503051045100528030700355981ca40d0201d0240400b51441541300c0030b05002c0184020540341d199001207440f00c0c040c61000281e1b43d030341c00c0d40c4441481009224000c08a0b1401f500c01c04e80c4044d0008461700c880c1e11046001e910ba0900001017401d0304a070000c60204240546104960158442c1207405180a50003e100500e9840d00042c103000c01ca0320010000c4200303000401243e100010840030061007052104001c620620040f52260704c245a0b01780d00d44980403001070300642007591250740118900a80380c0c41500d42d41031242d8000b10415050018a0070001006030b81d01c500c4210350015110001d441c2e801e15100c81480035540c1030607419402 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 188085890 1250 188084640 188084669
    0x1b05041505013006120b090312010303030c090b0d050603072336041e030e04050702121305240405120708070603050a05060d0201020c19090903081803030f010b1b07 72
    0x6d0090b00080315a00504110046107415100110022695810710004051649505020302c0740743c0550044009440a2901d0b82d0301d0b0b0366084c1500303025040a441d070764001d02485030040b450050301c15402e03808040c40e081707490317400442c03100344910215440700e60040c0c240e410315104079105c01d00c88030950352000744244503580e0030581070203036849411600d1100740103800440d002c00a03410070280c000e03584084400050030341d02d540041e41040b040e400034505071000001c075844d5054031480b80f101501c1d0700703540516400307100c401e1034034040b10140a040c5070084140010007a03407501c010b90020801c42c0e0801d9071541e40c2e0781c010380c515000d1183c10000202c2e4560081211100b0b042c8100e6610290440d03402c0100010350b00040e48440600794098001c9400c5107280d410340041c3c048550083c00c210008002000c4d0b582001004118142c0765071116176412080c0102000c0b0000c240c9015111800550301686d28014814030350b0303803004d01c0818480301403c0c26a600c1803820b11a1a00900c020080c1540 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 188087140 1250 188085890 188085893
    0x4110319060b04080f19050a060c0e04051006030c0318020d150e010c08070e0a0b091c060203040b1312050304031e02070602070503030703080a181b0504150501300612 73
    0x91200d03c0e588030b1b403148111001e0030007054000440c03500041d000600045c0e1004840d13803c645503521412826041410001801001c10307540c02d80004030345075554200416484010110240d80989003a00b2803c442010394001501d0203010380fa0007248a501c500c1080401c00d00704009851910f10004001c0e595680e8802d0215008029543d0017161403a10108100000d0005405c036012801040d551b40070110b5001060780300d0047c540803103c5100b81c104664040c6141c0b0350060340c000c036800c0b5180d40018000c601000c141c1c80d4a413001503481a8664132030600c45204441c0e0390001002a810082c41d00b02c2808a04140d40c10a240980315a0241c0070042c103014010b441e003061548218040e50081000d940400e601003c02600038100b603001050803084c41180ea0207080e600080500455402c5a507418603004041100d41200d0017500c1c18040d41a030420403421940c19403043c140403030445010300044c0c0c030b429662002d82458005181d40c2c1c18814159010849006402c405100341c5070041c14030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 188088390 1250 188087140 188087143
    0xe010311040b011b1727060306030d080619030807030e030d020a020d080c1516030903080a050402011211090117160c050a0605101404110319060b04080f 67
    0x351816060750103010240800000a200c03124a902c01e81c0d0043c0c8591320f40003004480810210140c8100c000c550b103414084280c1c4407000424485d409582052205d422824200b98040e2841140c0040c0a0041594814030658042200400440c1c0c016216810a0408000c03680d48201460140c100d1580700e8a80b45400f41a200d818400240300b40d204056906100f5400203004018030341c16203055912410034581041c89006800d00d0030302e14004d4a20300c00003d440d214005200d6a010104070b0040d45d01e041c425000c030b40825401400294080c00040c140440301d80180f03800500c18548907076070940107400c94003120f0100740512800ca500181c00015582e0065842201e008108203c99003030404240d903042c41c0c1480d079060000d00058407485024000103015582605410007400d02c581c0c5441c03061014016001d00030446035410110302e48250b41068419001004541e000362459a1240340c451908111000690001c035038a1b400045140701000d40900020702c0e42200a121184284c0d100cc2d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 188089640 1250 188088390 188088413
    0x913020d0513081803070306020f030601021905060c0903032206090504060e040b0415020406030504121806080603010902040906050604110a0c030e0d061803031b1409040204030c0e0103 81
    0x48040144000d07001c00402c01a1040b9845900c80b02c1d13145404060800220342801b50591003d481d1520205450b038501080d000110f11a5900b682520080200c240899004065080000d8203661144e000201841488030060044600013011a41000c4000200e42704101c030007084544424030f14a070030800030f038005000030041c000880b014090781d0300707056070104190070003000601001e2601001c24144501d0321807803490b001500c2c1041d035075a9100e06019001d0501a0b40c1168078200282042d19628455824a40c02250050352002040c0c6400d004841c4403501901d110350656845008100507607491084911184c403a40700495207141030310410045030820401500c4041c001c010501d407469000c50400c5d111580b500b802c1140c4c0c40b400010400040620100800e124078254824003c014403d440b9020644281d03002d00c451040300300344105001c5940020700102c0c0302c45000780c0134001e045000e00520308000d0801402d0980d25250340c46805810b5200854090075640140300388000c5c0500d1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 188090890 1250 188089640 188089651
    0xf0f0203060a09060e0316170405060c011e0e0c19090903110106081c080403050909090f25050108091507050a14090d060e010902150a0305060d0503030705030405030913020d05 77
    0x1030750420040083e019048a0030407030007412920790748d0350f4401c600000c4054602500c80a0449900d8060745009c442c020103850326040a01c00b044150200c0039040b5014102c4c1c000300c4100509540b040316818080c1900c03a4070714050340070070000320204c0c010311207205070b40296009a40340185016601d00e85400c4803015000802310b0307080340645100d5810407050640301400680b5200c8159036950900322050700600000702c3e80003140d4000e002c650540050030904c13400c40b00066030904280040131541c9240c500c400404002c3c210300041000398060045558444041c0003943c0340300480c80b4031448011021150000494000b044001c0042d510401702502c1c1c90781c966a45d482c0c400403d0014006816202c0c00410540c1c4441c2c0c840e100c00002c0d08004011540944000112107600003000c9080d00505914000207181c18005000380c41d00e20354640700c554000c400317940703907403500700c422205503000400c240c45030300c02000034600355107810000d40220340c956440145c540748218941415140081e0a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 188092140 1250 188090890 188090893
    0x10090c0f0315050a0e070309061e0b0a03020f0607230f0706080108121605011401170102090a03080f07171e1201180b13020d0b030a0b040f0f0203060a09060e 69
    0x609200940300c9a20060546040903064082ca983d11b88088001d0400403900809070b80c18504089018507501281a64507665001c09200c2034131395206220104079030b440301950000342075254000c941005002002d0046c050b4950700c1d0782101c100c0000702c90a400765583c8086500c10001c00804080038003019002e03200702e2401c80c0040d4500f00c4c010341e07140c903013900c0030003043c10010300d06140e400310740161450300b0b62042c001e1103507080307a4000c85001e0702c003440b80300c1c0d5000d048034900f0041101071007195446c82c030003070011417020b046441f00c0c05550014080302c12030080070004d82c00130408000d540081d8050000308140c0d03030008007000400d54404140c000c01200014015841c100b0b40c0d1440c1c1074103651542a40741e600088425008014141744c41c603854002c0d009942c030b12000c6101da0014a0010f020744c2c1d0a0201045100038181e03113101c0070601400c0c190307014010800065041d02510f030b01c1e9004142c840500e86149c0c00003818440c080e074030b0303404455036a2107060070071108d405000e000c01c00310340 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 188093390 1250 188092140 188092181
    0x302071d160c02040e01140c0a1d0a0f0b071b03051b190e06100207030b01030303051302040e0102071b0b0906030406020d05042910050910090c0f03 65
    0x10640c0e69600c054001050300720040120550540b0031000c491000ea0020f105004400d440103507a030081030800b030300e100303050150300c005010b0603c80e0f07048a04100c01d550712074040305911182c2005040d28542c03850b40c05500d4100010314955403444105c054003041040961395680c40c903102c5c04a00c50400d84031040d14070128100041640407030801e80781c0582c51600415015006c000400500428031071740b0354516000b1000c01c00300c0000036000d2003184290343c02c00d180c42081c04241da59045900c001031404003504014000607100341c0100703400c95100603104829030020340c00034050790303c843d10300c20650303601184480602903c501d072210b00c0030824204295150420000220a00c138284a007030050200001050410019034101d4030000d1112400b000a07041920746202480200409a08030040d400800b1141d99505120715024810700d0002d402d000f880c00c02030245400004200400e0121800380014400d071850140c0032101c00c03241e0701c1000410240e2801780403a14003220540000e41c848 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 188094640 1250 188093390 188093429
    0x807120804050105090111070801091401020301260a330e060714040504060605040807080115050d060b19050a060801050907110f070f03030305010b031b031302060c0a030207 76
    0xc008450641d203007031800940d1a20440016503906118410449485c400c2c031000244410b4103500c103404991084d070f10000c03131128030890103081c5d01080c06200d9910a0f840100a50040645400d12a2038880c0040d102c0286040c1c640b10040a100b032140507040513103140c0f0490702004114540d0360708005401c1000003000502c2e18558079100204043c1c00c0c03100c145d002e460307114102001d4400800004200348816511000018a5904184202c00071841400320200340b10784c060003071032503900800c100e01400a242404011074220b1f500c800341c40080d6280c01c20f225070385500408100f20441d80c0842d509c0781b8680018000071440540c8000100010800140200e07910551540c0e004916450001d9450945452031401c106060440c800d540c8144000040d610389200b617150104ca0003038600300490703039881078945000c3c8070071940101c1d2014640141010f20400902843e0469550082c8121001d61940815000e41c4080303a41d0b0001d52100098904040d41080900d01400c2603a2442c06000c82c1d5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 188095890 1250 188094640 188094653
    0x30d0f0c052d0a03021c030e070305100b0a032001050f12070e040b0102070902030c091c03120b010503040f060608030c100522062313030212030c2b09050304080712 72
    0x2031b2204d081d0022101d6070990005100340c02030054a0300d2441941c400d00d580340f410940d5040901d280d0303940c02c1d050881c10500c500d45407400030b08490f007020841c842d00070008035502c8100c490140080c1407040500000c050740d4080700290400000c84000c000607070030700030406005400c6a4008a00c0ba0342080101c40c2580d0303000c03900404542d509400946c80c0e854600282126002e40700703045070040940000b0b5a81504a0003031401c220b8001d441c0c4a05e00710748803410720b06a60b000040640452400c00100d40054126960a152540100c10000e0026242e04100303085511200b0381074217651000c3d180512050091003074640028414030401a0f0140082e10040a85480c0101818140e41c500b8080042031010701d8890320303001d03807900141d55403424202c0031484051001050340148a000c064403820303229041200e000d2014403c4417401c080d0800100780110850031440d042c0c0d82144c0c100d00c81c40e8515802a00d0580b4459409981c507941013807042c519052060f030055071440c0c41c40640c000803980 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 188097140 1250 188095890 188095903
    0x705030d05120a020904020c07030c0f061d030a06051008060c03100302130b04020a050c0c0a0506030c160b0103050607020d0305010b090d03031d0115090506030d0f0c052d0a0302 78
    0x103100b802c4169a54030454400240244e5000031340081c00003480c60300b4058041400380c01e8a2040d00b00e225400c1d1200b5141805194501032a0046203142d5079002d0740d242e00e00c81031081c0305401002c03685e00c0d00d4281d0b02c107410740f0b809036003030006950a0300041c422100e00388001070b4499504a621811850b20525520768200140b2020b4001c081d1004013465010050304028002c19002c0c0055580340e8040390000c18a6000c420340380c5590088c0c3d69030300068905034241008680009049034155218411485081d61080c004060480d00b0244004006034040a4150003503008601070041c43c90302a4010b41006007041490042629003030060000c40013810070795001e144261000b8800d160185001e400400102c50307c070310040441080501007407015084001703250300d1080d80d080742c81c0d611040042071764015a1403a0f81138200c039000f810b00e07034800c04101c4240015071800301101c4c120f075100d540c00e010b100c2d03002214075405c01c48000d8101042400b905040200040200021129610001d40300c26 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 188098390 1250 188097140 188097157
    0xd0b012604030908030a2313090203150a08010902090f280b13060f05030a03050405060d1112010f060c120f030e070b091008040b0f040204090605090f0705030d05 71
    0x44180000c41c1c1810300c50401d00b00644224400c881d56911150005000b242c800200104040328031403030041000fa0020540c0c501c0d181000e6152010703801c01501c40041d4000421440074802110b0f818242c42d5100301003030008000349800015200c180d4018020410401010842c01c001003601380810500044861101d60042000b81d42c200041c0718013042c0035002d1400c440b64400c8900c040103181d0b15203580544110b41da52101554040c1d038407411b058880b000c0180c0a0013142043c00100114200540101900c040505002460780c03240425074600350003005079034610350410700051105120207d04000944424101401e0f070603755510300450300e003591480e0b010008010610b1070414025044181441c1c41d035015100000c3e1501d4461031070b81c0110100c0c0d48034408100c0310aa82a000b096250b00a603044092100243c0c0d680f001c030180800042d01c12a000703955030082c4008207005100f030b00e00440d4802c02070030005092a00e50752800d1616003050384650070080500c0600e503080000ca80014 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 188099640 1250 188098390 188098457
    0x601060c06090605010611010c0207050105040b13050306070c050f0102070b13020411030106180504020903190f02060708280f1409040608010b190b0301090207080d0c02030d0b01 78
    0x2189145011406080d2002c0d00410050030b04c00046031068000e1052101450040006c2203060a545012691000039105e0940450002c003c14421803d1220091000c102001c600300200b80d44e50011900d0210b0845510001649400c40301c01004010321850840c514072900a5040c044940c880c21944100a849082c2b103c036a11481c008545070398000380c034102d0001c0491512980d40d000b010700341c020300149200711500a0b56000c07445240c10b100f40c511402e4050002c20701c0e85001c0c541c203d801000c0070b500361000d045400f150300050b503ca20041003401e110326013041d1a800020740c1e8400158115098182150f80900002d142560180d42c81c6400007007840c6c4240c9041244060b43d0540c4124192590000c0c01c0c0b807c0480c415005404c140340030001a01c0c1c420030805009180203040b02c442c020b60b01000c00030001008540550b8002c0c21080d400740645c1c2d40340050f1113010500b01d07200d0302280c0000d40c10104078076000303444a01c10307114800800e080640720980d03410f038030020000303402e010b6050701d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 188100890 1250 188099640 188099657
    0x60102101d060a0b0f0a0b07020103021b12070c0503060708040611070b0c040303021203070503011e0b070309080613080904020c0a050a05150a0e1902270a050f01030203060106 77
    0x8011111080840c00c1c900081030b03940c641400d14401c009016154161402040340c039440d80341d00e04190200d20304507041020303c0350501081c0d60046000e584a15901c1c0c40002d0346c0d180700c0c050307040e044c0300701540700d00c2c800099680ca41c42481e2001605101d5481103200b500603108205126812100965015522000c0014949071038500320700a8040c07507034080d146203107490030018051400c1c0d004200345e90084c0c00303c1d0550f154a001c64401d5100469604002480c1840100315150001c580b545c1c0c1e4418000e43e400e40f103502d038090316006420014042d00000d810400400251505219040e040b0404040800c1c400485484661851091401d07440c01683d001411500100e4203112844c03da80c1d001c170580d0490041070a00540d43c01031600da11120103407107000f0600900b0980314025443c903d601c0a401582010051700e0310200c11020141c2c0c00c9400035802d03035000b842640f01562144c50402004195092440c0c0e4041101c2c0c00a001d11101c0001704c00605c05a40c00040503411120b02d40b900003003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 188102140 1250 188100890 188100911
    0xa0308010902030631060b0c07050901060f0806011b030807030c030b0f091003020604120311011b03090201020f030301060906030f11120a020f030103060506090a1a060702040e03030702010b10050306010210 90
    0x2014810300100c417480724603000c404102d50091200a20780081080d08803064240c07140104440c046081c484c030700204128a00c00300c1c0407800b4402e180d510440506127840c2640c2006200c651a20700b040301100054a03200421007119054400c02082d01054503041103018801d4002c6034280c0340b01c18055200e01c1c0840001000c540b40c48200d10007840d406040c650301c4907540c041c4100750b65030b040c0c0201c0200b140c4c002c1d500035480d0140b150700282181c00e081d900500e100004140e00401000109a045014481c0008a0010208010750007009141d41d0b952006e03240c820014219424000c0612000d4106540013102e4001c46095600b821880100c521158464420500081c8107150f800346544e0710200000003440090f6218601c1b4610541d07684146558001a07042203c009481012800100c00e000566908080b030142003034502c003030000155071001000c1c061460f04111070410041c0c1d12102a1710203424110b0074654050300c81d041c07440c10350800e0320010307440340c0d0318503d582c03034a5994030400300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 188103390 1250 188102140 188102209
    0x20106050907031a1011070e0c07020618030109080d110702060f0a0c060908120a0b0a14040209030303240604030b1b04030209191104030b0c030403051b0a03080109020306 75
    0x703c005100805e0520904480000a8220005800107002a0288040000307043d0b54004101d84152000c0c071456151861300e0b800c0080642101080c074000c00f001d4642c01945480c02d03c29104140c0c083c1800a80703038421001408103461104e1002600208284203400060b210a0156a400001c41c00425203900700c0c0501254102840100a0a21818960080d082c005400004c020082e40b07480c5071821035450016880a860500b01e0842d0013507403040080024503550135140000c000c008001501d031010032000079256400c1914604000b000c900c0e00007a840c698501074505403401a10307910b0505146444101944100500e9403441d100c1100c159a00d5001d0081103c01440d0700070b03c0c850301d40c01c1c0003181e96040c00ea1542c980840038508502d03540b4040d2000160340490740e0069500070648d440d00d07940c206a80000c5d00c100c05014080c0320300441690b0700308001d260495220010200a001e41c1802807122070103a0020b4003c83c810403d100e10f80d00e886242008211544e90104005d81c0b0b9001d101 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 188104640 1250 188103390 188103431
    0x10b0d0803041704030c03060c080105100c02031014010807081c0c0c050d050309090601090b07030c020613030b0415150e060d060c020c01090f290c010f1b02010605090703 75
    0x8041c0d400f0020703001c010450755a03840c3c0107803030203107508104200c00d00c402513551110a001d034a51144e41d02c00e4502c505072082461644c0c092000d8161500120508140800d50382c507801c007110103d0b542c3c3d0040c8201e041c02c104078001440b194000b4081103c0341c000b451582e42c541d044c10020094204005024001005404001070a001e4040c80c8102c156080c41038690f00040a454400da6010003c905d880d841581c956041d41c0c00d00d580942303030401342d40e01a990700400c0142241c0100c1e092110052101d10340403100021070044080700c0c401d01d014035102c0840d800d040980a01e003494001310706a8204140704150980b54a00003120b01920f03200002100000e00940086c4031605201e02c070821a903000c11040c07030300102038903102d060070348450580c9080c400c80c1c0100340e0302c010341c0c11640035a5280480494007422000740383c1403030119402881d81c00e40340364000845400d0b8072000b841c080c6000310001d40c00400300c244020001b1a0070080000c420260141c90b0b0b60403d601d8040003400901720301d81a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 188105890 1250 188104640 188104673
    0x20904060b061303030305071823060c06040510090f020f0f09090705030d0206010305120a05040f0603060e0c0a0206010315060e1510140702221401051002010b0d080304 74
    0x968840b0f06031404164004000e01040700000d0030400800c030694001c10304e00d46036034113010101d401181007000e040c40398419146c508081d015581c1e0340b694241c80b00001850380442c01c0015005a00d0203003402854100f002129550080c507202036480815610122540141d034105c031005400d005100001c0d0070226588207080d44224848148001040e0004919080b1001507058800d440c00244050740c407520300340700262060700048504040458003c00512000c09241065421700e41c480500500d961034680100001c2551900140321210740d801680c0e038010500c0c070b0342c0c5d46041d03c80380c1c0080d00d656040c4001404c9600840078050145c0407034001074060301d188030500c1e0080c1361903c444829154082880e9020300c04044c22107990500c90400d41007080101c0b1f01e25464a6480c3d801d001c00c14184a40d034050411004116406288483c003a0184078140c4021500b4554103040401c40074564001321607055a25000c0a5180343c0c80d5a070034800219048450f5644956680c1850740314403110910 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 188107140 1250 188105890 188105899
    0xa0b0d15090f05070809010e0a0b131407050a090e030702010e01110a05012012010b070c0f06030f06082e06080106150905030607090b0c0f070b1804090f020904060b 72
    0x8050b0002ea40e580c0507a01c10310360307642c03103031314580360b07240c0c0c00c1d08035100405004202d4010300032002c085611403611a80106441b00c81884692030782d01c60300300100700460380b0304403608041e07000c004d00e240484c40107000d032180300f10800019200b0304d6010785c1c0c0d100c3e0705002070510016a1411926070301803107920800d411481c2c15200f0484042c540603000300202d0301b43c801a1007031244c2c2d2107c81d0b003010080d603505804101c0c00101076420301c02d080b2015080304004840c0700505076004101d24540c0303000c40b0001c05003901c0205440e4000c0300303440c09030703006600002d0155100b0710750703c0590304245405504240c560584040e2201c00808403001411031a04020101e42c00c118000406880000003480342000c19904d010045485004040d203402c0d00703549041c009002142c1c1440083c00b0300e8000d24103d110802100e80620700d0ba4081c500b0700707070b082d8440003a20b0300109106c1c11191501600780d07107402080300c04001d681090f03642c441540d40501c0c000313030240c10355400043c100a42a4031000c84842d0042 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 188108390 1250 188107140 188107151
    0x9060f09060609061a0309120d09020916020606060c010e01060e040201090801090803040605070302161b060201050906011502070f0f15030b0d060e0a08030f0709050a0b0d1509 77
    0x1180054600d104084404a02e4400d0001d0320010503c100c2c1c0568403002c0804100007074115100724503410151030411306008040010504030944801080b4208605030041080200c0340100000100b000380044550011103007400201c07540840c04a40c00328040321040d0310b071007500c035031640100f40014449125629044010600ca201c0d0b80d03500307100b54801d90300c510f21640c490a000f42684c40c4901c000307159401c184041400038210b908280c0d0301610600c0c0c01428a09001e00034114040884c00540c5e40124440340801d00501000800d0003400960000f400141030031000c090f654041403050b0250050212085100b2a02c2445018018041c1d01d81c0014590344071400c0c04103000c15446504041c007440f82d8042821402070046000c07901c402010030b034104002ea110900036200d10150941d05000d241540c20000c0c85800145018011921440d607141c03900c4030004d85020742c00d401581c8503601c624010071110844004032030300c504040c000801c4040503040c001340324008641000c05542e040a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 188109640 1250 188108390 188108411
    0x50c130b0405030f0708030304020d1104050a0b010e0307060219020d0b0705031905010e19020409021803010c030501151107090903020a120e060d02131d04050c01140415030906 77
    0x34010304103030740c412000e030348461001d1066036550301d800744110b040d00d03081480090090301d4181c801e25801ca0040721841d000e28104000901180c404560130148103640e07401402080d40c3c040f2401d85201c1081d0300810700c50b0f091450207943d40c2c501100a4801c40e11000d02c00d8110f490303160746a6941f641c8811481e0907410b244070b02401e1a08101c42800c610b121808055800301d044d8000c2504031400c011582c035807a12b840058104222901c3c2980349070540802001030320048520040603841404c01c800107211080808041c01d40341200300d8072081508000c01840030f070410591103c44440141014807101680304241c5062420310381c0805d00b16850316062030b00307241d00885d180504a1040707901c900002540001a40d40e040390242a44e0807200601c604403011099038020184414002d8000030110b5036107040b07400b4a6050300c0c0c0c0b0488840039070103200401c0030030002c450080500742006003c1e4214891541040d00692080c0c07640c0c08103001c415450a4082e41c0010901e41c4c111506000c0c602c07d6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 188110890 1250 188109640 188109659
    0x110d1808070c1502030708090103020d110408070512011a01050a030e1209090a0515061c0504030e030d09050f010503130203121b01020c1005040201120e01051801051009050c13 77
    0x40d4030802904148a5041000c3c1c584040308480409600620003420070f81d0100c01100203402607044001019541d001400d40c000c0d031807020b080181400001420802d003014280f220141d000841e880c0315a040c0402c260007824503000040d0200c07028a0040d0f10780a1107042280039024400f64801d840c001c000c018882c6084280c000c1491500948402c55103444102a141c2200d078200d41c4c01c13000d41d10100b0000c40d1071070140d0060000c4003c0f0404c020103020700c04e507214100c1d401a030b0100c010402c2617130302040c241014000ca403604030303130f83c245145900e01c7d000108140070060300d41c460401c20b0020000315400012018108007640160488107103000c10314141c010b0b503000300110b514100503050200c00a660500864000390414409010034103036140755103026141c0600124180400c06040c0c42c01020580f00f070280c81244c160011402d070500d0382c0750084d150086055a80300b64109010000070112480081084130f14000000456955015200310280594908550b0203406070a000444021 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 188112140 1250 188110890 188110913
    0x912100f0b0607030c2301060e130201020c0907022404020118060e13110703022d0c09070203090d0305040905010b0301120f030e060c0c120f1b060d09050a1104110d180807 75
    0x2207282707100f010f85980c89100070380000ea0350001e005a000c881d0802281c2006034207150000b41900403518804141c1d45c43c0802d000100043c41750380a221070400056603848141545000800d0a20b045480e00341000102008641c54000d402201e041050084140301d607809040e40c43c0b400441c035a211030b01403600a48036840601c1c0421400400c520558521852a54107050707180c0540c001d107482d404010505c03003001001081c280641c007081c818988180c4400b240f0700d1445101b66a40380d62541440c440002f10780c010380010601140520060160503105c52140c020f041d00810710b0000004d0500d8100c40380090400d041e50042c5c800f00e11150b0344000040c112002a0f001c0311200360090b00b210b1115503130780804002d4181d1394804681282d00810002411010001c050702403403401d0818480704081e600b0714001201c980e405540700001380445001c00250411049406202d6003403c90014980d038060707400300c1441700d541c0e2541b4005080c51400c007500820b6100440644601c01402e04851490 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 188113390 1250 188112140 188112149
    0x30408041a28030605090108190c0e0f010602060c0a0f0c060b0310020d1d0a030513030c151704150e03071e0b090a02030d030507050912100f0b0607030c230106 70
    0xc4c03c000d404601d510301000d400b03050710b18010092902011054121007071802c200320546848500490100d026100148868450200041420182c2d49400c2d8000e1800000815100d8080014000054129030009501000b0700240c80d1802c0c00010604041006050704502c1681c14480c61002144c2c9040c19006440ca101080c0010403000c030346200d0340030b40302120304e001c0c2c0d03041e400404000001a0041000e03007108885101c103520702d191240e4505103002020f41003200118409900d051445600c445200ca403844034001c00401ca05140d40c800c4030000c0070032040d8101507160420440766240400c196045141c22945080440c1951101582407000f1800240c640e45088400208802310008146990a901030000d048004a0b20700440081c0030240442041200030451300388540e407018215890039070b2000180052410b4000c6080884050841110000e0b0600e00d003e2080c3c5e44840681c4c1c10315400d4107009221a0319441c0005900641c100a6060295200e100391441d07801540b00b8020b44 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 188114640 1250 188113390 188113397
    0x10905010812040b03012112030b0915150c161d1608010509040c03200a050a030201020618010b06191805030a02010c0311100b0312030408041a28 64
    0x440c8203600c2c201c1c0300740d000d844c40300c000800040207030203c1c00b880ca00740342c1c1040480c90902107a580c3d03200700a001e074562500c0002c0c0c40c1c5403100002d00d024041e0a41040c0c103c2c50b48000c0030700100100780d171404151044401400d0104130321400e0507082c071034041840002d14010b48000d4035030490120010070301d82141c0c108041400001c0a0f00410340c100d42d150451611001080e1b86007404004075580010011255441d80150000c0010560041021100405640f00c14124209001c0c000010074580c0298131070042d14104202507600031400035004004e003010a444070400d01c3c1a44d014229010020390415030005807a0100c0a5503c104140c00700785541c1d10701d141c06030300f111030404451070250fa80d060308204c12280c0150b009950031505c080c803038100b4002c0042c2e5007142a00b02800344108814442d1900c035558082c0c81c00748a149507001c070305d101050071410240c13284100d074080c034040d1a0b500764200c9403450f40580450150341c000762003010300d100500da128101c200d0080d001301c1e141010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 188115890 1250 188114640 188114653
    0xc0504030b160210090204020702060715050f15010c020a030210050409051003020a090c18090204060212030f1303050d05010b0405040e01090b1b0f07050a0201021212040201050708120109050108 85
    0x58010703020700b02c0000e01d1150700405101c05008902c200610300a0001c0341c6c0540c0c2081804016101d4001400a150060005046040d100204001500d0700200040c0303074108902c042120000b080300015142020a1030080c8084c1020320202d5000700c880e820195204030b00100100311168403d0090064921900051016489405080020000d5400001d604c00d14581c030900590426a200480c000c14030703e040865040c3c03440b4003103880f045980111403800e400160078041541c04200244040161508280c0380d4a041003001d0001070000c1d00c0d842114810400281c24548500300740c500f40c40314a9020406541d444410a0555216102c2e00d80628100068071032082818490310103410b420504be040f1903945c000b001e61400e11020014225507006001c08604428560003500720b0030310441c02071100307042a000181c2380024049031004421001c11104402c0e80803064503e17001a03080c2082d40d00c0d0929494549071a00528078402318481d11540005410340403a04034030304894040c03098840 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 188117140 1250 188115890 188115901
    0x8010207030f0309031b03180b0c0d08011811040e130204110702010c03050904020706090b150901080706050a0314101401050f0301120606051806090f01030b06040510090c0504030b 79
    0x1a142a4034000d404901c4006c0071b035584121a1b172401110501c83d14082c4041d04520441542400c2550421445c0300c038041410085240d00300040d507008402c50030440d155600d482c4080c500200c26490441c80d1300d446001881c2022180400d5501400d41c4000e620b01501e1704590b003402500028a00742d114a0a1142d00b4001c0a440f1048950342901079403003e00112140e201a2407660285500725042175003088160701188045c403400800c0c0c0c1c0300b85002c0b440b42c18000203134240b0507e0b20f682c0900c5075820f00010408050300068480864049050141d20f503484010103800a145441801c0e001042c01001c021410030040d00c01020b81d11984540001005d0480c0111402e000b04c222666548000700300610603003040c01440d032111881003030003044541d2224089540c0d101c1e0180a050018038810601c03840b403808655449d404816901c002c1501c0d8510340740c0068246002d0130840c041da681e03601040e1f8840181000c4c0000d000205024001c4070b81c0020000c0c01c65005100c16240788418001241d03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 188118390 1250 188117140 188117147
    0x6090d0f0f150c0815010f020f0709061d061c050309121606030c090302040506030f0708060708060102010b0a05060d0e07170610050d03050a091e0602011a010f0c051608010207030f 79
    0x307020b01101d0170842c040410400040d6401c49114403801c1c198481c140c201c403003c032400c00c6100b015003003881001c14100d14051082440c00505a010448000082d08000b81c5896030f42c101411560f101c03160004203000d60170564218425000000c0c0c1200c01540d0081112000180c8400c11030a00c20640860a03038400c41102141c405005c040300144201c1c10400151801c0d40280c0d0300200c6c01001d9409c860802502e039444c1148a601810040d0080c2003006407440c0c004501030fa100000380000e011142950300052403517242c41c00b8041c8034103404107921480c0001c2d5481503040f0005401124003180e140c80c2105a0581611f0700841c0d076104003400507541c2d0800704040000c43d10068042d1a00300c03040d650958054210100039010814540c400188403084a040d14a0700c0c00303460001070000342031510082c00d5440b044002801144000440d91490b43e1105130141c684c030b00361400e89510203141c5002428071020b8044480090044100410b0000040d0300503d581ca1294403103680c010185001603 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 188119640 1250 188118390 188118407
    0x3050a02160e0a020a0306080604060b01140c060a02031518010911190c0203101503020f0907020d050310080601030c05010908061003060906090516090f0b06090d0f0f150c 75
    0x80d01c40080c40881d403c00f016401030520054507082c0410030303d403a010304901d003601c12a0240d07603039521604045107550f008081d0240c00d42001803214500382580803541d50342d0340301038240c170714481c0e0002c0012756040c0d5444401aa5210007840d08000b40000a01403500240a0056038401c500e004440c030105601c0304115998107554036400411045841d5056404041523902a03816020b507150003004100707248200106a00c0c8003480005660950040c0101c21129120030390180351420203100c10380780c0001e080f9465504610f4110390f40d42d80d0020030800551285d10008030b610800001204000005200105542c02030740c69040c0c866076904000d607503100648030803c1e00070b0395640500200360a5007080100601646c004201c01c510740e50742601d041c08040d40c40262806401d400e120703000d1355024440488044000070302c1808a100e001072081e06c50032003a07a2046800601e45000c01c1190318121108607080403800082c004030b801c024140700f1407580141e0741240f51500d8041e0850144d44107 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 188120890 1250 188119640 188119649
    0x90f03090a0b0d0b12061902070302060f0709050d050105090d0c0804090c1b051c03020306180a20031510200a140f06010e010605070210110a03050a0216 67
    0x7604400d440c05030350700e44540c0143e81e0703001c0b00c0d902e034495041662500318040c180c08000d40b000301072a00c0d00ea000d21400d00f0f21100d660020703d004000c070784003180d800110207030801c60340c414010301c0792207120040d075414150f54041500443c0305071048041c4001940841d204492040076a499595140f1080b00c1c4602d892000a012050502c014005c14603030794840348424281c3c1c1070904002096030741007078441d940c1c1c0b43c08591a41c07094078807800f80702010784410082c1e02c29040a50031420020005480128000e582c50400032a07440000e0304421582c0008100e00381d81d0400d4040140d02003040e041c1584101c4040c10f81502c202c1207000da034244026030341150382d45550b55181d41d110300c04015001c14804101c117401403281d91020030218011010034144403105000070689500da02c0d50300c9050010507449020407180800041004075000421541a10b130304903072091059a0610007542d41c1c05580107031010300c0c80313480c03003080805800ca802810b01c1040ca800301c3d01c42c40c408109805000006014 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 188122140 1250 188120890 188120899
    0x90c0324010e09210702010f03060f06030b060d0501030302151e010603020f130603020301090e1f020906071a060a0806060d06020a0201090b040b010f0b0a08150f18090f0309 76
    0x100401c0031554901d540200f00700b001d50780c13032940440d009980c50304010164403040741d000a02004540e0081025640c1e11540d040c10301c113942c0340503503c01003002c080c4110010b041e140c80030702d5060364031712044a0b0841412002040656128140250b42d50958880c1002c1c0c5903203038000c85c00540500000c8490951980300c502240c0e030910700114042c1d04044001c07800c5ca00d061200041c80900000c00c000580741320358005032650f1500c106103080d1807440850240540008000e1814026005030114041281d0070700541e8076040e01e03005c15001d20401c0005030405543d00355034140c0351000c0142c64002d01003100c0700e420342e40d101c000c0503450350b02c142c6809034044440b159050015106401502c00350140c0c1c000010803591030340b6a1200600101c0702203401d00b140c000103000c101403250b022005001c030080890f081c04003015000c1c010040240c000c0b0316201c01c0249450240c0d0b40c1421501e0044000f42c078a6030304482d900c0340b5103001c0f00161030f0708a4034080d0610008505a00106a442d074030401072 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 188123390 1250 188122140 188122213
    0x6090f0703030c03050412030e0901050a0b072306280e060f0a1506020105040c140a0603050405210c0106060e060433050c011802090402040c030902030105090c03 71
    0x180c0c00d0300d2074080f4680c11014860103120014045c507241d251225040d01949a10b100500440d00300308922105030000351040340019010300003482402e0550b518590f10041d5400241000800e41840c0d1041e5501c181503403190070100910400c80c41281d4190704000f14100f010f240f10b007040c002c2900c500f8582004c266202000180403844800600ca400902051001440d0042c00c885072106071a01c0d0018000350f9101c0081c0400c00142c1800f8400a04820002180c581c0d07460000070342c2e4208900c40c9908054940e8081000e000090001c02d21424035128240c20302c1d0140301c031564007a003000c034030328a25502e80200001c41c00e0046200c0e040100d00108030529003401d00c0f00001d010024100625a40d040025440c414030382620b80d456001031007501c1d50307515600c121217a5400d45814290644182481c03031104401a191458496001941140d000c2850001144200c008011200000e54150300b0f0034103100f0114130200b54551200b4081e0280c80c615a440d100c21000071000b00b128081110881 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 188124640 1250 188123390 188123393
    0x1d1207080d020306010c02121e0f0d0c110607030c060e1b0607061b0206010510052a010e060709081002040b0f030702071a04090e0604030c03050d0908130806090f0703 73
    0x1a4011680318005046c4064208070680100b0b003100c501071142403143d40002c0d00c0788c01c0c0305200d0041c0d0b0300c02c162202c01010100d17284c0702802c0e103568000e8400c006000414500d4810846000403000c20781c013014006540782c0415013001003002100c0401946d401d4500358540b0384601000c078004400e41c003025a1000707040c90842c18404254007413003050f50295544c0c2882c842682e581c2090b10701001243d4000d29855040c0000c010580131343e244440d043c442c040016060441b5048010b1300c0d007800410390f21790001000340d2500d016000402d4116100d02501e0100071100d03411142c0282a640e01104558010300e080716a40100d101d240030350f2461000c24011540c0350901c41c1d0046038080742500c140d42d03502e03650389008100c00d0110000c8070b043d52401f08090208040c0c5100700d400e006807010050000381800d86020f000b50f1003514000d000c121002502c05440076461b00306080d03440c0c0c000d19055072224865034131003010240707010b070344c00c24040c0d500810801980022800700c120070700c074098040345195 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 188125890 1250 188124640 188124667
    0xc080106020d0801140111070e04030806060406080f13050f010515010216030206030606071e02040b0103050118270309150212121b0a03050612210f07061d120708 71
    0x40c8005e890420590b200c040c1600c070000d00401004003080f02e414075050030580b402900101d00201041c0c000c1000340b01c100a10755100b150705401112281c0c120b540b985514101c4001c526500d5000760840c030415061810f0664154050751203100c1070746d004003425011000498690000f20341079451984014000e0001d403a003c402181c1200300109128940f000e1030b80c81040001001005824045103c4446415420700f030060751007038082464100300f50360501194024201500203485100d0b6903550442000b0003400c1c200c002034940e8002e540041c0002807030010428038150141390103a540d100d040001c92400050200468040c504409045c03441c00610807500c1c400050070001851001202c1101400740c590040c90008516038020030545031507814410042000a100314031035000108688044e0740c0c3c800c5030030303541d80454102d69440708100b4599030a4000e444002e8415803130f180545826100750103041d000e506640c0c05466440e501212202103c1c02a031601500c0c911003004440b200002 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 188127140 1250 188125890 188125919
    0x708010e07121505030d0807140310030f02010e040e0a1506140d060b0429030f10230f040b070311040b03060420090109050f03030a031d0607030c080106020d0801 71
    0x1002d1051030f08160380b58000f914014040c40c3d43d5000c124001d003400759255201079080c01da0120f100c45646182031003049a0140300d91803002510080307965007680c00b16849010207001211004005024105103c144641c8542c0032103404c071100b0700601c810400c039514034090b620403144e030810b0200015034441e0500001c0c00c10300c9411600d035903480074038840d01e5983e40325000da4410b081c0c011020001420b1301e011500c86000384e186100760300038014a030b92082c3c0012949100c400540b40420003200c81410f8450f0381d00f00d942e84413045081d12041054a000410560784290700034034009030140c40f0a40c0030740c12501c0041c5010f8070100708000c140a14407072640110342000003e00000380d21181d100740c40c01d6006040f5040a00c10f02d0014106000d5a031210115000d407500f100e4170108140102e00207a07580c03050607140c1080c1038440310340d00d10312001c0329540300310032500d40306071525841c10b410000c009100d06072042c00800c10300800800d0f40c0e4800079089400030b4154a9000003a42000859282c112 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 188128390 1250 188127140 188127161
    0x7022b051c050c0301090c170c18090a0c02070e070c02010f1b052a010509090408090d030201020301051503010623040f0b090a0509060d030c02031509060708010e0712 73
    0x1101d000300c4003505026803107603e120b1101c05507861303100d5040035540001c1d100700c1d82c1000100402c2d185058100868004240d03008141000e03020358508500200410040440e40801c1c0d06c80c0041d020020b00d90403d4110324034090b81c40d42030301c0c0200c0d295500140750240544901d400200c81d14000401540210174170184000300e400c0076104103200030310b4070300340741002141207a1540100d00c41c5882c05802503551404800003681c00d50a014440c00020319600a5011041c8078030f4020001c1004d00c1040e00807a051410080e10000502c80c590034041d000c1d510a126860040254190b07004608814209a90580e0055520b02c0d010b1415240008000520340e43d0100c090581000000341d01e0000318142d07401000d0b01050992a00d01c41000c1120080755903000c14003c0c030a00040010581d10000c21a00c51981803c1c01f000c000c580740086803501c000000030f8440c1d48003400910090560014200d41b196120340c1d9904002e07030b2540c0c07090014035020703a07004000c244501a40c040c0c03059207400648000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 188129496 1106 188128390 188128417
    0x1b0509180f06060f040f0e07060c050c040501050d0b04032703050105010e100e101206060302030c1905011103070204020403110111010c0801061209140607022b05 71
    0x294a502004c9100f203540b012641c003c8101640001c8444401e142100d1000e5143c9901030800d04030202c0076a42440344a0402d6240e00d0b05005040c107039400503081d445646019540c8101c18500504203c043c4459521001840a013644024041000b058000d4421a2440c200b540c2192410f810070144a800141000f80200d117030036009086458021310b0141d180d03142d452024140c252500108505541010740505103e015080802a00e0084041d82c240f007400d8020000240481c03005000c0c100d10021081009600a205000c40703035003001c2c2584e20380001170b4002012070b13000750001c0341c020f1a40c4000d0040303540e0060a00000c00038120007007001000413100503000103030510810040026a8084826803411a00102da02c56030201c1148001a6030802130380d1500c0040b101c1c030005100b01214010913007040e40c035004030b0b2910800c903112881d000c6203084420b94032098064a41d0f = true := by decide +kernel

theorem cover : BRFrame.Cov 187949640 188129496 := by
  have h0 := BRFrame.cov_init 187949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 187949640 ≤ n) (h2 : n < 188129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
