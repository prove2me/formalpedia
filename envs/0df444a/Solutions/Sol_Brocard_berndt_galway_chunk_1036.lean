-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1036
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:56:39.831126+00:00
-- url     : https://prove2.me/submissions/1e9f3b6f-ddec-4035-92c3-65c5d7cfbded

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 186151079 ≤ n < 186330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 186152329 1250 186151079 186151081
    0x60608090d0e0a0e010806180d090302040915020a170604050412050901030e03030702210403120813020a03080702030613020105030117161413140a020a0c02120c030c0604050306 78
    0x400d22403068000b2404002d01032003081c54507280804410031090b04460055401078062020300e9a12143c44d055500e40e99000d89011411000300400c0c904c26440060321494481c5507207418000b084074120301c01c401c1110704540d2502d000d400601504150403080f00003224210010b80b680c10207009540c441c0354890000041c203542c0120581e041d40110302114101075a03100c0410300a44204000c6000e10195001401e01102942d100b501ca10f10746032805071580e209100400000d10746400a045082c00e40c213044900740d40f00c4501d00c120000780403020b540128940800001e200460005014950003641a0f581035502d0000b2a1080b0542080c000d0000344204010010344030000d03013020648411800343c030546141584210340c04441ca402040c0410031200c4850090715003102c21442d801044501800103202841089590750070041c0724020740e0f0307000a220b6608900c21900b038441d007503008021420300b0808241c11540c603000a44c07458041d103d60340d41048146081d800380c0c0d007112401001024a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 186153579 1250 186152329 186152353
    0xa150309170405061611041d0f0313091e05070c020111030c0c010f02010e060f250c12090816030b010f0308250213020307090e01080a0204050714040b0d06060809 71
    0x2040240d140b00f0b0b0f07803080c0041c43c61b2104d661180600320195010300c040260824040f40018140b1101421154055108110820240c541c04042c0b0301110404480001c0703400d0f412035005981e400101c4601107152906040290702904a00e403107540078002c4c0e84503070303140907100002c0fa034074030410400848a900100e41c000d80ca42c46100e01c60100301c1140300200e0003c602c9042d1518200c03059035020403103120f0130f00704046130384d99180c6c04440d071300c1c0200e44942e40c40301302001806212006401401080d21500c002070080d0103420380300000d00d05402241c01c441e40b007518881c00d44280b800120b130b1161039a0000210458070780340a1094940001901d480e008007a0b88014030030741a40340c2c08480d07540050750782e0003694400c00b00550070454150056524501001c2c000d10b41402a00300050360707400d501c018421400000342d6410001e03030543c1c0004050302c83d800d06540b0843c0241d00350b0ba040b0000600454104080c002804440284000c14001c0382c1e2a020182c0c0e0300402190081c945501080b4034100f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 186154829 1250 186153579 186153607
    0x51e0c060c060609190609060e090a03170a140a0c0e010509130216290a06030b0403081902130e010e07080c0706110a05031e040512090a15030917040506 67
    0x904400f000404c4121702c03103a050f0100a40c1e803540d02180c0345643e00c01c1d04102002c8105201a4004500000341403240ca2554010300900a20400041e0072540d02c00046d158003140d40c031010f800e028508040c0034502d84a000800908541d07803548000440300d004030b2a643d4003540070395000000003080042140d50f0003a04400a411004c1d203021049900590040802d100b102c6c00001000e842c01c6a0301050b40d0411600180d039005409017a61502e4440304001080355003551540040d450b02d00b010b202c0e200d603106200034240c001a0614424400902c0a151007903068480d800c4502100707520701c0d00da9903000800d01c075110844641c000314080200084a180c0100b00822031580700300d00029019008800780c3e40b96411031713145d0001182c0c00006000a000008100b0710f181641500d0004182c0761a40c4d40c04d80320110b6400b807540f01a030106d460303030080c4d44040f000c1c2d02402d8010003d042080c1e5541c0024040c140200007500d4074a4440d682c14203c1041034210707804e071000030b0300c0f4914200407401c03011 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 186156079 1250 186154829 186154831
    0xb04090c03020d0e1e030903070902071103070e180610050f01020f240108010b01021f1e020d060b03040f0f03030f020309010509060a14040f080403051e0c060c060609 73
    0x101010b0382040300c504090f00034810401102081030090030300c44a40c50740d003108402880700c17040c0c0542c0140840da80c95a000101f013001e0b6020150301503110078107442c201c2800c403110b04900c0d601d4043e8038008222103d490400c0d0344680c51002d44030b6240940c183d1310540f100c509071000c0c4c05000c96204140000d0508800a041c01c0b401072046842c036222107000d042c00d2001c041c1455a01020102c0808052012003420502610a13500204104c280004c0040d550701c40d00e0410a0782e11156100c0c491180d10f0981c000c1a80030340314003588c880d4141002c0607000070f6001d03c0ca03040990340381480c08524002428103803485568804040c03001c40541751552010300201140c01c41c209612000722040e080c07118000b075801050420004a0300303040c5011421304255004000351000b61400ca40c414030415203101a54110381c200c40d4000380c441142c1000105440b40d5000a8405d118103290184d03410039820a03101100030a0b415203d001c04c500080044900c00e90320042d078558000d0011400f00e00c0c00840d09 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 186157329 1250 186156079 186156101
    0xf100c0e030c060a020a0b0903180a06020a021306050303070f0618020303030f10090603120909020f1c0209030a08041e2607092405060903032d07060506010e0a0b0409 73
    0x132511b07100a07964410710701c2001c5904180760341000c02c040c1030101c41500d20503480c40048075041d419506001009566000465010b481604015481003140c0101e501c450080d18001c1c06480d036584003401c24442039000e545c0c04451440c0751140e41c2c085101142812928164014003951840d22444840319212102614040c3c102c140c03130400013034112552050310000c41c0710710502e030364403c81194081c081c101c081d4003c0d100c0e5801000b184000004090484d10b0a000000741d14401d400c4c9913051000a010b4140600d4042c0314854010040c0542e00002c1c0c8126418007a181c45002c0b41401c56102c100d007280700d0383c182c440000c1040552031181c15000290060904100c03008660f4a11079401602c0840035206286800e000707240f0207418840d2542c9014010650b125031802e418407022076a207115102c0742140c000240211103412030700601c0040b091454040381d860f00e5141c50b08012000f800c0030f0b18960302140042001d00682d04005a1175812529040000e600701442c0101443c0604035030941 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 186158579 1250 186157329 186157333
    0x801150504030b071107060c14010e100e030d060e16020c0f0909010b0a0b04080c01140f030601090b040923191109060403141207081801030603050f100c0e030c060a02 73
    0x2440503031900c104000c600030091a5150441c8d800e56041c0500c0f03004101c440d54a0030f904061300d00068102c00144010362070b102402c0040e4001074189400d04501844a072080002d040c001c0000e24400c0c3c45005900481d42d03015000c0071080314a01c03c1e603075802c10031412030700300d44280d400316407925100c0102644402d0714000030030140750300300000386120b0164100300340d00c51002ca02482a421308001300c03c0400801e0070b02125072211302a10b40100e00490340308a0b162180080040c007280d200340c410800815184c25000d840780d8844e0010b1003c0c04880b804100c85a0b8402042042c4c212101e406c0e600402c0924002640040304078079100c042c18002800b50b002440c00c0014606030340ba40c83c0100010350054601d0700303005000d0440d05041004124070814119010710909010070030030800c8440c110207200383c20401c410a0001078014215a910250a600900c0014560444013044914580c1c020702410403200100c0340c1c050b64840f40300d0305245d4040e0b0101c5228901414407000401c0044000c0c01 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 186159829 1250 186158579 186158597
    0x30c163b06040905030d0e010c090b09060705011107050705040515090a0903110a0308040b01050105032701060902040605130501140702010309150204080708150f07030c0c020405160801150504030b07 87
    0x40c0e04d03146078004183c00c16001d98030399a06d1180e803000c1c41820366804c07e42c40c1c0b19120600d4000070043d640164002c007440361304005000d1381081001d5001080910350100c02c1d5440e507400b4200652102d00703d11a0038051810720300050507a02182c05c00b040c1e82600101b8220464642c4c16041005081c040c01c214240710b183c0603d804c0340ba4080098010141c880d40c0c600315203103440c1c50011060101a03101506020f8107000313200c082c400b1001800c850856886e9025068028051907601400440d0b0050b08818030003d408264551700c90300a08159015013240702e001c682d1400112100e440e02000100034039010700c42500198403940120a0a602039400a03901030420740c0d011049922640c07000c5403d500014042058107000d0155520418140034200b29503c0c1c021400724140b1401402d65040583d01c480c003044650142204074005600608200282d1400308000e000700c40a0340c1c0d80c100410154800001c051942803940924001d556480c01d0500740b4554440003000b002604c00014008015 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 186161079 1250 186159829 186159833
    0x406090203070302190518010b091c081c150609050d0201090f0b03010f08030a0e0d0f0b07050406020106090e150709030b0a0b0906240c030c163b060409 67
    0x114021700001a440c1401006604c1c000070017040c61010144030005420040c0100000314416040d82e008040030780e0305621540d640441d0308031709681260018003042e40454041050780c0c40c00f08440c1e401c41380c034000308648083d83c5401c4100c00000d00c03c1074009030001c02c060290703051401d41000110301c103040200083d0384030030a007151030299411541c0081c50100040203c1e02100081c90020480403000e5440c26119000003400044004c5c540e0303000740749009542c000c214045a84801c0036410803825003a60030500002000c0751321904c25800158202603000c40c5d009002e1040d00c0c1411080402081c1c2c60252010507806028003c01303100c280001c100000001c5142011114861000d5100004680002c403080090241c0c003c1e003014024841d48003840c030099010031016071101c651050440d00c4040200c5018078622485106040f6402100e80c4542d5400e49044901c0550b4401305083c04d80d0540e505000140b0365404044c10202400204a008d00b1070710034104039040107010348003040c44040ca07 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 186162329 1250 186161079 186161089
    0x2a090901140f090411060703200a0201020d0215181903020606040f050108031209011e0501080c0102030a02030d020c01060b0a020a1112070b030606071a01031b0e0406090203070302 79
    0x740d0040d800d00649128400007860501411105000d044a4076221420952185c612405490b10042d028038000503041c0c05140c01303240300c1d012601c4c034202c0da0540000102c0b030b080e0f243c0401d8101240540f050102c45600d942c004079003150308000983e11000107071b5a03814680038500907524004140c2c0152128803040042044100b010389005c0d40090030607090074020300c82100e44001c0080320b2603150a0041c00b5a10000c030131508109401003511440b2340b00c07a001d041c014000c5a000003070b0180c210884c4d02c035602da90340100d07048540d075600395505003030101c005903241c0c8289410b42d0b00503001001200f0035150582e0281502c80040400011265200c0c1d507900c40c640c1c0050f16007809a0f0065070071408020f0300d461402d031060f40c15100741800c0c1d000b1000f250350f6030704513009000c80c0d11400320003c1d01c1d5841d00d81c1031740c0a1070b40015281006801c0d80c5850281803000b030006441d1002c0180c2d80364a465501c40c4407074100d4004907040b030441da8446e21200020140300700304990602402d100040543c0e15 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 186163579 1250 186162329 186162331
    0x503030c030a0207060311090f21150f22031b03050405091510050702060c070f081c08060112020c100c03060608040f08031b040e0609010e2a0909 64
    0x316500031959411103010291a20801e517110201301410015041d55103032600081e40d410780d00580d80125400c4c80e0754009081c3c0d030306135100d80e8070701110b040050340b214030001070400c110b01d5000b9418080ea181c0e501820020002156006c4200c004540c84070407180d81c0300000e4080364000e2505024030803c03203002038082c6100000030340024034042402c2c01946000c80c2d5654000700c0e403d9822892003170a6000c28804880c802c0407406222010a40000707540340c1030100c03480783c1043d10540e1400e41c0c5440303081d050b01d841800343c50307182d1207030143c420b850f4520000040c0310341d841902c9264591f0364080044460f20300f00032681d40b849800b44540b040ba4501040140c4040391405000f18801d40040402000c4800680c000d400304010001404081795014058400c840c0e040300c011aa40c0c0d841c24140d100541c403a0400c520034000c0010005100041a6000d034003845044480741c02c16640c520310743c50209415902141142480100b9580c52402c880b4100e0a901d000c9a4460905108000007904600 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 186164829 1250 186163579 186163597
    0x70308120a1b080a0b01020304031b0608101d0414060708070e04111207180f0f09060b340b011706160507060b0901030602070b091b19050303 62
    0x840c0805202a407080c0340220702c03410880018241e81c1c2a08030b040240030080c09407031619071a40d105030300002d50f4802d10459001d1900310a01c990400b620001030550055144211000600b07038001180c040754803051000201e801c1807005110302202c4112805003842c01038001c45079260014107000001000344a111710500407515090064134181ca4060403444a80a909106901e480d9840d040d0302c4202d002c1d240d141003442e5500c65a82d407018419154040d8814403121041440f9100041b04075074481d125003601c443d012161a05135985950406031010343c0100311744004184000c591000000000420100300c1c6043c03103101140100c0c9052700703038660010540b0200825401800441c030304041e032820004010008008a03d80b01c00094105000c02c801081000f50004407507050120642181c5c00c542e000408280701075a691500030300035071000c03608a445104190014000071408602d10040e403400820a80b4940c509004101d400314050007600c0360701c101c0400201d102e48040010f006406 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 186166079 1250 186164829 186164857
    0x6040609090b061002030307022805010617010b040209010c03080709090204080106030201020f0a0f03050a0c060507050307170405070513060308040306022a03090405250203130e0f18070308 83
    0x1060103414072011010704c142e000103551081007403040c1164000b07503201004903012401c01681a8040500882440c2e2420217040c1d076017024004501461154403003d0403c442d41e000300a041d14210611040c0d00508000e1404254102440804a405a4441079200d60309182000c022a2074641c40012a00180c00c020301c5a0355a0605204558041001c1d40d91344007507000901c100300c210703901c807000070710520030007000c10401007441d251260154032001090359119105002c0b502e04004000e19a410440c1c81c4000901d140c419924100c521100e03940c0203581102c05051070038100002d019422090403000d00d0841d80d80d03c800404101c0311400703400654070544025036201d407400741131400c441601080e40050302040103c6126100004220350340c055040d85d000c6107e48d582c54295082c5041004110000308480d040f45080d141d0110051901130b100001d2034011903118040745001030700842d80550f030020044d001c01d540301d40300015001040301c0c107000c0b51395160301c4c2d641d503503800c2c0c102084500400e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 186167329 1250 186166079 186166081
    0xc03090409290f0106200106080604030e060711040506030c03010e01020403060506091e0601031407020c150f0409020f07080403030c0204050105040207021807090503070b04080c01080105060f0306040609090b 91
    0x2a20401641d00074031210502c6455a030510380300e44010f00e24107200d0f08080c04003000c42644098411802c20004008000080100640d200a0300382c40f200211411030004524146106580c41d082d41070f10b8446030080c1c10240c640d2041000d10004001c041d01c09a810320620110a109a40c24041e41c0d811502c0e0600141c0c4451a505e48101900c00141510f485186040d080050440d00964000519410104c9000007600c51400603001001290b581400204402d000c000e00039800145004400c00241c82e10030034040100b030305126034082e40201141c441810003003004122402d40141881c1031081c20710900c1c0c40e280350754a480035402940110b0201d4900700c40942545001d100d01c0d4011311007034a09615140d00c96000408082003a8142e0403a1403c010124041c2c0744204180d001400e00034003101c004079107460345006640c00c40d116407000f5220315900d01c983c4d035100c3e2a045040b650094200350821003503000b85001500001d041035006541c640c4000ba00314014094200a00d00075800b042003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 186168579 1250 186167329 186167363
    0x100c020102190c1505100510050c330c0408030c07081b06072301020301080307050f0d05030105060307050d06030305071202010908030a0c020c040203040b090f0d140c03090409 77
    0x214030402c410110510075854248004184000000c0040c82c0c10480300003142d684180b118100140d454002c00d0308002040004c2c80da150f04507009080800900b0220303400c080744020340070448040c03051100d000d006403440034503440700504621500300ea031030301e0050b0900c2d413a090b0251850708106014800c5500c864020070960300700380041100544c1c0401c80110456841d0045135030327071103485c00c02840001e000c400c3c24800b201c61180c503051b1001c450020356403940d60b0361071941d0742d4001c1a415501c5000e148000e10024900003085200a02d1503100c13542560700c0e01c02040013640000780301809200040102c14030200840c892003021b14441d44517941c480e03010b810401c110070014004481075a00d8040d80401040400707045e0b0360f001d1054000800c210050090403410300c803c494166401c180040b081c442000141c51070380c2d101d0006c030001c5900e040614840656038130310451302070000c61943c1200300100c0d00301500410103d01c5042c203c038a0f20800c1e8004c1021121540000d0b9025030340c20f500091 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 186169829 1250 186168579 186168607
    0x4030314090109080901110309030a1536262106090c0d0f090f02030115180203040f051c080c0705031209011113030308010510051b100c020102 63
    0x141044401d40204100307035995131046242e1250200c014103010040c80c016048400410442c6c18402c00a42610003a1180b0300e01950003298100000c29000d09245001e02034034400420ac00d8070b010840218107007042018580d16144201102c182c880c0c48101801d110740322507440d680702800c20101c44141e078584140380c40084600c0903ca4680c0800000c01c148109990f0b030030186900700c00344284442d41c806e100c0c04542d0041600b80741e00108581051181e805002c000040c03030540c0c60095009118101103d81c001907480d1050040750034400001130b180c024001359a0185a10621564102c4d148024944490745003104050043c110f00070000703006195035038045ca14a400c8100000c8031418400e16941c0e10b0b8807405480e0416a0100000000403086042500074207600c401c4013404135039079401c80002d840e40c4091400300350301191402c80006018284441e240400d10f03882d035100b40c14a0b0800031001300350244d035210000315200341c104135080540144501d00450450740c00050b525a103034402c8507 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 186171079 1250 186169829 186169831
    0x503090f010f080414071a0d0c0302030103050721080301091b020c06071403091504030605070c020a0302060a0306030203011a0f0a0b0f0c010207080d050f0a09050c0d06020f0304030314 81
    0x190400c0700c030342d4103803400329041105660065030050800785108802c0a400e443c182c403d5000002d1741003100001040d848002c0001d22450004250511841e0040302c1c1c04c1d001e070300c020310000300164080e81003001689120042c2201c164040e0016021982c210b0b1181c18068200b85c02c006605039a5540818215100042204158040703001405a50f045040007600078004c40750054a04151031060501e5008107000300c0e00c03140d070000c200b960701c01c07074260317400405030007600084800c070349054007040e10340303011300036194446600400b24001e0a08550a0040344d0304446503c0041c1a11100c4c0403005903030030f0107641016100300f200010118941c00030001000c400180b03ca00039a0103000c140701c2203e01c181283d00340941076a51030b541c0d00070484068024400c0d40b002400400021804940d50613072904090f0080c998081c0e543c1144c1c550500d4281264000c21000f8015130101e2800992410703c0607440740018010b01006080420070f40c8001f100c2c0e881150101d001035540c60110040310608621782d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 186172329 1250 186171079 186171109
    0x10e040903021b0d0506070801050a1415070302010b09010e060f0f0306061c0b090601060801060203180907020c0a09050403030c0507050709110912010b0a060e0109090f18050309 78
    0x144061003990314040d480d00d50000c0ca0300c200e21183c0160a00030788035070400050096000d4111052072900c00002080c0007001e010701e83c45004a02c00c0001c00100000000c903200400070f1041426600f04000c4030507503400080210295500c4540061460f40e400144500074030714802c0100c0b8500d0a001042000c106800c0c0240c0b18100300ba02003103964500080650340280c0030b50b800b07002a08500c1d6100d800c80100100100b00307100041c108190701c0f90101d030f6203040742c8107900c982400703980340e48060740c403030180c02001c40480880801d545201c0c540030000c40d40080302070040e00d9080a2110200c0e00c05211a04004903481c1c8820a00080587c148100e03006200c46c0e2404a0621301650b840b540c03580403621801d404142c131100d4603000a840da4040300c14000c8001d0501f4580034482c9101400b800803900c0151103160612070020740d0078041c81034070b112508160340f410082428440d8400c000c00980c0c40d4019520394405000040b0030301081d000c4410380c0500000d43d00d89480800700280c2410380945 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 186173579 1250 186172329 186172331
    0xd06230f01050a08010b0304020409020904030309060b0108040515100b040902040302030706021501030f051504030201150b0f0403140717030c10110d1e060f0806090102070b07050708040302060f0405010e04 90
    0x4a0800d03075413044410b81580c880c181180c2d0350761100d000040c050480c0e600301950000b6030f00e003403000b09034240e4007103170074288030b0f03401484010300c84030041d5180304081358007800c140c00401c8000c80e06039640860380c0d80500012801801c0c540c031850354907620781154114110b000c2d4005014000e6290070000040107010301c0c402400c280030300d924401403800d018032006000305071503a640301c01c110b020b00c001c0701055041d41e20311400d0325207400c000703000e000c60400250000d10160000b10304202c1030012110000b8000d0350320744c0f034146517aa61031641100b1044c80e02c07582c05200d0b40401c5601c0303c541c86010380c003240170055032201c11003104c45080ca00c8001e8200600d91030100b02c0700461740440203403081440829000100200d007000c01010300310100d0040c1c0b10140c94454040303503000380c0d0b403010004d40d18840111001aaa1200514200c0c45136050261901d0098000201614452801800d401d80308030a11414641c0d00d03404540039030010485100e410b1400f240c01d1002d5684000c0c0d03034020400c1290 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 186174829 1250 186173579 186173587
    0xf0f090e06060f120f1902130606050a0f020106030503040f0e0a02030105100c020112060e1006170a050402130903080a0f091212020c0f100e06090706050d06230f0105 73
    0x80021a181d60045a11303018070002e0b24500c2081d00c1c1841041903100c0303c0c400f0780304920b1136091805403610352440e080384907400c00c00c15900e051640340300b4142a5180764584618180c58040b0507240420880f03000c03400c40d0f49401c030200000c1c01c140042c100501e2140e503402c860508140c0030015910004200b40e460b00d2061004100d5940e50b9030740380303032078410b9420108076407038507400121242d50320884509513850602500198560403010031520032020000100b15054980d075049501180101707404a0160400d07020620000040c0d0059800a100070300719102c0d0007001210700c05a40408401303030081000340c400c1104110440c0160503c0c0100500100034105490b900d040b0082c0400c40c01c80100101100c041e42032210640c104e0b0002250030003180c00c0b916186007400c2c3e44c0c1181c58050004c4505011403034080060014805001f4224100904010707414984221525004440c0c02c000b42502d42c0c0c0300250601d0b143d42d0440084040048003c030000380c040030701c1000b5162480440c10032200700 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 186176079 1250 186174829 186174841
    0x190b0307030e30090d05151e06040b0a080a0803071b030203031503070902040f050a050d12080903090d0b060102150106050f09030c060307021b0a0b040e100f0f090e06 73
    0x318041500c0c507144003000d01803500c01c20440301130240c42c0324180c02541c07082080081c041c0014610801110700c0e40b040c20300d6910b101e400c221401c1c0140c01d19600c0d040d888041542407815402141b072400c0090008175106603103130030035880d04c5010101030b03410a000009016550354800b9010986190501840c8594a010317076000b5600d1000600d1b5000d0000c01c04c0728041e465905010050051140c035005540b40c6850703c1c0410450000b5108613841420240381c0000e1500f0032108100780e268014600440c290003001c000d0b5601d200003098400d09001c02c01c008041a1f03241a480c682441c02a180030f540c903d0480000fa00e090440700c100036800e100c180041080540c49021299a51850b0b03104c5030f11000c0c42d001003840c0047c403003021a03005102104004459034001100c80c10038820350310034450324105106000d100005405070344802c0b2010001400300107180800c4036000f9007110151012643d0f6032032031103980c000b550403000b10001c0c492400c01808080740200c1510100e0b41018160a0503c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 186177329 1250 186176079 186176113
    0xc03030a0c060f0902060d0c2a0305031519082515050412050c090106050a090509070e04090803062d01140403081204030306060c0b0411190b0307030e 66
    0x403540040c000703525143e408007000700c2034100e06482e590103054507448800406048020f03104150a900000300e920300d00d551204001440c0750180a100092090b051140e80c80c220391a13800241081d0507004070a01d0f401c101c1d140d50b000038104c024003a1510080c02d0410304403e0609481100380c000c1200002e841c4115407551602c3d0404850008010354508503032100151a1802690301c1518182c501c1e10713206090010100307013109039110440e01c22903941c1c0c07528015941e9006403070403003000500044050105041848242e070700400f00381840000a404800000d09841e140542154040b00100030300416062004280900395603a00d50091041d00c13100307608a00c800c0c003244250411280040c44078241340881c0c00c8402550304090150768130381c1c3e45840607207059000d85007100003900d0288005211440355082006082d0300c91070480b003d81740e503143d02c005074800720485a448018002004c0741118580f244030000c0c0004800300d6241e203002100581100c2c1d00400031843c5070401c141c0315001a0320 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 186178579 1250 186177329 186177347
    0x4050901200d090f0c050a170d050318030a0f021b0303070602030403170f010608010b0403030e121608240402100f05071a040203010f0e0c0d0609020301021b0c03030a 73
    0x45580d181c4038405148003801902c040c84001d010703004010810410b021140080c017081d40e90665004035440c0da9031035038580c5407500b0900041950441072481c007500d840740006540000340100410b8000c0e980142250035580901c01000c08a01e1030001160850b406000c01440504041114201e9003001e0700030a459108041008000e56400000075040500a1090089004281c1034075105481c0502050300520400c2c003600001c20304e104000514070b880e0030200c030700b40c0703034140d84560f500d000c0d61050083d10881e1060781c40e041c0c00382030005403a4928504240006200c0e41e40145040401e15400c008000701281189100110003c104005a00c40401d8161007100c1d910300503200c0780540e042180c0341c0c041c40700010518000f07000d003010301c0760003500304900880c000c500030403455245800300012240000711205103034002c1110f003601890115504c50045015017004100c840065000030708a0784941100311041701200c6405896800400005042040540c011880d1a0003800c015020f858 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 186179829 1250 186178579 186178631
    0xd08070816180e180f160603090c0b0d0b0f040e06070f0c0510020306010e0a051f03150f08070b090303041809051f0f05061f11030a0c0204050901 64
    0x703140314841207200842c07040e00000340404030f02002e55081441015002401c1d580e5140a14403d901821001e4903010400c26103040c1d0501e06950141d01d403030021780103460704020503036203d03d68400004145002000402e114103500900180045054007080855540119641d0090340352118150a50388000341003504030a160502404004a61034101c07614101414000c0c1903019818146a807621181c000d54000d07502600d601d0550302e0042c00f4050051024818aa4495441ca1081002d060817118090138024140350109110480b02e5060303030141056404490b9142045900300076440d0140700c5a0003600c00ca00c0044e241c402c0c1c5400183c0d903805203000340000380e83c622442c80c3d292440c0da4411320b452940300c000c0c0c034455201d4110141c440c0e0343c00384a0070341e00e50030702088a1b40d6000320f104a5109000080410070f440d241d600303492100074168010503040c480c0c421403903c0d40710710400c058100c400107903490344015100c61041c88140c48000e04400f10300c0c5c1c108003040a86d07003042c0c03568407000c3c5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 186181079 1250 186179829 186179837
    0x8040f060216090509120d06050103230a0b06220501080c2803061d0106080c04030f11010509030a0c0602070b04051c0809040c051209030301030b070513050a080d08070816 75
    0x18031007000090400b20084c4c925011071100041faa550b1a800d0380000d01250400d8800b08658024100080900034120140c10511180000002e2000110380e2046101040152005040c002c1a00c00b000c14501c031945000790040b241c6404100b0303580d1110000b68000e0000d0109401c000b007142150580c0340b508101803802c0000308000c803003014071983c480130040511186880c001c4800041d1400d034028203004510004400703500007900340c032400c0304460449601c581c050004000c0e0352540c000c10080342e500941000010003140030f0503a410041c00320220f02403110700d445a813a00f007010349448000da1025402004c00d01c400c00c02651000005210000400394558100304070b450680c1561007130020ba81d50003803400c0c0300c0202d444d40c4203010b04003212280d10003200d80d841e911100c0d030f85c0340001d1200404001902000660b00d91240c8050032650f000d6021504103035458000003140e08480ea000428031b0f61007800d8681000e94089900794002c1c085003400445410b000b010b00700c8a04010702c240042c8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 186182329 1250 186181079 186181081
    0x1d070c05161d01051c06150f150e0103270f12050403110306060d0311030c070909150603380106023909070c02030a08040f0602160905 59
    0x3100081c80300c41e0380d000c070204110103102d840302c0060406420b620410151203020500104290501140c0003a5a07a00b40d000314203072844036540d5030040c2c450149954900e901161001030b100c999161078074050640000c0d402140c070100782000300f5401150070b001d4105414070701010140039500c50ba45241745800c5c0c048852900d03840c1440302e074054411000500300c1c44040038000b0001d600c00090000d9a01c111101d07071413110f203c403c1607501c0500b41c0d000356200782202040000680100500e80045148006503802d04400d00d0503641070603100c3d4001600c064036403581404100e14450b200010f0619084100005030031511000d46082450025040e40d02c04046040101d08041860038048029803070902841e6841e04002502c40742030640801218010107410482003a400815140c031000154440c10311214a004101c40d101010b06401300b8011b0312402c0b0340c003584080c4201240d16000b01c080d43c2d03450340380c2000b83d500ea8030140c1c848811900f1140344038202d600003503240070882d05001008505 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 186183579 1250 186182329 186182333
    0xc0708090d020a0e060307060c1e1401050a02030703050903160602030c0904090c1a042306040b03070c0b0a180f03030b0a0e010e06010507030e010804030302130801060801061d070c 79
    0xc00d0400e0240030b503001031200f000095104101104500c04d00e400e07420344162031782c0c410007502c1928003090000c10b54104034510504031424902a080c0490103480003048510340c0481140c00c5900c1550705045041d000020000035540500075180c00402c502c0045142c42d501752191019800f60302c1000788619000804544406c0d810010380c0ca68020080c4104483c02c0107160034215901da40c4034000781d81940d080740035400100002518101c48031050903600072140300c0907030804020340c14080c0d94407150501c80864584480b001841c41400544c441c4030211986090941040c03500500c4000740e9401c1c056805500c412043d5290701040d480940c01594500900d803d0303025003500d40613650071846000000030200001b58119048491441d04480d060b12194011174151007040d0001d0045041d01600d0182e5510034414164081d0007490018100750341c11a100a05c1400350780700b00d400f40c7d10b81500744829102031007120020207200c1d4040c8044003201c03003880c1e110b641c002e04c0c450034000380188281c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 186184829 1250 186183579 186183589
    0x10611060601120204090c0206010e0903040e010b0702032a041505010c06050402030304082514060a08180709090302010e161701020409140108060915011a09040207050a02180c070809 80
    0x400b5008400080c00107c0341480000d540c1e0320248101d41482e0344d1080410b004040106c11036050b03400c0601d0100b100c0e03080040d09031460380008d074103e816206008020f144034464849000000e107040510312440035180c42000181c0e101e50b03012140000741c038001004244c1c0c1000e0710760492680460003046503074540c00007a01310b015030b41c450640c500822840c0c00e030000701c81d030300084403408140002d012140ca0701130007000310101e042d8254100381c0401202e644c80380104109079121500514ae07003441c00c858090300e0304140081e401081c2e410b4581c003520341015028000d207010903101c13100420210b601080c0309845540d845c8070b2002e02c860043c3e040c0317900b0a0f081d0115400382c14281801d01c0310001081c03842a996009210303445882c051a0301145814001092607034610326005102d0009034200001100b086d401c20400104601003080035109548880c005005c186000b000900200303001401400300c82480081d510341100168000c100c0103c1000064541e81600102c480f81c482c186840850 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 186186079 1250 186184829 186184837
    0x60509010c06061203050406091505070b191a03150c0904020906040806010e150607030e060a17130605090a08120601050d0e0d090506090a170a17040e0106110606011202 74
    0x968403488425904c02c0c550046d0050040fa807155031890140c580e42c200209900c3e025481480c00030342c0400201c4040351b44140e125420014209240c03690410642d180021104c10310b05113028640d5040e60011189402e0200108041c08808108254038015a0f000c40501c5144c1c3d07810300c510780c04120001d854840000b520017402da0f4804a86055854541c42020144c088900f0b94400300c0d00d042c028000d041000c1501d4200340d054a0726010360b4004400c000f403035005544a0780400001e5400043c0194029004038041c00540d80d490554003000c0c100706041d0390004140f41c0c0142d1029400320002401c040860341d0010810703c030001e090b100d244c01280c8621130822941c1400d410101e040e83c004401082a0750741c4803203919802c034951359400a00010380240114075a1045c01aa42000b106010b01600d8003181807000a8030303404c03001c940e100e02079085007103d5103412840c081406d000326001080301d1405800c55044c009103903040180d250383d031404c0040003d410044e12032502d0002c140d2a030151 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 186187329 1250 186186079 186186089
    0xc070602011d1525031a100c110f031002070b10030302100e0705090411010201050f0105181b0a090e01080a0804031e150e07090504110d14030301141009060509010c0606 74
    0x4041d103415138400a000d002c4180890782043c845410042c000d1030b061103480d000d071394241c4441500290755180e036100c404003560001d4101e8031000c0c01c01e150f41d40078000d200c0310800781240180c4502880c200300c6e00440000346100c00201601c40c060000c00c0d0006215140c5286e8a1404617000c1650300c405400d01c903103540300c2d9030442d0409042c40200a000c3c1882c11019034281e008000984d110075a00400380320a103c0c06401400b43c021a000529240030304130b074000890828120240e958180704070103039003d640510002000a00184220b03120320204500409000c0010495106551290045480707580700c000d081102d400c01100c00c17a68640f0050320b1071504035032102103407003469004e4400b400050351240014000c00c207010a117941c0c00d2064074004c0c0c1d00051a000e1004d06007062080c43e0414400c103607443c1b442d8071524100998104001c1d170290000c5c819000140c0341000c01d0000c0c1da4410510a01400280001482884d5011090368562034091a085040170001e080c29030003030500e42c06c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 186188579 1250 186187329 186187381
    0x112b0603020312040e070305012102030a0203060c071a061e0d0b04060c11160b09061201030f0c1211150904061401020d0f0e010804030302040b0c070602011d15 70
    0x1c0e000320520f02c0d400b8100300c031004507212559940740f80046044503800d00907000b0200144c425010b07408541c0d144803070494406400c5a00358100c50300001e01d8094116602c0c210b0b0340300014218204024058860340305007490030303103441a003044400528400500d071404800001c40081d600a0341e66107989015001e81c11103d41485400c080c1040e4000c1c01300041644081442e0901d00080d0040c00103507070020040000c00040014200002003005a0107084020343c840024821011120030074107589000f1441109d842a8500c0302d89400805d44d255980511030a0025030030b088007040d039407040ca500c0013000300d9003d103031140b031074940701c406024944106030031a103800300c04642c0b2f0080d16401145c01000b40c08499004403000d6080300c85281d201c3d00180055420154506154095501141c00502c00e0170094107240c3c64100200d03894100c103200f080d0580c41601c0800c5501c0d020712039480d01034802460405500c08000304940c1e510f014040d00c4075000081000546a1600781001000d12051050703 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 186189829 1250 186188579 186188593
    0x3070e011203120902121b150415021c12050703110909180a030201050f060307050a03080a0c120c060605240322030f0e06031603051b1903112b06030203 67
    0x4a44c2e54481c0a00003a4044241c0d00d1030801241c0340c44a05102230700d24040c40c46103480d0602c0f824041070350720707110b40c0d42c01c0d07208091441c03191486008a8042d5812296101c01d6090080c4c11014140d580152260062518200700010544540d80c00c0f42e68804090700c4024490701d40f40c585004515201075090424041e241c1c04004069040d084140101081000d094158407010101500c0321a2842070a030b202c04082c1c02040000c245001506401410b030520029110786511451034041d160300759000090304209400d41041564400c9501610069900c00204101c3d9480641c0c1030341e800c80c00c0400c8000110010349400030380305642130f440c94842010400a8060318000c5c111210840c0302d05c1c041080303502c0c8511a0300b000015a03200d142881d5081800095581003940244005040760140840b403030b00005e1214200d10042c03080c119074007074860f0000d640d068000c040350140240e03250744000030400082e00d0702c000004121007072840e080342030401e1a0307440000300400046c3c3c0001d4050240c9030f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 186191079 1250 186189829 186189859
    0x412060b010915030605090907060819150f1d04080406030b0f04020f041701090305031303020a0f0803070f110601030219030614070305060f030d080604060b03010803030603070e011203120902 84
    0x24218404842060310b01c7c4006031216416152140050b00402c00015045000201002c65681e000c0e203200e81c07485000036a0700f01c0e2403004100c90303190384c21920001d5602d5000b00f0030a01d00800201e0881c03542c019010083c1040d598900541c40b551180008140d110003110716282e0307806d500400c1ea003c0c0103000b1950754520307010900060300f144c0b05c0c08038060800c000b10710002006003c2c14806c0c981c965555490f41e07032010800384030313156240320603003c51143d007078000000b40299440a21450088a4450b2a440c03d044010541a110b044450400c0318400c0804000c01e00059070906499048401d5281410000c04803d070301e61b0194400390020b0705114600c4e1400c181c0c0c080050060f6000c0d5814007030f590356001070000d00c0401855840d090780c0101001c500c0c1c00e03c20b60545030011401000411810b5a9148000054100780c200f85001d41000007402040d01d010040540103110341d1029480315858051722050040e2f40d030380c001e014400110350075415841181e2000b03507129801842c951108881d1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 186192329 1250 186191079 186191081
    0x703110706060519420c06060503070501020624100c020a05060903060a0c03020c0a0302150901050709150201020708210a0e03040b0c0102090405070c0302060109020412060b01091503 80
    0xd1041e0b81c068810b100c00e60380030340c116408203800d69892800a1441e05c220440c0d144012500d0100075951100c008040907201182149450344011207990b1003040e04c0c51410039000320b8045600642c426403007528100320590700480c05641c03100318101c1e48441c1e580c0006600c3e40b43e0700801040740c1c0c410440310684c076080790401e0921152500903142d901c205610303601440f101d48102d030b510a0745039002c00c0010700b120035a40c200120a064614006d4100383e5030083e854135050f01c04d032044000d600032403c1c0f0415680044c0b0400d034065080c10082c0464140600042c141c000c031802046112041c88030020305180c001d4048500f15540401c1d003643e9030a1686001451949100d82c2c0c0d034061151501059001c04540100a682180d041c0903525107850300c1c0c02c4050b2644081c20260055400f40100106662140700f160700c42d02c9ca58945080140181ca4001c2c1803801c140c20501e03090740b06020611000c0707003464072070400303523401400051100002c1005898003440795000d412100c80114003501c4460741 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 186193579 1250 186192329 186192341
    0x91204080c06030901140f0702061501050d090201120f06031106090603070f0203040b04151e1b0c0513050405160303020c0d0305132706030b0a020f0403050a110a06030b180703110706 80
    0x1e09d50070b41c0c1c1030741c890075502c104a80d45030035001d0001700c1c240301419905015520804a0500c141000c8400100c07501d0448203840e112003514503060b5407410200140309018264404007042203481c0c3d031401c4501c8001641c5800003400c804108a00040f103131050038000c008681c054480c03964200e8940d42d8500c11007400081100f080c4001070070280d41003102c45400401500c2d00000d68075080041000c141a054206c16108401c2d90300c4507280c01d00044030b880e55003d20210f030740001c034041941c0c42d19044c0301d0701d00315868000182611b072124042020990211312600c91900458949030810704078241151a4026821103810008100e100003452401103522081107504001208616001c1c1090042c100e81c804c0c4000b5082803450b90004002c2d0070507500800410040081c40da0900d501e070b403503a03803910b10808402c6400c12000e0601071000d00d48a035031130000b001d01c1c2c50184100f8000c13002088070310003071401546c1d9888098000c900450702a4000e1540c41102401c0301c0d1f100c02d0181081405011 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 186194829 1250 186193579 186193591
    0xd0207030f020a0c14010e040623011d06031314010c120204030b0606070c1505030105040b0a150e010909090b01030b0a020307020304120f0218091204080c06030901140f 74
    0xca800079038030441c004903441c214107400144000c1103510700038443c44a60380b5014060304000c503051042c10203540340d01c201005010f80a10b21a001c0d20201182c6041c20048203189041c09540054100d50a1059441000c0a00140e81c04d44e2643c03030300b4075042200501c09600070803481803640a14000381d41540010040c41d8955111382e203500074001c681d0200d215500026224040001c00102c040c1030842c02450103d11805a1803081d903980c50f50149142e104d005400005000003004003e90700d854010502e85070302c100c030b6117843c452800c0103181844103120a07070401e00c154a000c40c14a40c0c000c0810f080141241602401070318442c0c0f5281d203e0103400d0104554141c03d2002041c001aa0384c0300345c03032090380c480c0c00079031611b41003885c0354040c50f8100104860f08800700d000762005885251078038548260982000f04039040001009042c410441610b03581c9030b0050004014660b0009041020f0741c02c191062903503a1600300d011030143c03403440121040c00c46d140c4144a55401a0703058a03216103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 186196079 1250 186194829 186194837
    0x804120c090509032704050c03100503120a0c0204110a03020c0616090303081801110c0d030e0c040b0307050d081c2d2a020709050c070605100801020d020703 69
    0x1544601d050412039500b0b40705045994810f1000211030035040302814910720f100090312440110960006041d150101c51028050300040f06005021041001d01406007804802408e000c1c102034184d0300d010f0180100110070020101c280c4015900da039130001072144082e032600d0b951940503e101401a40c02103801c0000f51180100090740152510310078102c03485140e8420a0261954600301c80200e4040c280188190b41d154902c03a41c07001c2440390703141802d8000c04050b1204100c0100604051035440d100090504000d401d030061100030600b0910031008450020b0303080c148030082442d080d00d5400098001b2038031000c14050104103000b0740108080f0000d14031510690b80c035428150754420328842504401d03543c09194183c102e003484003040840b0031000642090218028800a41e180e42c521245801c440c0d407280395690501c0404060103007401709108505103070100e14454420305030b020740240e6888003c110030710051110b070700c000d02d0f00900964a03842006100f0780213500c240b00480200d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 186197329 1250 186196079 186196103
    0xd020a06091a04050306010506030612071202010e220203070e040e10060f03050a0b221209060e01140903070b07030815040504020d12030b1309060b030c0604170307080412 75
    0x1c804210441e0709540001c5c01070010340c0d2800060145541006e00099801000e0020000c41c591080010034010003260700d0b043c0c0d1109143c0005022100e0b40c04401d401040c0c6d002100807070f16041c01c003100b40c0e103512103c0181d880d42c40580071a8000e10100c0000c0d0b20904003040c10b10a640e00090800701445060010004c8503903802d081c00000540344002000b603044502c05e000403540301d41c25258081c4000c140c4465150b040009002840e24007a021525210700e0306c003010707506501a004a02034030b139909010083e2500980040c1c016050940d4041d081000020001496201442840010310341c00c5c3c12191581c010b80b40c05002701c4001c403020a202c591030f04292400b031400f400b0300c602481c0c000e002d407032441c3d0442d2540158040320304588006d054a404e41050f0301e40b25803d025032110340e1028001002004c1d80340c0b24060b148007102c4107100360b2204818084541d100f20441d000c4800000f14141002450703400c407819405400805000381c9804a800a50f402d501c5403600c00c918030490407941c5c5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 186198579 1250 186197329 186197369
    0x4080c0a110a080a12030906110a0f020607020102043c0b030403030c020a0f0b06040902090c07060506030d08010b031902070c1502010504030e060a0c021f0f05030402010c0602090d020a0609 83
    0x14030030f060140a0000d402aa1682c1742050184d4070520307015008040c00300700d078400790045141a50215001b1000507495400300c102560b030511031180c1101c09031000303501d0b251802c81001c803d02842e4009510400d16040c90350440d81280e9180b18100c00882040d8465076550703150300320b80360000ca4055002c64140b950f81e207111440402c1d648a01e6501c5410f001004502c2c2e00c034040001e0005003207a07002581d841880025076191f2026601c100e0480c440c1c0707075507581c080c9040c000340e420161040f80243e1100000383d4001e500102c045040d110024802c40d02c0b80d032a07070701114070346c090b030f001210780e6070310001c0c44000b4082003901d03407000d407107150640800e4000d881008900320741089a0250000340e2112103004c40b40b40c40402406212090324020030f49500640008000803c903040c1d07130600390100b584090041e90400d652108285075828020f017103141c56000a400e120141c28000c0c4020b50006005405a840040f10065140c01034401e400d00361302c80c0c00c05000000780740906c2054054100361294 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 186199829 1250 186198579 186198583
    0x40212040b011d07080a1a09010b03010f0e1509040206120f0103060606110c1009030209180d09030b0a0c09150906020c060f0405040515130204060909020307051204080c0a110a08 78
    0x10040c14113560f0380416944603811940141555440f00582c880c085204011607130308d4004941c043c0c0310240c01607950b54500030105512444e9540102c4c0384013150703010030481800505009200c00c1c029181e07070361a81d84031300c0002e5052095512204849011000b40016110007070105810f030ba10440c810001251224030945800010380c9421500364880c045000c254100b6050400001c3c005061402401e92654002800341400721480d00703225465070b00c002c1080800300031b144900343c00e9040918856003142c03140c4801020060420703100741d031590740401a546c0301d61800801081c00340c0310f501c1f040e0f02e100b0000702110704900c500380052203055181070b02ea10b0304800301d03143e480302d03419154681840c1400340009000300a00c00560000f5550b655500742d1101c0340450307100c45000a00507520b50030404080c1c1508059040504940d10500400c003419801c03104991060094590ba00354550781c901c0c00b050103124942e04010140201c80800c42046841513685c0051117088500d1a855601d880d244c40d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 186201079 1250 186199829 186199831
    0x90503100501080a030c020a0b1c0b040e030f090607080a170603240a060503250b0301030f0809130218031b0a0b0a02070902070305030a0b040e1b040212040b011d 71
    0x9107242c10516800000900446d100c0c584940b01405031a1140d96440002e032440d088600990b00c800c0305660318455140451003100c6591071b00311000c00c0030a4805826030b40c0c0b4014040a00000ca038000303000c00310b55450409861a0310382c88448150766070380388840200880440c000141e40b0011001c04100b0501d40400c000c0810202401c0c03840f4911030920011b04040c00140c58040006d43d40c000110340341d18203005405e1048400b484007680c41c4070003450f01e03108181c56030201c915500c0500040c000031349401115070b11150408c1d41c81d512009000d00180c0130de908550351712074491000030b050606008603e00340c01141c00c00c8050303c00004400c06818100e46c01020419401000d0b40428000400504003420041480d881100c00603611481c0400c200d91010380b090700840e070007004010a06030385015422012005644c2480920021002d4070382c1c40c451034414101d0350880252280300354032141e040d034006084040c1c5040090600b400d10491138002802044001c0946018002d1910201030100d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 186202329 1250 186201079 186201089
    0x6040f110f030325020a0f06110c030d0f050904050a05011406030103170703020f0601180c0509030d030f11030f07110d0c03030c090302040f05010e09070f140619090503100501 77
    0x5140340c0380070328460500c4c2001601a00c0b6458004600c500b000d6150040c180c006884082c401d44086414600301600000c1c2d200305101e241d50000b1818080c0341c03004129440725441c1c6d414401c840c29916541682c913805201000c82c0c00a142000308032a11685400183c100c5442c19642ca51031060ac2c2c1c1403100610090002500321065400c070805150f041340020000c044c000d2042d0707403102091005440c144030003a44465000d003810600b410401e00c03144030f2508209602d04215203800860004a9141d942c1c690541060603a01c040080b00c8400c2c1d5088051000d90040d8034aa1b0303445c2c001004e075040c280176544480080c01540c10715082c4000016161040c00c419140c584090005507001c4001d0004e0358181d500b0454107030303c00401030715203000f00049120f880002181a60402e440702e00e190100904590450307200711030400c9000c82c03100c1e108099401030801441c04116090114006203d528000824801400440d00c2a00c0c3c3c000c00400681d8401c60680d000000e01815100541b03e082c020 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 186203579 1250 186202329 186202333
    0x803072a0318050a0b0f070f05030d0b040e0607080705040504090f0611040e0a0203040611070501090308060a15030e01020c0708030a020105010b040e01090b01020c030102030a0915091a150306040f110f03 89
    0x82401015541d50250200044c00c1c40702c6e40c5011096a111401501540c800b2203131940003003041c48080c4214041e0342e000100c00c0c0c2e4100316a1901440c0c0c41d070b8460001c0e200000307024600c40410304403840b0300115809000060030034070024915180203954081ca0503030503200c1e43d182040716080f0031072080c1103030221003a184000e1350030307100c04039110020350000e0f104540280d0740d030203030310700f510b003580701402206004000006000d121820040d0411400038503091240141c00703002e010508079103452890350289031400041750200022018024891289111060320602c1400582000c00000411940955078001d11060740d035000c1c100c030340c2c0c0543e0040e04403000e151001800b112150742c0c4102d079070391814070403030f41900400b501107401c99000790742c11590b5680300e030388680520050240d03028038035406600406c0750080c203855800c11035140c02244844540103401107900301c4400b00c02080c01c240e00505455190a0900e170018140c1039010088519100d0052481210300d458004031113008400740c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 186204829 1250 186203579 186203599
    0x109020414010f020304080114040b090a081b011119180303090510052a1b0a12050703060204060e15160303021b06010e0f090303130803072a031805 65
    0x10342d003c08403203c100045210602c0009181d40c424081c200104450b040c0c0e0041900b054104141d5980001303002140581c0015031020010300b280044a50f00c400e80f2444000110b00e08962502601980301c5104000300045400911a13510b0b00030364074802c089458003640c0c545200c0c2c041c124100c0501c0081c012131100541000103040910110955a80c1c1c1e00c0c02ca45000340c0108001c42503c0c1c105551007500c80c0004160303500c00d208001011217040d9903903a9041c0402400300041c0790403001d01600c19010640e01c0003604102007000108069680000b0039034495444820091034407030250081440340d0300c0d80404640c884907075821250150f80b000740880640002c0c0d2010750103584091111104400e5850a207549601c00380100ca010304808070485141d4280002044a4860044c103100d0441d007041060000441090b2510010264400780c555200e94584006690b80c021540c031003000b04000e054490000380b210519000310610079140d40c000811000c0e17030426100443d00541e90402c000306 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 186206079 1250 186204829 186204869
    0x50105031c0c11090907090c0921030507240b100507060c021914060c13140103020f0c0d0206013203030d09051b060909070c0c15020c0901090204 64
    0x318140c0e6014090f254010403014001c011454a10046550402c0340c0c100782c0e0280403424060261420340c00b29842c01044e00c40c1002810651290000c000e003440d60075954100301058000c03001c1d603940c150003c0302495000540015000b88000800900780c04a15041d00e41c810b41ca4440341004a8441c42e0fa200ca08040ca1551000d00070480d2008007003e510400c41c41070809082d400c8803d02d20b602c6001d40078064190b0040039494520b01906802441100b446070500100c5902c1c2c034a0100c44654424410b001c08080050f8001d1240c03610074540d4401c0001c005055410010340c18603000a00d60845200da030340c64081442c02c4540d40c0321682c100c0074801d6282c1c4030f00070b05220100d101c40000c00340c1703161092030150300c400c803502c3d6001144e07150850612030607030005203400380741c20b13003010355485207401c4031200000d40340800206030606114507101c81800341f1010416800c0a4541080d03107203403240c0b00c4003001c0e656201c070401c1648990320301c100115402d900780c000d980440c1e00340c03001d1409140082c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 186207329 1250 186206079 186206087
    0xf182003061903050706020a05010614010e090703090b01030b0712050c0901260915160507030f0c050708100e15010308160b0c071202010209130e01110c0105060103050105031c 77
    0x94041045a000b2000c000c408140b0030300000008024a030002c20f04a0b1107450240d0946500341c1c0204804e150100f2065402d0340c114400f07980c40d5000b00c1d60b000c2c441e40e4401c000d400a0001000140900c07503208008801c0120140b0064010078aa4450884000000c02483d05948084515001044e03081c04007110b903500401c000c000301459000090804c1c0399005094a2040d000c56403807d003544a03000103da00341658200e242c02c0f0950301b03012a840c02903a18013821728421542c00600304a054000280d40520842860900da980141994441c0340d54012503550703070301001081c02140346803240c00a40150005004503900e0344041e07040d000d070383c03854a0b42044d54004010420540013540c200c0d900181c41602502c0c894440405055207890890a101a40d00f003040400ba0540e84100041c171170350381d50981581c0c0c400c0302c61000070906005021189001d44150346500858120110740c0900100301904a0752080d0030030780e0b040010781c1c0ea50301055555164880003e1403c040040340509152207 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 186208579 1250 186207329 186207349
    0xc0a14031b0d021b0d03060e07020a0809010521040302011104080a0b1506030a09051e03181f0201022d0406050a050415050904050f06030309190f18200306 68
    0x300080c01800c0200d50780105044134440d008001c1590010309511356555010301c100320280c58020034041c00f624003503101950718801914050851000401c0da0346061b80f01d08216401101540704284c0300c01004030f2a4100c2c280c1c155401c501650920340d245040c4e40181c801c1c0e800301c0340700e800100070b400b500d80c407452242c007005051280103c0c0e040300031030301c1512280000c60291480140006d0303000240c0c01c00a0a002d07000d07841c00740c3d20066800d840a8810b0001c290744e1280e501c070042c441482c403c00700181041d04401e00c8442000c14070f00f81c5001298065026255404c810019100d150b1109401705c22968104180048052010f10061150600c64000b811311310a09040c442d02d041e40b5054200c0300004206909400100002000340540c140341c060b0642040b04002482e0150801000203610f90142540304c0d409060a004a00d28034007142851000800c2c043d0b445011040d100d401740351114a054641c0150541424401c0340b820901801c40c00c07003a040c4c0e100c15070540c1c4400c8c04200d40020 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 186209829 1250 186208579 186208597
    0x21204051e060c0f060703021306110a02090114030105090102040f03032006040b01061d01020c060a03140a200309150a0b040c02030c070e04110103020307170c0a14031b 74
    0x10100c20400d050b01c0b000010f25038020701c2c0c001000302100c055121490400018514804c160061048500e451114280303d02a144a4280a88039100c1d030000c46103040402600603500619160000512172600c0b040c0f00c485940550090015559500900d03003070380b09070300c207200b9054842003081020030b01c290f0040004030b8000019510044526440900d09641641d043da00391503101d004000c031030340207044005840090416000b00005074030011b1749850103485064091000045c506142e58404c0d80480d42132826450311f42444d0078030343c6126000345940010b00c020020b41490000c1c402c103c610039244101580c0d402408c82c2e8001c1d81501801c800050140300040392201800c42c02130b655070048641c2d1900c642e000b140c60b49424612146840d80c0d60f4400d00b141c242d46418400490041c01600180030006e080141e07a89d00d514108a41451012032003040c805411001d001c962030340c020003444510341e20f40d0703030042e4030074a184171501e90301c400e680c00140094035048441d00c4450300b03406404c0b441 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 186211079 1250 186209829 186209869
    0xb100c02061b0a0c0906050108070810170f0307050d0f0c05030301090f0f0203040303050402040b06041d07020a050a0b010315060528081203041209050904140c0a09020c070602120405 80
    0xc43c6079a901081c280482d00804103940c0c42e16014072055130300540d6503911041e18036002c4403c0c00c0c4110344401d1a0814014060345030880c40d02e0700e0600408202005004003403500300d81d5246000e0400700d8807040c070310800c0c0001402c50035082c041c0c14420402410704a0300030f0061481d5901c2c0858040003408000d00c1140300c2616000c0d0400f8000203440a1481140241c5001c50b81c4d1806104100c105d0761890329a6102d03400600c001d000c0d000d6085035414840b4502e40e80340c00503032225400ac1e031a00c00e040000401521640c4a420104003401342898100d911a40c07030443c1c40c0e44444801000ea66090041036000b2800c20442b5000c5e20f00d01a00a500b00354100e21428502e44658250f814654002c41000034400000180700820a0203141100c0320842032500341502800e24002171140d41c00a40040d04c030340399410744903150301010310001001c40e00043c001c10501e40d03600b50000c041d401416940c4441e004600300000e40758008541e90891084200f00d162915050a04212580e410300381020018 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 186212329 1250 186211079 186211093
    0xd050f01141e1e0c0309060619140a080118030806030102030f0c07031101060b0403020f0607020f01050304080d0f140711100c03020408010203150306070906050910050903010504060b100c02061b 85
    0xfa0100282501510b1180600c1e5960702d00085c4c118136180300070f4a41c9000f10b8030750f049940d40c01500251a000c1d1070340c0381c49468601e6944800a03003140c0240e005007045500e03100a000040807444100e803913861003600c2c1c08085540303801c1018201d00040740c40e8540c06401000041c0e504504400074001180301c0d040c00d0482d440c1c0480154210b8070540c01c4240d81c00c00001c0c05006516006c05481403049003114010310306071003640801d207100f10300ca1045042c000040007050030012420140c4000c5030014000b040281440b01028020303100c04502d03050000e410002084805100c0c02805140d0103404000f846481108440d00c0000c00c44034041c002010fa0a00c80403d8208003030000714041c1d0040040d140340c0c41642800c060510b8030180c480014440f85507820806a0742250035030301e0111040b100d00100d100881c800b0359207442a09c03031143d45946400c3c10002040340a90000c1c0001506660001004450044c165207803500c030700f0080d5010034107001d02c8801222581c185400d4464060980e00e00d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 186213579 1250 186212329 186212371
    0x5060d18060c110f0609031602010c060903080114030609060408090a050d080d0c0f0c0602090a0b12150f01050d41160507020409050c0d050f01141e 65
    0x71541460300300c000181008203c85903640f030402c1540e001c031544002a100c2424130503055a40d910455000505029840c690744003507a000b1000d11130300070b40024080c0844d95091a0092048000340110a60340102c0c4d441c10116040001c0c12a208030710307a800800854a49440e6545190003010550360300007a5a00003140540b9611859911a48941c000031385842901c0301d15402e640b11032421004110118030a09100340d03121040d803124603044240103a49050090100d83e6101c010707000050702c0040022303404408001c00748414852141070200e0f4104070101410000c500b05480010383c0014401d10202520784210303404103801f034120259044585650380240d4440e040c082d4038a030300e804d400c00880710710b400500d80495886a400d8060300411841104050198010528081d00030340c0d960482e801046401c00c030b581011000100484201441441d00c2961810319035445404c0d542420840c22000324500c005600035010b80442c18103012049a44080b0400300a02465440b4000050000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 186214829 1250 186213579 186213581
    0x50a02041203020a06140702060103030f0507330e0706081026010c03050118022212020102160303140c0102070609080a030c0c05120904060512010209130605060d1806 73
    0x807400d01c41e4001e03081c0901c181c02e12904a84404001c620701044260402902c0e43c0d010950505580d49800c010b081c3c2e0540c10070445241c0150700380209403002203403e40c80c401402c0102d0080742d81c0381000044070202000070402c01c1e600ca660881d00070341e100341c40c00d2000c9402140503a0b480140101048a0950b642c2c5460703144443c0f081380c0c4512010313095010a0803007001e006a03d0303003840c2c605080c009075150519600d84c1d4030600503940030340707903011030b540e200408401c07a114040f103480800d02c0145030301c5009008200c00d114600324003602c01c0c20004c484004c14000848222605a00e0760100080a080100c0b415841901608441e540c01c00c564030004469100c0d882c66a40102c0c000e503225400700202600700c481c06100a001d001c00714000b400010000151240380c006182451600d840d81440410007809131070700107a034010125518800750b074a0542c050071421008491130170108020a40c200c04580c2507008440d000001088564000700c2c541d0010703000715018030603140141c0c00030b0716550 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 186216079 1250 186214829 186214859
    0x60316090b1503071808030403050c010302300105040608010b0a12030c06090f060509030711010509010903020d050109060b060414190e1302040e0309130b03030705100b0109090e10050a0204 83
    0x70022811841c060740745d040c900c20354480544248002076282c5400c42c0c484583e41e0f800302112a0426400003501e41600020040515941a100d0429003040a0640c00001d00040c00d00540d400340b41303003e80000e5554414028a100d11401401d042030142c10301080443d003602d100c1040c4c051151903060080003446911500b22244d01545111901881c5454a4802e86e0030180201100358801e104240200300b0048840c0c100a2003403c00c0340d41c1e0100c0c8001a0760b518180d92000e5840400d80495106101c0b06401554600c0e12442040160300b90b210f00300002e501840c0038411401c501c00c1941c40c8903003450b0124460309070404960500b00f42e5220202c400da5841200ca80e00941c07100300502d400c42c2054044c00341403005010107036080028460121b00004080085001402d40351301101606841c1842115412a0081c003580d520424051080024040b00c10000b4001035a0060006280d6003601ca11980640014085e003940320302d905441004d403c01030420014503600f04400640032000d00b03984 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 186217329 1250 186216079 186216091
    0x7032114030109200304031b05120c0319080f010303030509010b0d0629130f110a0f08070509061b010b1906021005060a060c050c030a1a060316090b1503 67
    0x100d2a84e8001c5020003850000c1c00b038100820f1014400d000000307410040880c4504c10380c4070284500c0c800307400c00501d0108203001c501c0401c0c40001d40d06400001c088024000301c0031070703d129910300c01d41c000c0484540904aa8951144111900500004e84641c103c6e640100400c4000301e4400740140010340004140d50040310b042c0e13610a42001241c000207403c3c8000c0303035440303280114200e1150208500c1d142004c0d51082d80340e80c0b400c0707600b5914540e5200f051703581d800e00d1620ba1140700a201c0940306c0c10541c5249030110f1542800143d90b280f050085509600c40500014181803032040090303009039000b81070399095529240c0c0c030036003034940018404d8000d1541c01d01c009420701d008800781c2480c4401c3c001401041c10181081078507220440c00b01c00320b88040c6400a06030701103050183c202000e0395403142d4540a02515102030040c02c1045410100c3d1802c0c955580f510782004060355241c14589d01c141c02089508200b00b00e103019070100111310700c0070b41412a450350064028516074011105 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 186218579 1250 186217329 186217331
    0x1180207050601141f090504020706021c020c0601090e030703110109320106080a02010804020a0b0708030403171302190302280501020f030d0f0e0d0c0201020c0307032114030109 78
    0x4c40100340c9000060300050320100039500760036254403031000301b0701d4805000300d0303000e150000340c100c1c10801d4a9040b507405050b0300110600500750145420013a60203200c0c2da0415200e002d0003c81d6500540c814410074500001c003c500c0c0c00c03680d640940307094284000464880d5a10030703062000c0b1b1603620034a079000030609580d40189505500034140c001c041803075042c450785880003d02c442600040c5140003103409080040b90342e030700c51002400309041ca801c80300f0142008104041042803003030180d4000c52082e1a00324030344d84154420805420100c07044c3d10060070b1050b282015040c001241760940026003030080c01c10792660085822203103c0303142c40d841107001014070b4060440280307881c00605800d101800000c40d1745071110383d80780224241000255510b468040340c0c50000e1307212503420220303002074420786805040c000c1c0130354500200903800b500800c0d44588142c64041380da1403d0ba40c1c03141804101079602c41100c416010400311250502c2a001c0344050103014481c00340d4020001050 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 186219829 1250 186218579 186218609
    0x12031b0d0c0c150c0c0209100515190c1e080c0a050a060b0a06090e06011e0c020907031104060804050f0a0f0317040b0705030405070e090a020f060702030601180207050601 75
    0x1500c400d055400140001d5110f2500c2e110030301060f0f005e003141d6140c0b0b8040304c0071460740c1c440001c1140703108081e034001c81d4007820040d00f1003140165000030700042d94812a094410301100d4500303070366251003010010b08102c04ca0741702d2069900802c43c1006494000c882c0c0604055204200600d401e1030702c1002da0381c03a40060320360f40410500e800780c041c03400b20030703074038103a0240c82c0c800007506c0c01c0c015026a17410a00010001021039100d4051420156035002c1c00000b0b110310484042c0c09445002c80a0380510032060000d16518040e000308440d4103c0080118609071501342c04032529040500708036a28052007800042c0203200b08400300c01d1074054144a18a149680740140c01aa1808c07415103491095a0400c00810301860700d1640c03018260800c0c550b01d54407490420b042c9000741d041103001080900502c135481000094804109100383e59158515060104104641c0107a11009500d90300c0340c0010701c011502c0c40b4204c001c002120001600301641d565a0605101c8240c01010354081111 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 186221079 1250 186219829 186219833
    0x20a050c0c12060c0a033909050f01030209030a14070e01060806030318010c061515020106050916050c0a030c02010305060612010b1b10150812031b0d0c0c 68
    0x1c4410301c0c12120403111645450211548075403102c03002800b81034034a00c08260200c80d540a80c0154551a882c01d03041c80104002c032896065280c0c3c00300760103248000344140540040d0240c00007000741c0d1001480c000b41360550000441c040c4d400020f02c00d800d4010b003000c010006010202131960551241c0c0070700b0181d41401d8010100e8a416404681040014070902005803000300480d814880d608040c0d4890b84030900050700c1c011040c540c0181458580250004441d03600c0008006841c4c0719140b8800000c007a0900302d0903510b0601910f030340641200c01248100b13a8035031100161204a00b021401c000c45698150f041044440c415800314140f502800119a49841031951041c1c0864000b403c0840804c40c62240f001305009948001400285a4052522501d00f60b6820b80c00001102c170440c0c0c84120007005402202c4043c1881d420440010840403408079000000c0c03104071000e24150f98841c0002e000d0a410300e0b01d40c11201004004d0350000c0a8103008407003212100e511a000342201c24 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 186222329 1250 186221079 186221083
    0x1110408010f0c051204060b150309060103020a060207061e0c02060406020114060d0f170c101b05030403171306090303050601080f0106020c210706020d030e03031909030e04020a050c 80
    0x7091950007081307410416440418174620710329030031903001140050440c08a030b020451440c00c440b98074096031004420001412800962107050720f01c207840c2101130076916030b000e90b03907085030b0b02441c80456a140c0000d80c0b0b8038000c616a014210b02403814494200c0355030085507140c3c1c0f00b504008010303511a40c10080108a410f603050300400191008510088140c54150312200034140c002e1009214030070300c112040b1301209842d05410090300341c80c203801c1da69580703030010007680b100750390154038407241040f046005005503031149405480c0d0007035202c03100d45c15421100d03005101102224542d83e804002c02d0b241d00c9400446403107504d0005050074000005801540000c000240103e01c44006102d80303030380482d004032071a0f03055a00c02400d5203076050100706402d4074520029184a08400000c116900245001e1160381030f80b41048030080f0300010359244e00c0101d41e510380e10759505c0b410700c04441465018032045400380c40c00310416503074240060241d03400410040c0c0015030100c0c030250701d0b0000b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 186223579 1250 186222329 186222341
    0x6080714160b0f040b0903160f020f04050a0e010506030307081603050c010f0212100302130f1d01020319020301030f1401290307060516031b12052503120e01110408010f 74
    0x40d40c011810900c000d406190040310403a00142040341d003209c96011510384960340300007103c0081040c040e5140000301000101950301e40c403040d07507003004e0225010742008400c4076800c942280b5407034508001607184061911588200300c2c03c001c020004001d100070203103c0c1201488200401513542c604000c0c43c800241e4001d086104401212801040181d44000900c8004a0741e40c002080407070300740303004800820f0b2124440080d52041e04990100103410760081d8450034019007130380c0120060b008940308074002408000c011240d000405404104800d08241c031300881000041000c00710015005242d88454420407030701b5440b43e07100e81c59498184050000303070071071785840c0382400714403007100c02080f4442d207000c0d00707100040006251080140e500352880d1a040800b44000c014070307400060450380300300f40c40b0001040800f404d9668044072003204038007981550719186c0380f40903117181100420044200121035907945c0419040e15400030060002002c1c0c2c000001800e1803425825015a24 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 186224829 1250 186223579 186223591
    0x10606090e07090e090109061a09070801080c04091712010e0a02070b01050f010201020f03010b040e0a1b031a030109080c100204050904030f09050a03081306080714160b0f040b 77
    0x1d1080810103101d0f03024040008031080c20304000499150545500e00401e4044005403c40d41000c00e880580c840c8402500e58031042900e105006a8032841c085541110070b000d03504030341c0c1104d0301c0702c481440c194102c200c440e8010114504543c0b1210300082c2154030003800e212079450054010000180c103210a41d50004070b10806501e461020350321808840014000d8900c98881c00510b0440f90340b003503050320503040d803031a01d03180e6a58440d0960b4110b500305c0e00c0307204e00090703400700010192066406200103031010220746e5489116272480940141400e40d241007450f0843d100040441e60b024011020358078080c490680c0c0c0c0b8146421071702d0510f084a0b4501000c00e0041004000c140c80d01c3c80c00c40d500a805203006600306070014811650b0302400da10843d03000711020360100034004424018840c200742103001c5400c040e0380703160542ea20700c001c40c3c840d004203901e002040c0552a541e0003c001c9401d400507814181400c59507030402c1d082c03056520f07071140c2c0c02d28002c1008104000c10034640082e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 186226079 1250 186224829 186224849
    0xf1f11010c0c02011407020904080c01050106020312010311150f180909151003050d03050603010c030b010f050c010204050d03020d08070e031c20010c0e091504090311030c01060609 79
    0xc00c03680780180040c07620b504003c1c10020600b5881c10704080c1c0c0784c2640c5016038018440d01140c200b03400d103c0501c0d040b81d070b4145241d500e84000000c0313090000040755070070380d030700303541105260310f1074039018140c184480480360071844407801020201d043d4401052394124007448540c95130759100c0e0040c00303122140b0340c05001e0b918100a015509100090804804d0401044111241d40b4070304074100c00641d0703500051541c0b00c0c8a946500158041d002144925400e40080000841e440350403010340d40f15140040c0403035894004031355014031440040000704040c400140c03403d0f58840c08039809040c49001540140c2200c0003c045117680522429005046171400d84041030341c520020392203c000d02c40d42c24040b5180c85800034500e000383c0a1060200200c1011500182c1c0814002c7c040d0100e83c621800007020100c000701079151000e81c480c09445400380340128202400180401007220107070603024040c001020700b284403410001400446e507817030700106409240c000b018004070b440d500008103030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 186227329 1250 186226079 186226091
    0xb040b06030109020703050c06012402011b030e03160c14030303040302030d02030406060503010504050a050105010609300c0f030b1003080901030c180602030403120507051b0f1f1101 80
    0x29554080940307064443d90200180e0b03030750007480c040d030302440351250304030f143d008640c0000384110340141080e10207001c40300544903983c4901070407400c90340e10581d4a00c00d0a0600007246500344203074005480c07a0f400130f08580c5452410741c0030f0141088064400c031114800e02105001c0481c0c84080400d4240058000b18103506096501079164018040c85e01c601c0ba13800f00000701846025001840100f1019000b0000c1d8145428130a8644141c41010344896080c0400098120710400c44c4208030741c4c0c180f00c8008070b4800c01c130320842c0d0b0156814111180100781d00780c40010443e114a00c0d03004001c1c40d00b0f404521740c910314000001c80c03002001e0303030180c8000b01d40c01c10210301410300702c80c070a107400d2900007201061041c01b520f01030302400c4030641c41e03140ba20b404070307070640c0000080094074090805010260320100085401d48035611740140b040d00941f01c40300020f030002c0c0084608102c0200181003241207a808a40c02407801601540b0a03400512a884000e801003801110b5000b0b03c0024012 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 186228579 1250 186227329 186227351
    0x30f01020705070918060207030201232e0306021303060c0203070b0c03040c091e05010e0c0405010c080904020a052d0910090e0708040b010602031201060e01050c07080d02010b04 78
    0x480503c0d02c65464942d4807405401c0164803011a41050154011001c644402c201d0400031300070010310b6105c07400303176600d2581c0910701c5610140c4da5120b170038024072400c1c40c03101a68044c0f44a001c000c040c100d4001d10200f0110005035540060004004140c0d0030308180e52440c14a1820780c2c074540140e0042d50010048400400c03188603000758490108941d855498070340303103001c1005140540c8101402ca10b003400110f10000d0045205400c41c101000070300140e41c070b5540380401c0c0343d000d0b06d5160f88140c0401040080e940104224180c41d40501040342c2404920b1020030180c1e8400d00c0d55034001100001c005a01348034025900c1003044101c0400e4a10041c25229030500d4866003882030301c12010b1017002d00c442d500c50010900a0004061000e4060811880245c9220400d4031700311010a40c1c500042810ad1000080d80d010040d04805c5460310792070807809503500241c2c3c505442c100101009800a2000c0c1006120300400e4540c00a00368a090580024211108008110305c03903401d220483d04 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 186229829 1250 186228579 186228583
    0x8071a070f0e01050a051615112706070b010e0601030e010219030e010603060603060203040b09150601080a0902090f0108070902210601020c0d0503190302090102060f1008011a030f01020705 83
    0xc02e04420700300700366241c2c083c000640f014001c1d131914040000038103401ca410042820401070a80c14142e8040c00a074078004c0100c089401044095801d0210011903030b0903440b82400015108103001c0d00d52803800340a501e031100314103070982005085590190030300c5901c1d603161040c145c200118200840c2040140d041118545000719681c104040d00c400440003c90fa0a40c407010003158800c004000301d030b03903a1a100020b90411203044d510742510303070002807980300049500002c200c506442000550b03200741c01910318410191a8480155441410200584030948814050702c204071201042d0346c5800180c80c902000780c0c00c4502d8507401440304c20f941c84405100c080e580c14030070840e00c50543e90940100d203002000301d08698042e403100460424070001000070300c81e1050365820310f0b080c0703000d10701e05078160320419202c1c41c01a84030000081034004240480da8000b1612501601419515580c0341d0948051507030340305110810000d40b11349071070200f0008404000001c029810a41107844490b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 186231079 1250 186229829 186229847
    0xf0d0b240d21110304080c0a06260a020f03090a02120c010e0d1103071203031a0609060d0618060e0f010e0415022203030305100b0306150708071a070f 66
    0x720b0909141160107496a000c0c40310f403c402180141203d0302c8650310340348290707204d0300c1909490203241021008250207220341c202410641d903110350482d8460107901c100c0c02222001b0034400070345038288803a102031003600d401140113005040090010303501e2401000003010b001d03011070304164086541c9000700d0341c000c1070711800c0f80c100322481f1510101c90305221103003500034051b066040c050950f0100300c000b40c40b40700030707944c44c0659801c2150038256400307040404014a002a8801d0044c0311212080c90501c00400700382c0d45060001c240590f407041414034040c80b44110b003841b1900c8000c01e201001c0544000e80e0310a01c0c0d08405525540340000e560300e03a4001500107000e003030f188000850200c909804a4003541383c0f031036105d10b4429402d07581c110030b40c50f28041100001c1c01e010101e801d56060701151015511144041442c5481d80c20400c0080c0344002400ca000d07400c180a41404038603040e01074110117004e0024220100d00641d0440301e1545c0c02000c03c0c060000c0d1414558031154000610 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 186232329 1250 186231079 186231113
    0x180f130c030501021306031407091518060809060109110706230103030e15040311010c0c1a0706050604090201120519050a0207170a0c0609080409020d0e010b0406140f0d0b240d 77
    0x482129203000c42cbc1140c107989007451081542c4100b15002420b2680002160b00c941d4440054402d40c0c0d0702d0302014230035203020081c2481d09600a01c80b01d00400c0316940703c800d89501c0c0350080c01c02c0c6c00700f80c062805118400d81c000d0300420b071580c11120b003a00b8680c041d0b81c18074101c45a42403620341141e03181480310100105060402c0031541b400300c100004d010811015200c021000034818140c00c82800d4641d005000c03c990284c204030100b81c450802d4000d03c040c4070350586544070100d40d2400c40c2001040010200c85c42c140701c140542c10741280d42d20555008004010f405030340d402040c24001c03d00c1c4030031400b01641c03040810040c07000642c031803a40d290095112001160702c140074144284a4002d5400001e100391001401c482c022000380e000925541840d40280034800d450703401c120403100c182c031030f00400c1ca124400c610000e00d04510001900400184046000040c8ea00c82c100500b00844040c140c184800322800c0f080c2801550116400100f03d81041206429507526804030240171a0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 186233579 1250 186232329 186232349
    0x10f0e010e160b18030a2d030203121f090e150105010504090e010b0603150a0f0b0703110a0602070b010f0e01030f080a020a06020c0a02180f130c03050102130603140709 74
    0x14a09001c02403001c130030141340006084410051441c03c00d01149281c02d12a02c1d80c400d4214284039080c5410f1018003480b64164002c0c0d410000500044146024000c122a00000072040c51ba00c814001c140c206010b040003800001c0d50103d203c000e9803503c0244100201c5ea5403142d80104942ea9002c421178050360411180461010b02843c01940582a41c1c11269840350010040008601c00d50701c4090300380904880005a0310707034503840190118000d00071848402010050f0002117402030261144585184045850303210894070355804a1708074100072030315102444010460008840d0000340a81500d180c107021551465842c24000c4244020080c104580480d0b4006000d00078060020f015030010020755555040d180740b680c40b1500390004902c10406000ea642d0341680e40301c00980305181c5500c544a003038446051508140c08007140c101c8910300609400b1000540c01e001900b10391600070808013016042c0075025042d10409861000054034000800c008280d000d10141304489440c00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 186234829 1250 186233579 186233587
    0x70801020903062a0d020705010c08010b0d0b030c0306010603090b07020d210207020d05060901060608090a060b0d1203020301050108010501020a0210031a0d0804150206070e06030612010f0e010e160b 87
    0x20300018074450540719070484c44000300c1d0119101e200c3d40c000b0510144208020007819a28000645800c00203000d00140c00500344000d241d0003996a001c003500260060807034002e040c01400003480c01e000ad03080000007a445036141010446900c05580e045081b0703001034420311034400c03402442030794804a01444403c482c0c2e10701c409000300d94102c03900b050f00900b100803842118204142d070744805803820300ca41d47ca81280007038028800d5111501801c00c2c40007400310351b03030f06442c2d100c0680000c0c00c1d0035a020000c41e24200010b0008600e98204504544015032a585040000b40040805910880c1550458804007005035658001c442e11309106040028011103018131151150071302c41545500300180c0301001040c81000e6016008903040c1c6d14080b5035100220320704036141c2105a4a60002c90902d40e10011a4075041020390342c802005865051092250b9170310314290303100c1075040b0340003d50303c4204c1c40d4501401e00404141000c040014a82c00304003001103941d811007403081c209203050201d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 186236079 1250 186234829 186234871
    0x8040b04081e0a230a0e10090503100b030c0904030c0b180f010207021e1f020c0604030b09060622050c0405121614060a030902010315060203070507080102090306 71
    0x120b105214038a250410720b4442c1211280034200d14480502c01035a40320800c0e00840380c1d141d26003100d843c0041550b5000141e410a0184100c008000c0c0420081c400561008982c40c3c400300518404d80000c4800480e19104030400e060a1448030304001e40104041000c100101e40c020f07195054284c0c3c80352151086e40d4500b000c0f000c400341c10f040c04009a0044c80410051800150081c1405500232a00c4081529101440040d0294680c00894200e0491058003201c0400d4442029442c00c01d4015581e40d41c0e01309001845076400394204480d522030400030300c400003008100700d5503c0340040c7c0380c680c4206941201c1e0b8100061441c400c0d0000d40c2c8802c0060001399043d410b480007094050114003c111008031101d403906001c3c01c4104200e000c640001400c40c000c10f109018808000d49280c1c6010000c441c105c2c05848850000e80c14944c80300980d6000250200c01c0f0300040a43c0e5002d103444135050315245003040b1656005420070380c0180048025607030003107522500808110140305c4c05048030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 186237329 1250 186236079 186236107
    0x10504060e090a09080d020c0712020a030305030705090d0c03060c080f1f05030607050c0613020603130602070f1115070b061915180611100b04020d060314060708040b0408 75
    0x341c0002000ca540202d4041b11942450300a0b00041c0ca051003070300c401545449008182081d0008041d6201c0c0a140c010004030740101d00458000c02140350440c5824905000b06200b01400c4400712200c0420f483c0800a100951007444030004403454405610300b45010044a0004041c0c51000d200c03800c0c43e03802c0741c1d06d04a0203d107070050001400351100b519203110098065001940304007024010f4000203151140e03220b040050190b40240094107546440c14000500380e045070040307408540c20029600441c07120550005003d1081c00303c0444a078909045c0040c00c00c4810010740702c000c0c06c3c801c44001405510701940d000406544024141c40180f0780000c1c540c1b00d5912500103070209450307161086900c280090440005080005800c603910300c01103901100710380240d14640c20103c0c1c41c0410351165040660f840380010405400c26070042310410454203c2d52007180d6058031608002c0a0300001e220700c0f43d03c040d031030030206454603090311095956070b4000c0005244145c0054010b00952030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 186238579 1250 186237329 186237341
    0x13170702040f0f060b13031707080c0c040f140f150907020c01080105010809030d0506270604050c07031e02070306050f060405010e070e130b040c09090b010504060e090a 74
    0x1c000b40144860442d40a0040058072000d10406040c600c001c00c055054104546240d20307004450200e0a1440c4c840203050500350290304905a410007485020582c068060b0400d03100b5203004d8071140e60401d00300400c40e00500d0314450f502d81000114801c180032403400a82c0b02401282c10342007640e9040c014180d15035201e030b98030360213080501442901d50b400a030054190400b0303214085aa626400151520708040b225540268001c00c600c41c43c004113908015001000542008a8450111001c1d1224034a041400d840c0d07050b10403c00c40719103014014280c0100c0c00c00c410380d280c2400d80d10000c1c074024140441d05091f200203c14030041620803c160340046801c00010882c80c20108100790810320705542c540e2184e400e142c008141010f0b0780c410706003e682680c44003000c41818800f44444104030300100c40d003d5a4941c1349500307584984c028000070900540da0700f400ca6061412000881c3c50044806041181c14031040c40300e16001441c0880f6080308450300c446a5030344440100c00b03084 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 186239829 1250 186238579 186238583
    0x121020a09060b0c060609190b150c10150b03010618030f060c0e0f0913060608010e0a030f03020301050108220203010c020607110a020904030503040c090207150c0305131707 76
    0x89001c50004051403d103000d02000700080e004c0c1d0302c05880761420001d14907416140800384051030340410300012401d50200518200190144040e40030101e420b003190b401560408000341c0080c03180000b40181071144107540305403914403098940c00d100314481680014055072052142110009080b09268803041340196031150291144410380c0c5002405860381001da40c02003a0705140b001c0f06450b01d08407800c1000000382502a056840c007040d46c425009482e010388005c2c1d0b4403103010036000420b02a0005041d80103006000003800c4d441d004000b5410210740200b05881030006001c1c2d03070f1740702c4180340d000324034101c06615210503400707042d0b400718804000a50540c41c100c6882042600410040e00c503120948954104510340000c440d11912900300080d48030030f0300b200140019000303102464100d805182100c22050300c510407403040781c0c00400290303012400801072007452603480c081e000f84413075686010300007420106c2e07810301c1c2030901c00001010050000030b4000520882015940215 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 186241079 1250 186239829 186239831
    0x1131090b0a0f030f0c0501110c0402180619090b0a0801150306170a022704080a051917100e04030e0312040605090f040b0303070b0603191202070801050121020a09 71
    0xb542d01e01c2d00c0c070f40301240780c00100d038508a07110b000511580140714007108404440040c141501103981000003d41c030259801074104821503129038151150409001044486c0c007100d030152881d40809080350b1910781c001e0900b603800b04a15100241d01c00070701811a1030b150010312024100740f1082d0b000e4402c680054002420380a0713036015038100000c07200b4a4a00944000f50101e1081c0400598095500d0103e083c0071590004940000c103440000c00d1030300b001e03241540c02d00c040c111803071202d45803400b000000180d15074048065240c0f0b1004254000404440d0004800d15004821200840040000d000d00c110b040180b16603880074000c40140c00302c01502280c0d10398940d4805012504902c0ea03040c05401c005039007e40d641041d105040010310014015400c0c000107a9501141c100b004000f9078260040201c4a4100c00c0600c0040d070302035105000000403465544c000a29007905035000b40c0c45a030401d0010001c0f4400308018400b01030b4cc0e000c01c00041511800450a81202ca0344250049 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 186242329 1250 186241079 186241109
    0xa0b0d021f09032001080106030b030705060702120d020601031e020904031101090803090304030c0506071e0501020f070f02031606050a1202040509270a02090f06131131090b0a 77
    0x30703900d500c801303442841d001d881e4a2102c0c0d0321040100e04840c44090219050303404400144418070b000000350480c680b0003070800c003030703c9148a10f40d07080000006194000d079100c00c00600801145c001d60303013040c0340d100c1200080304d810b68000a10404000d0805021700c1801010407560080039000315042c540c00060803592401d0080e2a1543d075803142c40140e490300c49008000c00c0302d2030554115424190003195182003500700c1c1100358042140f9403002c5400c0c4d9030030044c04814020000182410130f000340d080111004550050500341103070808910a0100119818401c80350000242c48000d00c45244c140020252901c8000c024800c40e04060382c41480b1404016101640b00071000d103040c0110701c001009003005502a68411601e00004d41c0326100b14000341d0940f58604030342d40e1102006108500c4103000881407021511190302c4080362840028620a240080f00503240d0001c100041e662202c51070070040200ccc41c00d150117606d0945440e42100306403540c039000080b000d0b00d0411964614 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 186243579 1250 186242329 186242363
    0xc100c0605010807050112050108030d110c01050406320a0506030c0a030b072304061b0b041a060303040b0f2826070e010c0302030d090b0a0b0d021f0903 67
    0x960903407403103406c1c00541148a40581e11400b40500d40c100c0316290001e40c10088a1040f1001412101d800111b64110034005400005403d01aa90241e401150000b40424000000c0c01000c501c00d50340030342040300710180111714074070801e200d0f23480841000c00040a40711000000e0030310509080325a40700d0350310b030004024841d0882c1c5642c008c2480740c1f20030101c043c2c00007020001600c200003080850205001c2004514019007450a510400c94140b180c840c17119541c6003c0240203480c15104c80b01440b2541d404481c0c00c118158110004a0085050501e01a00d4582a103d6004004141200403071540e0395081c0c10301c8410111401d150091100e100c842e81c005006c4441340103070b24540e01200088038640551090356602500c0e1950b218440c50b8591001918140006c00f03088085200c00c000f4000035103514410030141e03d2007a00419441d042a01001055032080035419201c0d507600d41c14640181d48081c40142c0412110045600e07042000c170382a181e0043c07592019003400000e41c1c090803 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 186244829 1250 186243579 186243583
    0x7032a1109061c1713141806030c0d05030702040608030a0206130b13170a030e0f070f1208160b09011404051f020f040b0a02100e0c100c06050108 64
    0x1000010754070342a00703035695000c20501c0b60140c2c42c0b503602007003400c1c2c42001090b060b109800751034005110f25441c000307144c9102a0804442e5010720903044904852960300c1c600441400b92019410500d05103904002001a807640c45c1d070300b0702601c40d80a40c00740360304204090090368251600101300300003580e60340c00d0030b50f1070b5407088204c100140650380026449042d040c0c2c030080703c10340101c012807069882d120000b000100c00c80b01900d4096014008a400458450090030001000d40c0c0100f6486198074400b85485d4918099811640121105102c50708004500108468521a4030741501006080900c00c0c5d10881c5010200300d410301c07126405000e8120841c40c014181078008119070003d114000700c0846091310002d044d40c02200c19040c010740e103c194a04a2101101c005162400e03908440d402c030ba20079480100516008070300e45040c20740602000400c0c242e081424854110b4610301d86448503144800244208484012404c820b4402c1c8100e114542c0d101e1004c200558403900c10a03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 186246079 1250 186244829 186244853
    0x4080304180504030206060405040503071403040611120702061c060902070b0a09031d030705030a050d030506010503041e080f13090605010f0903140c0a030309081209010507032a 78
    0x814400015861024400103602c1100e00c11a09603028111680740d0b00c00300701c040d01c00034100344e400c1d1005101ca41c0110307840c402d5a8042082e828011a41d803881c008020300f0b010031008030340d0500c3d0880700c1520307110319110044490080e4102c9a01c2e0340c0d001c0c2d00c103d241126810304108148a403900c440070560180aa00601000b8050340002509550781441e0109070741c11600c0040004a030001a401c0320f0071240a00f6504020080a855100d9141c1012034601480301c002950310341c2c0280b0000b1340e80d80e017510503907820a80c20303e80305145141584070405d01a2030300d090b02802002c910303000360900c01442c06882040f40c09250307065645291105240d0100e13a60701907241d495103040c400103140e42c0940c4800d40014440c0d11500106491500d95032910108041a0806030190b0181210789a6a00380d0031009144641c60303101041d8100a02e8900d441486000c9034441c0c1300c1040b000445030381000c19510340035031600c2c00700285085032545061101800300764240051850380384400f005039200c030302 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 186247329 1250 186246079 186246089
    0x9101703071a06040603330603080d0b0406090c02160f1a03040c0902041706010b0901090308090a0e10060801060c08070b060d060c031e0501030807021005070206030703050114040e0705040c02010902030304080304 93
    0x20304004100009181108c041c0e1200400ca100304009000c181c5040c0c1e001448420700003480007440c265120211001d489650341081d00582104014481085c3e22091541c0a40f6083c4040c07051207080414007124075000c0f070013020030071201000180030480094041c801504182c2015529030b80e848200202c4001c106d10110300900582d000410904400000e40d07001d003c0507036542d40070034995102c81c501540640b141a80112a014001c034008000c01c0005008088210641c0c108911708103000701400010780024003001045d10128000c00c1c003d0040c0c507030450f00948903140030b4032907000060410340f5200001f090f403401d180343c1c00d800d1070f0540c0c02112000414a0310403000c034034045d407010441d0300900004081c40710502810015040c2007040c40f00e05012403e040d4074101e00c07500000c9040d0401c40380d800020307460710014440110080c1501c106440705541c03d100340190001c413076456030b80d14010380b4040e56856418120303851003500850704264000c1d0562381c1e41c0748c0314403c0742e44980c0a4050 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 186248579 1250 186247329 186247403
    0xc210506090105090c060702040207020d1a010b0a0e01031d0a140d050405031c0210050103050106061202090906010e01090504022107050c0a11060909101703071a06040603 75
    0x1410800c1c0c180100e522503020748010304070b030301c9030f5800b080f1781a0002c0d102641c101e6800e120480040c1c13140424640920f0040034000748100a59111030f0704901c0c16000381e28503801c140729141900e9042000400c0c01b07042401d0125404503050141c03210309100760002003080c81901a41020301568890b00c1c110030240c94240e49540780d100b901600c044c8518480c2582591180c140340d40403104088180e8021026403054074007100580070300d00181d40d03003a08241d907181d55404042004e0368104032815096210104198140f02d881c0b00000c0b0303405c0d00208584e060242d005c08411843e0f1241903804054000200b0454403480e51418029400c0d061521800c158407100700030500da58043c40a50f819007240d90010090714540b50b0f1108081316010f0700c625004141848003d40c04e40da000340d012321402c2c0700c12120400b5441c00c4078070300c2d44250b5407509803840e07081000500e02007101e50400040d030001c429962941d44c0c4401001c00c004001507071000c1c01090030751000765020710b5034501002402c4502c1c1d903 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 186249829 1250 186248579 186248581
    0x72907030c18081906180c1811070b09010f020c152836200a050409140d110c041103070804050106030203060a090b15030304030f0c210506 61
    0x628070692038518052504540c1c40101340700e00c0c0b0410302c0c03400d0140e144a00c40115025009280b6140030814000e001c54500c4400041804040c651050640d40260b16003001c0c070041c0300522540d820ba11800001078070320000d0710005100030900350884c103010340c40c800045544142080501c0c1d15604840411160001c141c000300342407000b035000c8902c00d0008224140212101050580c1c0103040786102854882d14000f407803094030840c200b1b4042c4160442c9841040206a817401403804040c0034010350b14500c6498485140741c60740800b0506541c2c00381c800003204a50b41c104541b91103840c9a400c0d03414400c800b00c00001c1d541c07040000480200a20031614480380c030f00b0402068402c5158555605202440000c241901c131300c0d10150803e024500000c2d01c1c80d00e940100e814450102c8503d00c4042d19456104100102d488006900c80c12109030a400240c8040c000381c0c4074403c034400903140c040a03039501014402080d092800424a04840f40080500c20b03040e0b02ca0000410010741d501e001d00c074 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 186251079 1250 186249829 186249857
    0xa0c14180601081f0e01030807030206070c050c01030e03070c0b070203060906040809010c140a031e0311030a0504030516150c030515061b01020f0304020301180305072907030c 77
    0x308a20300414050b11400055594101070a495514011807083d00740c0e8410400100b483c1a00100c80c045c5000d00629aa50103c1d403c01030701c1c01d10041c100a007007051140c1c02d2000305a002c03a85041c616400d00e00405c0ba09410192945140104800a01414140c0b000010744440319001886d4091013030382902e4250741c5408250f034468504a40280500c9020401c0d440250b219a0030024040e205e0b0345103000300c40130b001210780786c2808820110045a818000480344a00901741c5100b07003100e07840c091103c14541c0c0004806408090140310310079480b0408101014024801d9a20b002000c81110440030003d0030f10400701030b070440030713040340c0ea1512440400d022f00c00d022301840b5000c0c101c0c0702d40122210a090000b03503441b40d06c0001d541460411fa00f11802020300040c004180040c1f40381f0380b01d041c180105070071151070021000380b01010b4034a15000913005429038500d10b0b0018002101e2840c400c183c030076000c010044403481100b40804000405405a00c07101c00420300f0390307900703201840311 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 186252329 1250 186251079 186251119
    0x17010b0901080d140d09210206150604090c0915170a0b0d020d02040b120c0f0907020607030906020f0a050a092c0405010207170705010c0201150603020703020a0c14 72
    0x403046034000210110303c141c00c100301c0080106031701c080d01c0c01c0004066486480c0c11001c4030301e60901040280329005040c404540c100644c0e50080c0704050400c60401401c000030300700e80309900c102c048154682c900084101d02899101e0003c2c0007404186010181500009107401c4003e008032005d45500300200d81e11400c80d203c0c4211f01c80025080c60102c284540801445080011040340d02c5901c1700d00b4101c0b941c859000004000c06c00600600320001c00c071040003007051100c0c1b202801800304004000305540c0c001901500550036050000344c1c800c80c0e0400318040d2180001040803880005a04a045980100107001500e0316030b482480769511081085a14130724101105003110f07000503c410050440403410f034116110344001840d0164503134680c6003003881e42111180d00c4034049404001d0103c01c0c010040740342c03141c1c40200614400003104924001041c0101c4040544c0441c2e07107010103000708116840c443d008a03625194940d5082001c0500c402034900d20b0040c0100101c0c5c041c10880 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 186253579 1250 186252329 186252343
    0xe0f12031b0a15051b04090b041103040b1810051006030c090501080703021605100506120304150e0d0510020a090b03010b03150a0b030c03041a1009051017010b090108 73
    0x40046000300c00f00d5032885140c05443d01614600ba884076262642204da04100300400003000c08280c042150703440f2030200300448507840510149210100b0030800000c03000e0010781e80c45241400e1320355401e42c0ca50142d502c0c184401074007451041c0340ca0203104011f00000c84d0032048a0749a40c043c0f081503038410088800f06618400c042c082041300006c10400350203070b0007801803100401000c0c0c03035008407601c0316498900d00c0780381c1007c004c0c1d940043c01403d05040440b1402000100001d5160074900000703040b9180d0800f1050040043c110103040d41c41d0794009091540d56040001c440504a48200c03441c02903002011402c04520100300c0082c4484228007524120b070050103002d4107558400104502e651580c800280d840b2403440030110310740d10f100001d1400341740041100c50b100c2c80c2914025030410100d00381204059a242c1c10401d42c207000c40c10031801d43d80d000c0030118942c1c0300d036403d0104195058000682c0d5803a5403594641c0c1a20541c4000c7c0651012510b001c941e0341c0c0c1e502d1a60711a02 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 186254829 1250 186253579 186253583
    0xc080f07020f071a0c16060f08011d0c0904020c0616030e06160201020c060106030207111804030f030605041d240c0705031314030d050408030a0e0f12031b0a 69
    0x2007410091400b4001c004910440c003203100a180282c403901760f0b42000091084000d150309550424021180e214005107a84661403c15082c0303541040146c42e800d0380302205035045140b0701d00010b8203188054080d5200d0031070240042d51511022820b1648500c070403507040001c071061900001049110307021310300f00e41400e080606100d84030240f4040030030940c1c9a00c041950340810004880ca60108000c0b4002c044035980140c4510052078000383e240c07958074400d8854000d4003411844040e05030784190f001035040c100b540304200f40700340035005014644e009550051404103e0444a000b00c03000d24040a0703154140e8104800c00c00c440c10004414021a0380007411402c0001d4490754040c0041c054580602c4c00c8908100220301601209034182d00001c1000f5004d20316806581000c204985455160b42481c505050404400b50f50368010b154034981013010320254020759494420740001d0100d4040e000c003000012009c0c18543d01e80c008141316220b40c00e44241c00c09403620101c0c101c0c5a0742d03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 186256079 1250 186254829 186254833
    0x307090e1219230d0908070b07020d020106090c08150a0510020106080606040903020a1707120905030f0606030309010302180a0902190e01020601060507230d0e030a110d0807060c080f07020f 83
    0x1404c101d071000001d02c12500e0443e507a034400c01c8100c001c144007190651180416a00400d82001400030082c2500c0b800c0d4050300c0d00701d09002c044140309800c4000c9541c8128580240f840541f000800643c040506601454204050106c8164256419045082900c2d141021600c85d46c40c0c110500081b60340319400034006800c81c81182001a901006103024040f0b00300e1301c141000000d8442d240e5001600c9001e00105010750302c10002800c05002c5001e2021420f805000c41d0328004001c6074032072044550041c109a4006030341405403e5200c0c1000710104081c100c84412911000e000000b07500c0104103041040000100d040314610642d024840a44103a002e4521a4070303101c401d0360030b60411403040b10303a040d041502e845c410540e40d407407480c4404548001c0c40300100e20300c0043c2111044c051482d0298002c0e24000010076510b8108819000d000d840303800d14000c0f1420900124040c0e050002c010a05000e680c50707a841c0c0c0000350700c0c0100e03e1a0441090fa4849500507030f0703501c18541c2849215 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 186257329 1250 186256079 186256087
    0x1603030c14190c140303010e040c0824060112020408030301090e2e06050405040b100902160210031103040b0604050a0603020d1101020c060d061809020307090e121923 73
    0x128864590543e80702c0c0708844240c4500c290480c91401c58209130048181546c211f82000107002e2000700f00760003049000054500854280601418403072000303180c012041d1040c001c40e0b41ca0344510394005816040120440d120b6441e03031015501c9070300c02c0c482d140c08182401074204809001140321214501078180d0b0700204c0c10041a040c020f804016081702ca026910100080d8503103403805098829440b90324041082d140039101d0518003030741900212000d51041c00456892618144540c00480d0102c4001d0601141c2d120200c000c0c00c1d0705088101d0701c50020003440b080028200031a8000c21003100c00b8811070b6120003112045403054031001e540040f81c545c800000c50802d100d0101185010700c1520a50281100130603481c0d1301903000044c040c0e545000c00c000020455108090314802c00006000f40041c5400280e55002035010f1806641d135204507400d02d2480800c644506502c54000c00da803101d07210190044480015041c01c000b207512004491078800c40545c0d040e00e8150108012130030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 186258579 1250 186257329 186257377
    0x11401061d221103010f03141e03040305010e1207060504060f050705070b06040603020105031605040918051507080c070305040506030c0c0706080702070603111603030c14 75
    0x400e40c400d0814402000440185400d803241c41d40c0382d0110142040e5600300421140c0c5000844504422400708500c0030710050140000c41024041160b4000305100000088080c6541c10400b580c0002d568403201c0410000e20300f10003002034000c40c1d00800081082681c030b02c0916454078031100c41d101c40c00c04104440800101ba950000e0f0b00036000320030014034045641d903d2070840d03600b9100040481d00108010040001e001c1500d81d000070181c0301440090310f554000380950201801d000000d807440020014407a2050f03003502c00604074808180a4452100c181002e10480d001050741c071405070710300503d02c5e80004403806009819941d02d1800729a00c3c02d10030070250b08008021404c01030100400100b0f50340d00c001441c02404d90801d013030b070303540c0003400005d00d80003099000000b0702c005e80081111035a0080380c0101101c000341000b0414403a032a074085010f2003080c4140d1007030199484000240f40c0e041d4170098100790203442d0604101201c0b600c44943d070062101c81100d9040648031018 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 186259829 1250 186258579 186258587
    0x703080901030c120e010b0a05030a17031f0f1a03071d0a0b040e0a0b010f050906070609020d0303090b06040b13090302010b090405060708010e0601020d0e030f070311030601050301140106 82
    0x2038103000d525100000c1032003060854280c400172100c0c0e0000341e455181708103091a0480300c3d41c0c01002e0403001000d010042d5610001c5043d40c1c180100580c40011001078000100c10b968007a40340341880f50f43c1151900c81d20f0b5003103a5801409003010390b17070b420420a80c0c103400c1702d8104c030b00412340354490500420110b00c410f02420080c20781980c100d910404009801e0074910090406802d040c4504180d41c07a1101d10201210418140c40e0704100c0355080500c21507400c001201c019140c10344000f0340e6150681030100190521420081d00000ca02d008102810313403642c490003040c0c2c401d610104042e01c405041009039006406a9036019420040c80c40221400340d212181007482400042404021a0300158414404442c10303542c540082040080e595445210503026042e0f032841003015050401c0000d660348141d4181c0c0c03081c80564202403d40d503030108a00034040c064201181d00854403445c0120001c02040241800781c4a5038002154a1506000d07000c054070444050403120380c6000d004072 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 186261079 1250 186259829 186259841
    0x60105040303270b0408010509010c1e0e0d020d0303050402191a2206020a03120501030312090309030501020f210105010215130203070b090f04060e070c030e03150117070308090103 79
    0x24900a00c80c080004142280b0805817000f44850b0000207007600d00321590509440000307400e0010040c000c2010400c81168a2512050075240d00d440d250329080c0030045013071030001d0f60002e98003214008a00003095410f030840c511441c429107501d82010b03060780107001400e0140c001d94500c01c0b400f803910144000003d0284c40409083d500400051031801c100034489980b907041440160002d00d503100505800514410f84405100c40c00c104035850364a0050941003002d621200607902e0f004a49c007818800c0741c140000c1c54004008560f07030030f0f909d104500240d00c03146588070101981e0f4400c000d480400c0401504859060b0003500b603605101d8030b510342600005100115150102d00c681c005a10204120301c00360203d06005561002d28404201011a003c0e810a20032414100140030303a0008059080e0009018182843c1c600c51070301c2d0a4030031f0300e418220b0340c0e054030803404001c080840c00d10840c0e0407103040900700c0c84a43d070911142a01c0380d81c180805046004c0c20085e1100551182c0d1020b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 186262329 1250 186261079 186261137
    0x1120305090a0608060328020d0201050c0d120e070e040206071a010b0403060e0a0c051207030816140a050a030807090b070b2401080a050c0405030a080301030605060105040303 77
    0x140740650010001d00c04600ea500040001841c42e01000740780d007010840003c81440880c0d8041010143d807608005400015400a010704080f5030910116405241036940143c1310b54140c1c0d0451000781e900505800c0e058144052301420420070001078140441e5000c01c4d66815107210340c00c1e6a49409100c1c0540c004102100d00d0009500c40c1d41000d10500c100074003901400709120380d918690309000068501c2e4010105090b0007200034980094451100b46044030829600c880f0980803006401342095039a41c000380030303018000745801804088441c80c6090ba44164201000c071440c5900f01a40c611315010010a5039000b1402400464041c002d0304d5444a40340c64031034201900d513548000c140e0070280084880c69506414000c03281400301400540f40920f4001120000240000a29010b000760071031000d580d643c00450407048c2c400044401600f0b0140c203c07141c44089241c005c0d07855009101c1503d51624000205000d5880350b4210b4045980603514000ca64403007004a0380d002d007900c088 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 186263579 1250 186262329 186262337
    0x50a0b040c0507061d03190201061502063d1703090a0e09010f0e010e010e030f070b0c070f0f0b010902090d080c01150603090b101d151e120d08011203 66
    0x1140120700c02c00003487c2c01520407129000701c0c5000702c0007074255003071a0042244004049440b010b11030740000c94a83c0408002602000503401c1082e2029624200646d05c54a101030180441a650baa0701a88201c54255156082e40c1e98402032440d00c0e030060140b0310b544126440b90400020145540e5650000d84100001881040008010341118640d12205880b6519030301408070000c0284999240c2440719400785141181a00a0910354800c82600410015440c80851000c815160507a1901a880200e884250320b80741042450040b60700030031a44410824004581c003040d078001d4138054800074110148a0300c40d0b50303c004403500481500700d5559a22082040a0002011008000d0005450000f890318460500d41e4542c10020501291512030480800c400d00951541800c28017422901d604551035600e40580700d0301c25410070541c03081106075600031580c0280e0010804103001c540c01d03102410f08524550304ca0b0011029140480da020004100346880780307420b03207140da02c81d20f0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 186264829 1250 186263579 186263621
    0xf0a03051e030a06090b0a080c04020714060f01080706030b0607020607023c0613030f0f0506041101031a0108071d031b0306180a080f0418050a0b040c050706 69
    0x505076089400c125030700320348141c49660410108015105090303840b142995202c0103035040c050117a81d00c0c448015240c1c084c0358001591428070048a108002602c1d5900948425090a400301c1d06419800e00403031016000351940003540b64000d02c22300c210504040e011a0401083e5000c0103610703000030400f80d81060442c904162912001d110520409a001200300304c9070207084280240c00f04c0a009035405070804120440e0440880782001e41120f50003076101103880b44518042c1c1210310305000050035440780c20140401c101d080c1c013010403c0d24007030b07904108103060040c900308842821741c4000c0c00324008002140e000d600c18410742000c002a41c0c0c11214009644000c00c1c5030840e150382500d1100c2400e00005083e280174095190054058000c502e429403035585c0c8183c4512811500500040d000540301040c0002038040d50010400081d00030080d501050950b405400121601250b492400c0c00031403062070075102c2d0108040d0f4a684060a08141e40e503441c1c000c0c03c2c403100002d801c520807a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 186266079 1250 186264829 186264877
    0xa030b06030703060305010b0a0302011209020d080a080601080c03012904050303070f0605180d050a02151509060603010807050603040f0204020a02100612020105030c090409050d050c07080f0a0305 86
    0x10011400b0303031180e03a80011803900e14200782d42180d600c50181c600c034500304041000582c0e885035820015000044002071342031110b1002400c6504000c000a129041c04602241500d4004100c1841003000381c80c1c0e18015620200c50801d544400d01030107050302c51000b00028802c01a090400d2400350b401051803400307858200103480c64102e540700319070354096414150100099030044503002400594285200c80215603010384076021808070003300f10000c0703014400d0900c02c224400c2102d9000070001114208801c2e0700c0007008640e188940189004004543c250400f141200d040381c2081c000b034040a070912042251641c0b002e0015104ca0b9a000041c00240c2e0f501c1c030003000600c00b150020441c14500c4a00801520100d51041019808075a080c10250341c0080484e6404908520119610900c410001d0000c10040380701030501e109074010300b4038064200c80103182c0d150805c800c0b0366025a0300c503910760381c2c0c102001003000c164020003101400680620702410044540445540e0903040308 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 186267329 1250 186266079 186266089
    0x309010902062a03180d05010906060b0309060601020d08010614070203101d011a090604090507080309010225030b04030c1505040c080303040201170c040e0406020a020c1210020a030b 80
    0x500c149540070102500ca111810f00c002c8220b522494508080d5041041d004081d0241c48111804c8500a560200c1c65108200c0d0030b44c800c084c0e0690240c000c11201c0d40b141c1e0141025001110703150214031803a80840c036150300001e4801c50b156800d036125100c2d40c0c20084101c0720b00601005010090340c0a22100c001070f602404102000d4180c002c2c00a108209890300c040c001c0c4100a0005007640340c800e021940e2400c00035080c5c800c0409032140d00c05610f0340c5002c5401410383c00c101420a0003401c3d8040b80115001c001450440000d90850300c504030100101503041e5103800c004164856045000c1001507004080c2591145c02420603040d203141c640c48071307118910311985220700c0968910400080001184103800a010081d00450031440d1550019180003201c1070440022001100004d1310942e42c3c5003110080c1c4170000107203038a070404e403900030083d410041104000d030251844024150601c0840c084058480100500e001c804c0007d030304c402544010140740030562034002400180e220 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 186268579 1250 186267329 186267337
    0x1101020a0b1609050a03051011090613090b04020c06040f0f0b01061110050702060708060a090e0c040f020a1d0f0904050307050f010b010e06160c121b0e0408030901090206 75
    0xb2111450006007800240120f000d60402441000c0c0c824007400070550000e66603400702245580040c0401d043d200010140c065010701c01c4d40a03d002424aa001c800d03440d8400c200c804648050144180035020041603000341d0581100c00c1e844680044c02065084042859041c06201c2d0981c80000546940306a113000b60401c00108502215040c8182c4040002c070403100f885a1082141c0c2c10000c40003900c07210054102c80800400c1d07000300f026a0f07651500c4100400c00c8001c1004582e91030007900e5180e003c1c00303400c68031451520700c0840c0030744070758000c40d01141c22030340d101c0341048101c81403040405110b03024650010030411800b4410384270000d0650080d8051310081d41c81301b1252030400c3c41c000c0562403690075a418400c3c4402c0b166041443d841752600115440fa03120b0440c100080028071042c900a40301e40c000040020304540d4038031402d96401c0c000d0724102c0010064014403c04c0020078803580500040940024020400c07000266800002d540300214409241d50005821500 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 186269829 1250 186268579 186268591
    0x60d060f061a03011508070516030e040c09051507030e060a0302090301180204051302090114030a0c06030c0f02070e0402150702031507020d02060c0405010c051009050c042301031101020a0b 83
    0x2c0000010702030b41031200504640b5640c1072404240610303041000070014051210090440100d2024000806010b00c029800d00000a0010031219a40c950000d1441d0718030b204030b0b40640d50228000420100d004100c03011039815840301d444801a00c0248605580011200750415900f8030a030031066400303006500707181580310012103994249004210403036a02034490000c201d85580c2410050b150002c1c003e0444005074640c1c0303940440e280100c3c1c14408117a2009265030503054000c61400c0d01503100001c0c0314240e5031151089540310409036500d00260292040360008000000c0c01850042031240d100007500000c42c3c200354071036010924041310b075100c1c85001c6c100031f001c0142e80e43c1d0402088111582c0b505c0184082d003060a4524054820b6005d00303030401c5600d51080e410f03c40c042000849000e100c600420212103681001911003065002141c4242d0511840e108805040b8004545401449140d602241d00c1c6658990b02240744050803415400f44c50400c0001c40d040110b40d600c119 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 186271079 1250 186269829 186269879
    0x12110a0c080a0308061c030f0516200108010e06040b06040312030c0e0d080315011b030e100305010528260c0102010509030d050709030803160e09060d060f06 69
    0x42ca43c2c0760141400b800207051500801c03120110302c440d4140102c4c0f0f44817039500f40c200728868035a2a40100c0d62032040700c000e40c0712909005110b40422006812110724243c0346007201c503c6040c050011900c3c8502841501104100403000c24032628150344804c00341700004081915066807a547c06540c0c062010400300403036502c1051140458103c80c501e00442c0b4101c80d40d45504101d40d40d05002400003903c0c1e00c8200d50707645e5101e00540d0091500f01e944134503032040c6000404051030000c04c1c10700401c0560b402003104a02c41040079006c0e00070036051311802800c00c000c10010240390181c05180c08140c011090f1036003c0040c0f0b841540301e54013040050445c140309420b03c4808010701d80344000c6040d0b81160300d404104084101301000b6900c3e100c220b280045000d440706141215005101e400241c01400c0020610903241040982d02c080d466170750b11480002e883c000c080001c1c43c3e104680d41904000c81c00e000c0000525030b036102170f2440030001400a41c0a031604141050000d04114a410070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 186272329 1250 186271079 186271093
    0x30201020c070504060518100b03040b150901030c0e13080a021b0904030e130e010203010e090f0109110105070c0801090501021e040501050403151d071e0312110a0c08 73
    0x3220030701c1664043d00c020f480070b00a881c5850007041d041d00c40d081501c07900c03000f001c001c02c07501c40c40c200410005045180c405500e80c1403d04191082c42c10a0355002d840c0810401903038003a0900000c5c280c1265084a654140c55190403400046410010000300092101403084000156203c000d0100c0b85615402403403071880c0c8840000901503c0c1034943e00c07e00004003003200207940300c0301c40402c0507400d462a01c01041c00520340c1010740300204c0071110f1940040000f141c41d01450140780d11a0044100b11554008901d604600302e42c0d41c50700c080c02637003001d1001060b0f035028200a210482c8500c1c40201c8071075641400c14216994010100c94694001541e5901c02040c4624010081c80d94840185070515043c0060140d00c218800102903082c04100c11302d5034082540b000d840035480543c40804484202c0ca100d40700c06881c0aa00c2d21110500100d0a04260bc040e0640c15a90701050700c220001c0c088074141e6000300c1d01c1d00710041307a204e000400740000340c030031085000078041d40c8010508 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 186273579 1250 186272329 186272347
    0x61b0634020307020924040e0304090b060d02070609200a050f0a09050c030702010615080a0903050c0105041b0f1a090a031205030a050112050c010c0201021617010c0e0d110303041203020102 83
    0xa82c0c8041c4c4180f03200b1f5040041d060502c07240881128111002c0d1030000450045034000304090b8040c050084806070301c08181d038010701c1400e8103c507480d507100b14007180300401d240d014011040b0794115401c0e0400b031000310a0009040c881c40f807080800c0004c281c5040f50f607540d201582590401c48003202880004010b02c2500c58090045101824140d0103880548107151f400900500e40100703e0709a09485e1403130401450f0182d4100d0780ea460502000740168601400c040180218000d1403940b11002003a002881f00703502c00030030064807840302d50709200b05a0310038400c809800c141c50441d0f00c01e90300302001000400885189072551003c0d101c4544a141425a840440304140c0c0000c0c5440150009030001810101d080201c100007424000c11010007400100c2c5050100c880c5111030b02450720000c5041800280c456000c0225000240a03065445c0012140d1410603013545811101800550002a4049440341e921800c050112400c2954030108030809034000441600583d60024402e80 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 186274829 1250 186273579 186273631
    0x712020d0e0d0c1e060204030b13030e040506011704051212041e020d0f14060106120e1203060d03020c04050a09060c0e060a030b01020c061b06340203070209 69
    0x105489820300070500007050300c5101414035604940c0d041380e01101c00080c1040201c1d0b0503130340034640000c180d141c14071301400404501c05010f4420350126802d008240c80610f4540102c030b103d80c5040c0d6414101101000401b908008040c000725500d000d0780304a22017081ea003a016000218a01c000c20b0147d00300790400018494400c5070138060111061851405600e5a4007407181003641700001070f0460b901c0d4100754034802001c540640c014080c00c1c00010f034a590089000c030480340c091208000d542182070300c495039041068800601d0750018000202e161602c40c081b82000c500034016500c1da00c0c0c1d46000201101c00490314101566641c00210043c01100d110b44511004c01c5d0800c40301d07400814000880f14015038020b04105501d03405107001d180d1080c05442c4041c5406024545c80c1c408030765201070301820001d00c40307c151180000103114101c11541d40d882d80d26034034484401542d54846040a1940008020015032004200c5080141c03545a2154410203110207031000c203525400c0245 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 186276079 1250 186274829 186274843
    0x402090f0105150c0c0405010305070602010e01152c070816031e0b04090f0f0506070503070c0b0411060c060702061b12090705030706020c0a1505030f0712020d0e 71
    0x3850003142001400b0a8070f0742482c180710500c0d001a565140c08810000702e00c0d106214134140c3c1c000313041c4800001000000035040c0145c440c160002d109a982c000c84040c01c82c2c0c9400061101c41890b00001c0068041c0031040e107a41c20f0000d40203920402c900c3c4080f410764081910207200107099401000603d1b01103041c3d112043c21103180901081c0501800c281001c17014601d4124815502d032901040c40c0d07250383c00a5000c60b40b2045d81c1c00140300380c0c10030101115107990242c0c2d440c000d10700000c90003071207082202d00c00c45650b03d941c1503464207501c50400c180c100a0040703d42c070038040244801d96803910003405240740b41ca8014029442c03c0c3c80000d0a00c0d001418545091400201811800b030840003562800c00c040001507e081c3d64000002e0b10300303416139020b980c241c05000ca02003030b6a640810035080c030050030344d0b034100401d9980036101c0c241c031404040d00000031014400b02d0200c40312044119005155440c10240000000b408201243d20440b5010190b5581e003000d45c2140c14284491 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 186277329 1250 186276079 186276091
    0x612070f030303110307120b030f0f0a0b2503050411090a1b02120708030603151f05060307090603020a0c21030b06040e0103021309120906202a030a0605040209 70
    0x81c0d8154100303148003915003510110306211140d222355550500d61420080e01e0381d50709070901140c80d1000e907205e4154441c1e020f200240c1c0d0010740c51001500e46006070400c0c10850400c1c0182d55019020b05404030010140640100c800ba20400d50030300b4103a95811b08240035162508002402c40c00f4030307500c2c21300c116000340c079002035411408040701d6100300081922641a04614925a0307607403500002400c0500703d0b900040880744000a11199182d03c00b03000d103240444031722843e003132515841004458001140c0c402d002404605090004030720039006007001840c0750511216007892584d80c02c40504624044801130f1100c21110303400d156040c011468907020a503000d07450319040090129064105000180c05011071041e40c0d140391f400c50b0b021000042e049446107200ca00640801000d04942d032140340c0005000d803172490101300441d081140020342c404001c068402805008151041508030884103081042d21020400d4600703010020116110710700c00515441c081c0b041100d42007011b010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 186278579 1250 186277329 186277361
    0x10c051009030f26190f02340809040207141e0c010302040302030d030c05040306050f010501110d1e0909020409020a0206070207060503010e0c090d030c121d090612070f030303 77
    0x4500d0948000110b04c0390003e07010300b4aa40c402044000c5500541101042d2a11640c400611407640c682281102074440170301e1040011705002c031000000c81003038a8072016003140e400704084501850a680180300107441040480c0b01650607061141c100b440c2020130100080b00110214913405007800f01c4401003000b400e04500341070550700860380d00d2a8010001044c59a10b0038002c0c011801130040c0d338001c543c0080103001d1407502a80000e0521802c3c440e044c00300f51048600d11404c1c0001c80c4c41c01d00450140d54048600030b0610f90000c101c1803221046091040508000c190046240010409410b69810150760741c9100c00000345010401420b0500f15003110070280300c02c0d540001240d04503604282c1c4100c00380c440030011244d512800e14990b81c03000884204404050700b02c5003040201e809142c41d00e2020310302c000c041e640807000190b200810000800d10310400c0ca0461a10790300040302414002c0742c60700e080186460403000c0d400140340041c980314108105581406903002c00c0d49103042c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 186279829 1250 186278579 186278627
    0x301061d0412020705030f07090f09020904111c060209030d050a08010e0721290a0b07061820040204150f0c0501020f0405091b09010c051009030f 64
    0x203a40c168080161004201d07009030300d103840a181c400c018640280000030160707100705c403030060a242d5840f1a8841d81c528942012414400000c0c180300f2440d8507500a42000c03e030355501d58440c0d2144441c0c1c1d028a5000d500f80d40190403001007200550f042c94818080140e55500309004c040c40d21110000c140c081003c02c002c141b060b41c0c1e100c05c001e41142c60056a4000a0302d400c0b40541e1000c050b030301c84a140d81000702c4140308140301904103150300b0503882003800110b180814a254220280b0081a400c80746144c802c11400044200408116005800029a190068030522038044110500352400700c90105110800e0b14540501c46032404102c808514280c45e2a20407040d40785501120018080c4260544e4a0540180d841c0d5403600c2d8020003c40d6504004c18221a168100d4002c09000e581c0d0742c0300040701e11080c84022078101d00303040c039802e080224000c011600c8841d405011a03860250410180135004140241c0001500c00c2e200e02c4601d0000d110000d100c0b001d01300b1040c85040250f1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 186281079 1250 186279829 186279869
    0x80c06090d0b0a0608030d020d1d190303060e0a050601021c120506120a0804170109050709022206031d03090f1003021c1a0d030522120f02030106 64
    0x5400c010395030340e01488920756590f5080302c0300010440e030741c4500350a0100240c11680d42c5019801001540844402080004114040c0000704104403920480c0c550001e42c041d0b4555036840c2c21494a036200340b8000c40e0850300c640c211328410100b554100c2e079050302c03102841542c0d03806005040344007070740c8500f844082801a10040015141e0040c602800e940c540105070251500c82c02210740301c01c203000b00d840c8040303280f0386054950311920920070302160700e0781195032200c01030080020807a00140141401c60400380321400135880344a88480c03012556442c4407440c000c14840c5002400151000208000d01c00205403048681741c2c065180c940003040b1401c003540e1105a040312001c81134494010a19070810243c000340701c0c80341460044000b03d0b900150f00f410ba030704101c0c10510840a074111103490760052100e4488041401000b1030002c4c005480d803101441107103c1400d03d4098054101961810b0381d00f0007903a6a030703041c2c8004545c0c480c00c20560900f405100000d25103950040030b03868000c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 186282329 1250 186281079 186281089
    0x305070206030709050303070b1005030a0503040e0a0204050a09061d160c0305090d0c080c0103050405030a1409040501081501080303010b0702120304090510080f03030f1602070b0d06080c0609 84
    0x140203101d4036011000c40ea8562040180c038014081c00380480e5621407460410f840b005100322080071308850300b0304000c1902d050224040741e02c50f034031000860606003040c08040200c80010302c603520003a4240400500c0c0e580d0640140003d00c030380000091740c9414a10f0808110302c2e200b60b580c5044c0c1c90300c0c0a01440010a1801d0122003150f0300e08030307040000515084916108035400a90300000a5101d0750501c07005c50561001c80325010100c454501401c3c00550070381786c0494000e005030300188100e9a019006181209030003403401c503114a01154000018120746007078000c200c060740300c10708000c80324250b52010b074050800c1c84011402c41d803500034041e026100d2804001c1c01141c10031210560f0100800a9a024003006001800b142c0352040e86038544400600c00c6088600c01e41f20480804540131040728010704450301c07400b00e16a600410001d2109030f0038203000451190000c00582c3d01d14035005007121007450744000c500b446c40c00c0141450001c00400c96441789400700141211a0341d4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 186283579 1250 186282329 186282337
    0xc0703080709091d150408030106110a06090c0816180b041b020f0d0c1208060d060f0e070509010807050111030d090f15090f0303051807032105070305 66
    0x11500d010300c0580c0e03803034104403401c41c1c0940c080b0300d02c107052240b0705101d8004040c084d00c40c429008200d69074002c18030618201c0d07400030307140504150010001072200d54828400c0464a03980d034400c0700e41d5205290364600131120b0800d4151070407130300d0a4080c0302d4140140081e1500024540b4064941030a103118541660882c1065401060b0303240a43c07a501c0d01e441e0003d260354500d10b540b1440b0720030b5015000c1d40324841010b08201d1400b030410000e81c3c0310700508a12008c0d641100340d04514600340311040e500c07130f1800341c0358540c4501104039602c0000d58a0041010380980b003035000c66050144185240f9002085c0c00840c468a070200040c003a841e000070380502140d2007440c284401200c0031100703a0662141d00e6030f070800d80782420303030703079010b12680c4112521814412003046480400207c0404101c07030304c41800a1800240010580c0030900c40c0e0070490f04104840c80d00c040d803c10407090a032034414260701c1112000518034185030a02d200c1046520300ba080ba0521910780111aa402445881 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 186284829 1250 186283579 186283583
    0x4120e03060138030a05011a0405010318050604050c01020d02070b030a02090604150906080a02030708070309081303030e1906050f0c07230a0f05130914160303090902030c07 76
    0x40392449500c1c0b4500f5202d81a103460392100e1141840740840f0046800c0b90700841c0c0b04c1104600380f00000403018040001c0b1002408103145d0b260519003000011005081d51b00c52600002e005400b094002c1b0f0400c4c01080d00440c8100001c00030f2040c0440064200326004002e0f00c15908240002c0103504400c0c01140e0f8806880c1c040103a81d2510f1000281850084d0b40002a0500300d068441141c03540144c0508140d40654403819482c0c0e6600a161080e0700c412aa144006039414001c40c101d07500942265000c00c1c8035208060400e60a0201c101942656520a8002821402e61800982041c02100044100c3d022507444610304107900500386100310a00c40a0340382002411803031900341809040003406503010511046288102881c60110640101d0b520600200300c0c0003824681d80b44a280c00c071407002e820252411207060440008009195041e03800c0300480d256152002000c0c00460014000316241a0185045080042083e4400c0d04551544c600c100b050103000c0f940002541c003255 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 186286079 1250 186284829 186284849
    0x60f1608100905160306080109030c1b05100f080603010627060308030c0403050f0c10050c01090204050103051f0c080c0c0102090a03080a0e0306040c0504090c1a0304120e030601 78
    0x9114201e010215030107961110344110714101c144503440380b002c042e20785034001580d8240502a02c502c10b490803206c42e2070000300450f14044030b5400044504208044440e444001c001c6829035a201040796621700c03070366050000300d03440c10361410144c000c5885a0410f006400800540b41003030b641c0075000c240180760f445080c403003588843c6071410a81284000c2c6500214131a12424900c05080c1035030014042100c141c020241004c5c074108000900c0c15405078006d1400034501d80c010b0081e1803da00c10004c2038600e540346c171803481c096145c030300070240218440c0700201014804900c0445110780601d0001c80c3c4282042c0000b00f550703030701c00a03003a0000d400c410910303541c1e50001110b0b40240304070711403250005030030500081800300344009001c1d1020507441d402180703411b140400d41c541204440042000103072030014841801e080c1e1050000d18455940d00203a50340b1485110542c400003070703074134940d000c0010402042056821481081700070b00d0404280c00003d00b400217446050501580e0010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 186287329 1250 186286079 186286081
    0x905280333020a41070606080109031e120c020109050106030b0411030a0b01050405060d06050f070f020c1c0812011e09020a050306040f1503080711010905010c030c0512041403060f1608 81
    0x402c0882c2c100c0b145c81e64803240411229070354052150103810340c59001d03000701e82c01c41c44424100a0818600c1c0c103038251540c401c41c0140308119010300820300360307848201310b40da40c14150000840034480d00c006540a449a0360309071400d4500321481075809661a03010341c1090078514000b51500e000b032415560f0445c0c000c500c5503100782c086142d100412202510701d50030300040c4425600c00034005409544d4540d030b40100c02007000c0f0140d95818a0341c1003aa040b1644811121000d403540c48105810380c4a02880e91400e9000721001414260a0700005106200803051b410b003c0c540340c081200900c0031140940c2040e2819001034814000184007a00481c0c5072030a1507035010103a88621110344032150032408841d101e080403450703a08840411100d2a405c100d4003021503000b481c2400c112607050f0745043d50780f8156942210070310344080040341c10340300d001208214100c01d81c000d44050104540d00d2034540e40c490303040500e4030034041c00b80206183d40200380030312851080d0741c03068030302c0c1641855501 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 186288579 1250 186287329 186287447
    0x1503010918060606080403030c020c03190c1d07020c030a0b190b040f0c0e0a050d03110f1f1a0105041a0405030d0905280333020a 57
    0x6101c9400001401e540c903005010800c0e68000303881a000d00e00070303078080014881c2050240c1e42e902c400c49145a1642c04003144499400a50290b80b1503144103404012282e96a84000c04000606d007000090a5801c5400c10403010740c1040b04414005088005024014003521020100f0394064107143c2e540391400e0103da00c1d103145421001c0d2544020340304100d02d94000a0503070044c0040024070f40000d4141600650600c0d240d64000305a403001411412030340036a903000d55008095202c1e14041c0d02031807103003240c140e5061010895450540f5030080108030010240011260240d00510314141c00c50107001071030b41d0000698042e00d85440c1c8084030031015100b0000c40303015079889642e1520030301c0b400c1103030203034042d40c0582140c00940e803c0d62203c00421041c4504042501d0040c17070011210801c1011640b038080c00f0840c000d02e07000c54030303d24541c0c007030210742d10755032002c49182da54000840d4130400e580a4040c591403001a0440d981b18041e400c51201d42401c12003c1c9208900820303001d43d0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 186289829 1250 186288579 186288611
    0xe07080601021c03020319201303060c02071802030907060e03070306020d0e010b0603040f06021b1005090d020703051203101d0115030e1c021002130e0615030109 71
    0x1040f9540b03c003a4040389001c040050195008507900c0840e0b4411825603800007855029080482c60780b0303026136250806c820000d9455400c031320028034440c10000030000c0483d985128500c80e00051343d0290603040c1c14540149071581024011940799481001041480e04000c240c0c0000d4030010304d8070404501b06c2c2c400192a0502541019280d141300080540240d80709911002e80621074030000d0100000080402c10180400c580103824144105000000682e0a600404600c01c203506809a00f031403c810051821141641c840865681c0f0014032550306800c0002c0c41d0254001e02c010a940350541e5521912007640700c14002d5034820220203d0506041501444041e1040e144003106113100764240115a0000388035600010151050b200501d600c2070240d400c8885031030340288080d282442503101d074140c601d100380045014180d644841a08a80010b03e010403410140c0503070f480c06e0540340a1003600280007a031041001140b600680280c982c00d82e0704407991640001445241121000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 186291079 1250 186289829 186289843
    0xc0d030519020f0c0108010e130204180503030f0603011b110709090302070f1d1602150a020a08090601050904200a0306020421081902100e0a1b0e0708060102 69
    0x20500c14218980c20884580c000f49030700d8451068030440f000d0084140055501110a000e11441c54002030001100c0100c050866a1f401c0d2018200040c00d0411901a94000c429524102d829400001c18031049003c0f6100c0c60340c001900320002c001e01c1c1030500d0180c0c0c81c0407425030400c00f403044521086007010400d0100000821030035005000d405030528009440700d8181c061548481c0e41e01030003046020922003101b8900d100301c1e001611903201d040c040c0182190401c504411449190800c003400d031018605540a0000703080e002d80c807a03182d032030003034030507a0000d08c0c1460503880000100291355076892003075003141c0c220030245d4500414000304c8080518000080c0e4200c41024000003c0004a90040c0212201c0c041c500115038180720040444462581020b0501c06091144602802400400c941a5803842c012140e90b5445070500b9020b031100020345040399044240e400e814000002d103000200a000080c803400d40c0d00f0b0418566030f1020207024002080708030303000200d003a40200a81c0d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 186292329 1250 186291079 186291097
    0x20301090506160306081905030702031e1011030403030c170403021b061c0b04061a09030606060a1b0c12110a060215060d0303060f09020405010e060c0c0d0305 70
    0x28001a1018184070b540d9a106940100c0001d081d164200340c014402e110300310540d82c0d05009000c0307001c208074400407502e51503d41515140030812174840180e401b008040f540340f100784c45054034107509051813410800904009401c0c54140178045490300e0901048a134000d9142c2000600d00014000c22203040300180b4503103056001c8030003800305260b00000d081414048020100c04160941f0b41031000d113001d02043c8200030501d02d01c0c100d100c140d90f600050600305e0007800003d0303210307a200e41e900c0d040d04003040001100304000494041e64103052003003a6010700c0594105152254051000344000b4542c4050310808038003081c424100b2501079984001000b038a000c0155200c005d046c4120744100d4040054800d4020b04000100a0f0020580c80c0710000000344401c49969444140403120703005440807030401d9036030b03040440d0803120900d002029181c407540060b151401c100001d402c0c0310750384040303500c903035010f101c0e4804c517a40000e03600f03003131110035500da03049542c0f2807405585500480d844 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 186293579 1250 186292329 186292331
    0x903080c0c0a0c0e0906070e06071401021c060305061f2102090a0f151505090a0302040606050d0b06120a09031205161e05041203050c06010609030b1b190507020301 72
    0x1001503184840c1305a0341c02400da40d002e44041d40c49550007510050b900e81c0c1065040300b4103121020200d10710401e01400100440000b601e40200080c10796007890440c1c42404a0554501c1d09109005007000844e500901c6062210810b80e00c2e041c0da00701582c1a4400d20f8561a0311194025080c4602011180c01907809003400350f880c28880d41410241c00381c9440031402914012112542e0503604005000300d91114148051001e07514808844a5020309d40041e04010480400401a00c0700c0c442c140003030100ea23407a070751940c0d00700301c0003001e90f0810700308184136540a1115686031409825190b400818811000a8000c140e103415203c0741c404c1406c07186c0c082c0c644010032070700c01d01120020a00003101c2da500030707000700250a98256032091072494000941c0c1800b045c44902494541c516046e40281801d80c1003552810407685882800d070443e80c00141319400c01c01c1005088120203802054001c001e202c00e40c91184040040d008201048160040000481e1241400380085505040d00540 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 186294829 1250 186293579 186293603
    0x30e0a050f0d091406160f150204050909070501051b07151701080601060e01081f091e050c0d05040f0f060204090c0c0b04021c050f0a021207060e01080406020f1215040903080c0c0a 79
    0x458070002b50843c4c4165030055114400248110b040401c101c4140e64050319240d051a08000045094040501c0110300720b11071250042203001c954940c4420014259440030f020303400c041e20380d43e080b08040e030010f00b150b8880c2c401071040d1034200c800000341030400e01c0d02d45460340c0c50428200c8000003010a160700d11f000900041004401c68101c4884880707040002c0c0243c0140251410442ea0100c1e55805011010300098a22410301d030891b58000d80200705415840e03506440e5255040d211a104843c50b80c2e0000302002414018002c0c4208241c86040041004000b920340300b0700341c18010002840354010350300d40c0c1440826800c0d8071080b42e4000b8100c1c5c04603480a80740c43d81c0e809035030006901c0351300b04040740311481000081c643d043c5d401e9582e0b404c44056200e8010358074080050021904150240700d007105080c00100a4070b230440407403850b29851700b00001ca03003c01c0302d108001d4600550503c3c1d040e401098000000310b80000440f02c1c1d566a44001b00f40d06403e003ca085001000800604 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 186296079 1250 186294829 186294863
    0x602162705100302040e070b0706051b160c0b0403120f12020c0106090b150a032a080435030c040306090c0f050303120106030e0a050f0d091406160f 65
    0x8a0402d05a0784245c81c1044042e101d40030f615900c00b41031040b00240c6804100c4040090f405820031500007051841c040444540c80d240d4201c02d800561000b400b40020500510511840d40351100040448805c00f41c9810b0a68a490104e840000044000e0014294614059520891030b00c000700007252411501e0b91300340e465203406401c2c02d207c1c0301d08483c1441c1e0103007020301e0a00b840c0396051031503544007441c05001e848140d000d403610f4001c910341d1550074080c1300c0c108400c51400100e40b40c81e030f070380303a00c01842e080c945110f81a400709181d0448500d9503291005004400c1420038026554070b602c0d82c1c69644003010121a4425600b000b481141012409800c01007140d505200b070301c00200c40040300a456605050390b82c01042e800e88034548072513004120080c0a941f0002d03050540c581524001601034481e54503020000c00486100c0d0300c0044d00e007040c20790000c0e449026208550301803800b00413040006034039014078484403060045c4108442c0c200074104180480c6240d100800c1100c501d500 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 186297329 1250 186296079 186296101
    0xe0903041a1207080f060f130b031501230301020c070512070f0b0c06072a0503071203052e090221040305041802090f09090a0b13030f0f02150c0c010e01050603070602162705 76
    0x10701c40c1e84520b90de40d80c0003645901c1e06000352015901c0410041524503d014204105612207502090050186d604003140322101603464402070190780c50340960724032000641914044000301044204880d00038000c101354a05003000c041c103000c1c0308107400d151b5210700700682580f06070380d001070a078065005400d86280d05030700050300c1008028004600480711544d00d402250340e0700720100d20040030002c240564400703903000c0c051103002d0b0700301103403152030030700c0c1061007600c0c1501c05401007a40400c2c208850a01e821480c2d1000c00220310650819440c40d010032406036520f0041e07403040d00f60000003009000c0800103030214030703082020400d40d8144105001c0d0345082802003070300091a58400c043c1100e0045481c56201c0b201503008001c102d07800c200200038082d0140c9000c42c210800c002c5a59401001d00490080f00342d1100001818100703001011300c1c00c045648001305540000400d40c290501e040069401c580b2884045041c3d410b0001610100050602d01c1c1207801e0711740b00c02c0c455000c0e09 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 186298579 1250 186297329 186297359
    0x10c0c1b080f0109021f020604030305131a010306050c0c0c101701030c03020a050a150e0402190503010e13080703120b0a0605090a0e0903041a1207080f060f130b031501 74
    0x1b41c40f110701c6000e030388000a00940c248181c142c05031340148003083c0000c4c0310341c0c452544604c5418070004d0494003540c5071100590540c5d044412818030b400180300b84409407158039001440b004000d440c0266070b41040c3d4550a0454566210750924045079003160300803012190301c1404ac55480c01e1540e140d20302a00b01200d00d020a900070110404082402c1c1841c00c622420340305011203294202060041c00c890f003000c0e24500682264003800303a14280d54840c0454240fa40700354650680300d60401c210026807800040c86000106440ba61900c0440d12290440c3c03103880c3c0600d081d000101d406900000034060060106070051003001e00014155130003405000c0301032048a15400013640c0d02c91542e94184240c0d2002000e420820041041c21031078108d6038604041c49580904082e5800c02c43d44410030102d0710440415044410040741c00d5009003065842401142d00143d40210100811b040802039803001031403036610b640500b000e5034200b101c40300364407000c8000212036840b24903000150300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 186299829 1250 186298579 186298583
    0x3102318070e060f03011715090c011d0f130603050307080a0318030f0c0c0308030a15080109030914120607051305030105010e04081c0204031a010503010c0c1b080f0109 74
    0x880c01c020308800d10b0031104a91a10321600f961504690a0102030700203215410601b0b4403a1284280b515404030600e101d940c42181c40270094142c08011100140c400300c0003046034000c1c0c11617603202400a54843c10001d0a40390207481c2503541002070215003005180c2c1d608090b129210100c1c1900400c4600300080c4101c01c2199828001d440d6880806004040355100003008074400210910f2080c6c031070f4008810444c0514034602c4030b03d0340ca440e8000107900130358074031142c9520b4a81c00c2e1142e8443c0104070008004507402003018003425200200f442c0d416000305540d1503c0c489103125203036903200a9007a011a200c0070f40700c483c1403414001e40b071a44008010414a124104009210715040c0700d04c0303048610744001005150f0726a501d00101d540810016940c001c151403125084004c503101810240d031041603d42c9a4904015441508a40c1680300c1031081e0f050003081a8510f5100c0085c00505502000b0b03648100d00e0720b194404820b9003600044158070801d004010107490541103a20003034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 186301079 1250 186299829 186299837
    0xc07062408061b12062803061d1b01030b0127230306040b060604120506010e180318030708100b1008040201021b04060302060703080412050310231807 66
    0xf50b80e1907110201d0080304500b03026208490001030311400d00e400ca00e040d0400326280055807100b12504e5a007406129041614400d46c1d07555024a13006500001c00e80c080040401401c41000c4503c1000210b43c0c1d2036070a80c10541c41d000309101590089a44400014884a04807810340c100c038a41c4528400a00c250022003806008410909640d07250038204401c0140180c03000c2c0d40c4640342d0788074850b805004241c10060401c40082c0b06a910101c40340030b00e210f500030300059407401031348000601c0041c110040b88a51500311221100000040780c00c411090203041018556040000e400e15820345e00150b1113015500300c2e4440d40b01c1c0e5500c03911003180c0807101540c000c0720341e241c1140c541004850003800359010484042c035510706010079244803c4000c00100e00c842d02c90b80418401e4025040031008a02d032a0240420428070100340781040da07461410384e085140c031035440c034202070903482043c0207000701010000c86a401003605480541000d803803c099000c000400c0c5480100132101c510002d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 186302329 1250 186301079 186301111
    0x160c02010c0f30090605030408070516030b0a0212010303121b030209030f010c05090d0501020f160201030b09040b01270c02150906070c020f0f0409050717060c0706240806 75
    0x480c00311940f2640326203003a500c00ca581410514295807a40c0050070a8451440600024000590400c420007a40c00010000d8038002e2071032400300154540685074568103401401401021403001c0704c45811a40c2510301013140c10b07085103d00f4000c0400303c1c1e42ca5850b0508080c1101d030b03190150014094200b00360100c8586032034149190f030880c0c1c500c2180b0400035204110b560020320741b4103141aa0030380644001458008403c1d80007800398000b621048881c00007000790340540da01071007240c50078002580e83c4d010510301a510045000360502500034003084c01e070307060035100464400080040007003400401c07901d411684040d60354207060708140c5c07500c04c0c4100020803409000c20a507004014984410400195503401c100005802c81c81454002e02c1c0c50050b64850341c1e0341c0c0180300000d03008101a244241c141044120341c40d03c0348000582c0f5500100c00e2140010030034040f10300742600220b0000e00e11004071566034014807480358508900031401d50224510078041642d500501800210400c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 186303579 1250 186302329 186302393
    0x61b060103061505010809060c1c050708070311120c0c07030c080705041b1d0402070609060f0b0a03020105030c090102010e0f011a01031b1d1c021503160c02010c0f 72
    0x21041c01c481003006a0000303000308120480c00805420b5500328ac2c0004c140c82d40511101000300c4100302c0d421360004d40464184500f464261144c40c0e001d4560030b401c207252086044207100b6420300075018155a42c4001401400844280b21480c01385070300007060aa4650303180c00243e99111a400380900c501d18001046100c4082c40b03584000000d000d4a40402c0c0854541007030007641202c014140d000f0b40c00700150300000b0304a01c9402840d502c2040001581f84c01d440198003181c1e07c4540f202c1c0a011605801c0c4007507a00407007640ea000ca594040e01c0d543ea000c800040b80500020f4001c10450720901000d8400c112043d003010300c44000800704610210402c000450684416080810741004081c811042061040c549159800800350020755202d00342030100d081d09249100803d03216040680d9001149065002142600303102c070860f80c1903040c00b407020281d244650660030144042c6045503c1164094502c00c0c070415006601d035000c0c0a12418060305140d1801d00c02c2100307070540c07258600 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 186304829 1250 186303579 186303587
    0xa0306080c012c030717010c1403090312090703060207051b0f210708160f09051b071a04080403020f0a030302060c090a15050a12060311061b06010306150501 69
    0x302c0704001c21443c0c001005640710f2042284100104982601602c44003103030ba201825020b81501d241c00b0b00018400c00620380007800f001484444042c60101001482000e44000041d50400c440c1d907840ca0700a502c0b800c0c003803450814203610003006d050000c0f03000000e107c3c01003009140907400d030380358569405c90441048620028114100e43c41100752014100941078080742812040042c0d00b00c404042e11000b8441c64a0504074052405019140c001d1111941038500040201009407050055003003111f9602112440c0d140b007100c644501007078100c1400506004400c2140d1180c0b40a11542000c0c1814510341c0d019000c1039004010401600219052410001c01104e41582c06004103031142d0001c841264059900d0075806403141c0d4000c1520040918001d084400540f5090303581c3c003b41d14060000e00100b800c0c00c44507460b0110404c00f2030000325a02035146c2040312802e95819140c0e0707440600084c003501d501014440c101c004410414a0342c03080c41190210901411a1951600111 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 186306079 1250 186304829 186304847
    0x1090512130b070b0403080405030705071e0f050d030e0d150605120303040b0c0a0212160c0b13030b0c2106030c030a020307140d080a18050618010e150a0306080c01 72
    0xc0c101000d44e0001000300b441540d045ea00203100c0c90a60703240a0143e00c0305440c04545400540c0d4070b00c4149030b0000c1c03004401120000414013407890102203490900003503442c1d40c0c040e101505100c92a20b03012041ea950b179014410b80740d40681e11128034a0b4042540b8001c1c4840d0083d180180d2090b500c0d451054400419244113640c880c070641000c0d03a0301141714455030815403c65080d84982d102c840810f8907850042c1101d403052198222817001c0b903003022038180081d50f22101e2a072004007c2d4076a2100b40140400a803074101040c6a81c076201c1d40d5150119106c0c100c14006e8070290303000c0071f418030500a40d52300c0c00744208500300c0d020014004101034a038161441c0080d81544043c00c1008036500d040e4125425940c0101544620032a64880000543c047c00c40750300083d8114030440800442511500c01806040d5011170030700c410ba002c1c0c401a00011031901d4103100012244810941d0f88528041c007105081a440b511201195001303005002e860082d0003041c040c0009409883d44075003084 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 186307329 1250 186306079 186306083
    0x80106061e27080c040f09020102060a1a15070311070f05120717030307020f21090a0504110d06050603060901030f08210f060306010f060f0201090512130b07 69
    0x1000710007140741003992103401c1021258414264046059441c9140180c0c8030300a002da00e0141519800c00c00c100406ca0b42c000d107000580383e14044072070026076400584c065220001c2c20001480c0c0c030304400c401d07818551210107550b00c070000c5000d4950300364006000c0d01d4014481d4845042d200c242d0a40261582c40c14010800524000c000c1008140740107a1103070803004041c0107030344045807984003072a40340041c4144a000c41d8000400d0020300c0780d040003071581c008815000b5207040040c0700c0030000d50072104c003a038504603140400c240314140c0d141c0c152030000f041c00030400c004a10013200b04143d2600280c04111045251690000700c5003001c90840303110700001404905140e00b10b60720340d409420310400c16103544d8004d1090511000050000120000f00405850701f60714003440d148406400003040c0c5070280d0405d10040000d10f80304400784041d0b41c03ea04100c0300310303000700508034010315849030003914507c26600d4070f01c0000080c0004205a00700300c20007812007a01c4076681209485000b00c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 186308579 1250 186307329 186307367
    0x8040524030a0c030905011802151606020703020c1206071101150e040c0e0406050604050115020a12050c01090605071107060503060103200706060905060f09040f17030109050108010606 81
    0x804482d2154400c43d03c4580030b083c00038a8005584543d4211105031090340c080302c054400c91002d519256084a840003881c80c0d15521700540300d19034010302e400d00f00300184600c0d001f141417802c050091122140380000070300348401e4049258062641c4400c1502d00401203550302210f00c020740e0045c020740301c80d26410200400b03020300d040018401da54005005603800d042c61071000c10942401c0b96050f0080d07000e2100410a0300785181040104c50060744901508025040482500c0d83c010806071072481d00940006801b0108a50607a020310422a041480e940381c01040001c0143c164401c40c007806007075581c07202079090340f03a40756500c40081c0500004510240009017041d03110340c204649240c00c00c03c0071010303440320381084415074001080c1180e0058440700d09001c46032042c4900781c4d000320f04940c004404c01c1d0701c40c00b00700144800360015003a040002a40824400d254600b552403030b5102d07181640da0740c0d40e56250070081400303000b902810350170a000082c010303101d5041c084900c014426 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 186309829 1250 186308579 186308581
    0x602031b120a02030a1209110f040b0d0302070306051f0e09030f0a08040512030c0403060b06091c0309050105041d07110709020919080c0d050c0301090804052403 71
    0x4004001110300c1101850940315a9905880811005000c0c003480d21040d0001c60b01c2d24106800642041030346418107881d145000c000a02041d0ba134406004508000e4409e460700346000705c04200581100155079800101a04000c0201035000814004590090704100980d4032944918100708500121050010b00942402e1080310700e00c4113455000141c40080341c0c42c05003445615201c41d0030500390a0086100c3e20208424820144480da01380703101e140c4040d00d5443c001441000a005a0201404040e500c200c2804d45880d4017045400c140401401c1001840243ca03120000e001da0f040102c0001e010108006011350041d003d503015584061003c442c8091041d0a9a2000d00700422803000c120002c3c0d1805e20301c442c14040080a818a0b04000d0782c0d4255032014401030250380020200c1e03107420386004201070fa0020900d5040800b080701c1c0902c2400c01401c00500c0d002c100000b5a50652030315691008108041c00200100c5005560354030b0b40300c00d50440b0060344003000d0000101d0400800c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 186311079 1250 186309829 186309847
    0x22060509100c0c0303200604230a140a050714061e09090a0b040c0c02032e061503140f04020603090a0c0801020406140304050309010e0d0203060f10080106060203 71
    0x11a5009140c00d0b4074100e815442540c40e080102415640254041120004410942140300784203441c1e0303400c104010082d90800d65580000074451b040c502c40c204590700d0003000c0c401e0040c0040c440072500490700400d120201ca02c540d80781c101e8074401f00c40c130703118402d000120369601140005100c40001c01042c00d0150b40101e40303081c6c000d03007004059541800c00644005550780922036006016410000481c80c568005000888440e4080842406850301e407807001a903000424031202e8a0031540c0100040701c0c42161802041c0400c4180b184505280d4045982d41c82200c0c240030f00e081564040c0801c84103c82c03080c14240c000d86034480802c0f0510006005070600344000c54004e60810304070354140c5859100d198400d900382e04202c505035000102000050b901100c0359004c810355610b0f040c03550030550380e010350701c0c0f00b0010200d042c00884000c041c02c5940350f040241c802a00507007aa0b40e18074220100503002001180c80c40300d84028407002141230f190511a140540c1c0c03564000310b01d048601 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 186312329 1250 186311079 186311089
    0x30c090124210c020111070b011401260a0b0a150c020105090406060e0f03151f05040501030503070c170a110a0918050f010b01080705070201030608060c22060509 71
    0x4490501c0c02d000c1c40c41c490214003000701c07154071803a0000140000d44120346903030003825542c5618a601c0f1500c800c1c041035003c612030050781411601420b0703001650403048001030324280407a01140c00c0c0345480d40c2104503924800004a4030400207440104800640762080060401140c003484004804143d19002c017180581c00e0360054a0050501d103043c01d0348030b00020140c40b080d401400008520130b051f4485810907a0640096200c103c025003c0182040303008894102b00414909000c1c1d84824041c288807040e41e8010003030309000d00103108940e100e0800315940c0e0f00c006000c990540507500005044404c0c80c0e90601a052641d01500c84c4200350349581a8100300b81c1d070060b0340030044010000e8017111a00c44c0050300d602e4201040000d500d141006030030120160341051850341421100741349a0380c464201030744440c1a04010303403600c4c0c2da400103c1c000c11031508280b145220310000d001c4001071520151802d4014070000401c0d494150340c5020040683c0d100381d1010031360a200e03601507403901c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 186313579 1250 186312329 186312389
    0x903030c03020c1201090c15051e0904051005090603160b07060f090c0602240f0916090e0c01050903070504021c0c0302120a1803140c0a0809030c0901 66
    0x82c411140070b41e41d20710014002e00c2440003080705581d5a905da00c010001d00c200440014003001c0b000b1005029808809080e51107058055103580c0000394221540802c0c0c50151020050060700401c600c0c03618425000c158802405100d12503d60300c400103480f45400a51590355005500320001154a01900c0682c16000b1300d800700c45c100d8035580301c105203d02d58800d41d1111f500030ee040300300b2245480030181c01c1c01a40c1b01028460f20362074108030071384c000035500540c00a08600450303000780d5440904c1800e002070b0100c2501d003030481c0301000807544490703000f40d650b0000c510192a08000078400541d55803084002e003540603009480104110324003580500014450307610034540c80ea495032402c01c1100c105101c5400800e50100c1c40c8042c86c0822094990310022030502000210051417444c41c5a0f0010a402405c000110070114015001c050640d9400c0700c1c9003044894075890351400030080c1d00049102d070700901c01e0180315505440e1103550b081c101c852085402c2140c0d00200c10059001207 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 186314829 1250 186313579 186313583
    0x41703070e03030c0106030b01060504030803061302070602030a0618022701020109080c0d03140106050d050a0e0732090a0c050f0f0702030601050906010e04020c070e04050d030e06070903030c 84
    0xd00a207500341d0949082c0300508043c00f4140c0009450b80c03c524200d02c6964040e0404070410009010a200151201c0100e981120080302e803407001010f0a138942010380f0a1500080000e4008420700c6190b4042e44c110300142c480e1070362078401c0101c0e100d20400880c010442c256802d02c0d42c0701701103400101000c4081558a4061001185000321601c5020081c1d21144040355603a110b0840c502c0e007241d2520501c06a50322140b0025020351602c0401000d90007401b144584240d6150701062181880c0d41c403004020440f0700a480003150307034003014444440d210740f01c0c0b01d5119090450400030380300120600c40710790340185265003a1b1034506c0705900a00d408440301c028840c041210184441051010b01500180c5103d6aa515501e03481410704040c23040e4040ca0085101030b0034046070b41e81040c080214100c0c186e4005848c0c2e18415200c038a810729907841200d00981080c1800141315000c03c4514090400b1b49082c1700b4086002441565042d080350040b00086140d075050000078424458006254 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 186316079 1250 186314829 186314837
    0x1020105090a0f080d2f19030203060d0501060b0408010b03010c210f060e0103050c10020d0e0604031a07021902010c060e03090405010b040f082b110114071704170307 73
    0x3d40d0492180c0200c941c0c0b0138058414420180c50000f1048440001c031041c0c3e4003006c40203050a944010882c032044000c8031a8060607000300008406855070368800740a40e4015000340101640c8042820031603200b40a040215401e1010003456424140203102180035246c0d100c030030700580030652144165450b00410001900c40c0b890700c1d15045075000c1d0402400110500c100700c0d525602d0700c1440c00402d844924010492812082045e039004680707421081014180b41c4880009080094010700c0307035404c02009440800a15214280f903404218480c1101f81c0884d0740760200c0340e130f0514514440c00030003400210b0a9100c0c00005040f0f401000b500343c00c079400c49041c480520009000d54009810555462402040410111f6505500d6030002c15a601c0640940582d401204111b00100c00d4007003d01a411719114000740c1c441c00030440e0203d055070007006401e0f21880c1d009014007007611208000b0310400300d40510710410714400340c01103a00c171402e150104400070a00565410090080c8180 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 186317329 1250 186316079 186316087
    0x506010c0f050106170a0506010522180b01050d0b04020d020402120910150b07021c0210110c0f3312010e010e09030f0c0705280501020105090a0f08 65
    0x550151103582141e84510300108119040140e5154170049134000000c46074441000d02001c1140464940d06680d0169042514882d225400416040300c2c10200c00c1c00780e24240070008640e101c41180a0050720410fa1101c241c0d98402c00c0108101c81c41d000900141c1c0072001180040c601111401c1d400c6101400240c1840303031016910380b441008a465000d079400c441c0c484505041c485c45001300b80041e4111406202e403e02c00140c109005000d4002d0141d00f8500ea42c01d1100d241041c20210180e004100405070500340d41d0040c56400180c44e00c034618814990601940c0ca0100e41103100303035101034890320442c148081190303045945e02c02880d1011007041040c0f1a40703c18040189000304107441d07500c1088d45003c0308140c0c2d0000c168452038148203c1424800c0b0340d5004801c0350b02c842d2074100d50640301d10900c060f0300d0801701107500095200902a0f022508108805030081103808111004140c840e6a10010380c241d6908454002480d00520356020004001c3e004228401d80030346256820 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 186318579 1250 186317329 186317333
    0x40b030d12061a090906012c030307061e06120201050909040c0f081f0b060906130f060f0806031b060f040e07030e210307050a0203070c030321060305100506010c 71
    0x40d034010881c0d101c00003c0009240300c241c1c241034440b103400c0315082c60004890b100c0900d40210200300300d0840a03e0340c80323940410f04959000c2081d2802c03039400410420081c5940c80f0044020b0241e030080c200f409060003000148281507500441400360180c4490b86071102c2c1c801000041e06000380101c840d1a04050045080c1a00b85050f8001e449140b0041c42a0620581041c40d001101d840780c81c10503080044450a40d1103800540e520300a0613203607507803105c403403082c0703280c510302140c0029140500c80c889c005420781e4400303810352a07480035880c0c0c15410b0b00d6450a050b140c10b4110003034034074a007090040781a1070401c0c200410448050300c0311542000d80703d110f2444540d90640d0f000c0c2c0080d0310f41111795a518414004800b02d40100144141011101c03505400240401030101091103400310300301e84028003d01c1122112580520401d00e095140e14010300810f5444440d8100c4407c1b200c507c84410b4010302c104400c0d40d40140003481e041c110907103954081c1c100206400e041191141c00200 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 186319829 1250 186318579 186318599
    0x9051207031115010f05060301030804260d12050915070e1203030a060302090f010e04060f090212070602010c181401232701050904090804051302090f040b030d1206 72
    0x2903946000701c00031189500d000000c40d611122a002548200300c00c01c010000902d01000311005c37600300c440c4000d03062910302c1610a140000100441c45401092000754400e9480240c02010002c0010108895203504030025035481540064400031002213010030215030003a015031600c1c0400800341c1c9141c00001c450141141c0094403541c3c01c007625180c06108600d13040d034003190700016504208070158505902640308400103000903046a5039035a000c0c441d0101608440c050940103000d1142182c20041102d54900300d0b44184d8005500c0c20501c0c5a42d144520030f103105201c60307204280911401c00003910f0800c1079044202c0c2c10701032217162001a0220346691f075002c0003075000d5090340350005116450341211522840c4000d10080a444400320303a0810103484c0c3c41d0700e0030748001402c02c03481d1401000313078850703070308043c2c2d000d00d00d5000c2c0540d4103410b0b0010704c2c1c41841641d031840c160a01005020603100307070094050b45a00301a4071030b800d25204030300c0440d02d460103c00c0400c3c0941c2d030b0048a2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 186321079 1250 186319829 186319843
    0x1b0c01060e01030c1d04060b1302180f030607020705130b04050c04060807080f0a0903020a140a0318080303010e07181401030c090f3f050709090512070311 68
    0x2241d480d4100d40100103000c0c07040460350007000005540000d080c00c1504950002c58000c0004001541d10103d4034416100c0310f0f00a000004100403c650700e90407180407403000303441c911000f032046543e040c143e0f405082c00300d0b406010314075540003450000d082ca400c000b41034940b19001548640e440c4042109580c5a0040c140034882110240e680c443c24000300902c0107500070500010701182000b80030b1000911610b4542c0b1103011400000e5804d000d1a04909004009401901c0401c2d006244134900102040c420b01300c1d0720940f01c50f040e0b28040300032482001d0003032180d11696007040c401000f500009440740f40d031118942c42c0100300260603aa0b00404605c480e0030032008545081e00141da59601403080c00843d121900303002c414203103403050f260700c0c25605009006403061381d00900140120034030800b440403040200c070600007641201420144c2010504166550b105480001911116900c1032100e9545c010000d0b10100a1025039028039601c0070303000310100003800207480c00b01e6105001e0701d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 186322329 1250 186321079 186321089
    0x303070e1f0804260301181b0521010506030a200f03100504091101050d0207020603011706070807020a1e0501020703080a0c0e01050909060a080d02060a1103010e1b0c0106 75
    0x625003001d003000b42ca080360795504074404a400d0203400701e04c0b564420030b8a044a032200e50b6050380049040d055009400c1c400e16101c40402441004030781c164000001c1c002203602c03200181d803c034070402c3c0813000f80e0ac4207100c0c0a40003141040490810f0020360009200c8103001381103102076200ca10300e169807690001c05c0b0b81c801c0080100910030b04112103e9114001c1c90308039428002490140c0b681013996444031001810300000040c11200c14a00d90181e038100c0d900140308907101d40e902d0b291600284443c0c05845420300a0f140040c20540c004d0a485015a58a9004043d100d00d08d5850503c94080c0d0780a010b046030011003490001031090004001d10b45c481c0d40d8810050034521030b003006a901c60b25945050002200400c58183d80c082e00f507490440c401c07601c8480d25142c1c000410407800c0c40e500103008a00800c80c4005a0700d40008196014501c2d85030100840690030f840b0305800c0c0400e009079000a8018004030382900300466400d0180c20411400a2501c116070075502c1c00c6803800d601c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 186323579 1250 186322329 186322337
    0x31903030b0307090b030606041e06090207020310060b0d050c09150702040c0e180a0f0603050a1106030c0a120b031006081e28020d06020909180303070e1f 68
    0x100c1c85890400748081c100510100c001030105001c0080085d85502c030050040307010310764598100f41441031348040d074820444216400c101494a51102c1c1c3c0281d80082d5044c0d00074442c0700c02561202403140300b10011544801310090605101006043c0503003c0540003142004040c00f0760070782580ea041c680c00c045044892416511007151040c0400e8403032a546000500c005074402c0030458881000f10403d2005214101174981d40c0c0034040c41c01451102502905d5130304d0b1000200401c000010b01c480010300a0150940d44d900090800071a0710044966a51002d0144440c0125a000d105080c801500e07208001c25000c801a0100703142944140c0090620b50306c5100c200001c0d00f040c00b000d402d010281c1c800d522001b8422a0145c0e40784221b4000b440654110804041d00e102c448008401103a8000c107840c0495850342040c001030f412140c4051b20802d49040464481200c00222504600c03024020314110ba03903601051ba204244c180c030303054000001888010300385003107a6502180b0701d502d0316 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 186324829 1250 186323579 186323591
    0x10b130b0a0309061a03030a050703021e160f05030c0105090d0b040803150f0604171608070e0606090f09100b070c03050f070807120f080316180515070203190303 71
    0xb0b00318161041400424a11811000c0f5508141c40100c02c80d10882143c0c185140d52b841380349001c902c1e08800d0001452502c10f80141d00f00d000501282d065920049510311032a0542c0304c02003099040c0b1a0701c00c45500d0740c07000d0303410f2845500910240441c0b91000740342000d5903400d51591941c1d40b9003220700b102c040000100300305c0300d150200c151010852058550703d20901d0300102044036441075002d80401c007403806541d01c0d00d140d010040b00300b201e1402001d50701c44a6445001d10b9554100d030144c3e08085011000144503410107a06940c0745034401414444012962402c0c00b00583c000f400a540c0011090f0000c114103245c440180103107849400061002d40c61420321a060510740812000160450301c2d040098800000301c0c0b805403441c00c080b180301c651a074030b0202c0c000303211000c0060500001104225490703c10459550000c0700540750f00e40c0c3e03103140c150924942500c5000e00c981c170042040768040000415005032442600c0034084901000380030100039440c00141c00100c0009442d16 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 186326079 1250 186324829 186324833
    0x10c03050c0a2402120a020d11191d0108160909090c08190c06050a030b09010806090c010305010f060e040f02192312040615060f08010e010e010b130b0a0309 69
    0x18101e500c072510f80110441c202040c0c0c0411210b40341c4003070810056071f078021952049071401c0c0d40c002240300c002025240e5075144048420290091a6080303980410815801e001c040b108c82c41c650f06410078140e40b02c0203155500d02e010001045604140e40030440e0303041010507010540d00c243d80315140943c002c089402e1620004520f0140c003900f04680b0004250034200010703141d00d000c8800c4d51001d091003078580c0c003900b0044000300344540c0c116030300c0700115000003003034440803c2d064011070300e00702582d01c41c001031001034080d90390a1088414004c280d200030000148901046203d180c40100046000318840c2103203400d0760008142d1181d0310000309880e480654013b11200702c003a07007030815409a1075405003170070014080c00c1d069000c1c0c541403170000345c00c1282c0c0d41c0c803c003144881c0c00c03100d0320510b44600c0002d1202d400300c002c02d030104101000100e0107690341c91b001e50403500c4496a00903142e091004595031a00040c0c0b0340a50110703141d40209480c00088040d040c039408580c1c000642c0000c86c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 186327329 1250 186326079 186326123
    0x70e0319051b01171f030b01051314060d0309030506010b0a020f01180f020613090518030711010c0203120c160b1204060b031908030708100e06010c03050c0a 69
    0x81d8001c01d20403250700b001e40e14140d8001c2c000f20043c039100139503113555039581e060301060020303103010740c0e1460210083c1c0401000020010107060302c0007035415481d1003103150b4003e001c442040411060035100580001e43e80e10302000b82454191080c42c05d92044d655940c1c03003510f0305000f07800020f030040020800d03001d071540c1001010380300d06e6244002d120f03001000070460304410500201a204000005c1c0890954948a044a00b02e405400b800c180407583e4503c4800144815030710824025441641c0142e48000001552a8240c000b594241d4000d110f0005680c00714440c03d003240c040c0a440b04c6a49650400000340000ca41070b94007600c00c0c0a80040c3e441340408050b040340100d58414001d00c40149010714080d40e01950048000032030200034000a4501040700325401c41010300001e0300400c2249410185001d211a601c6121490304c9400d9040140c408500600e20b80380c162000085056104a00b400c0105000e401c005140140b20100c0303a041c80303029802551812000140340c002c4a40c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 186328579 1250 186327329 186327343
    0x409120206130c090507030e0a051006270504170a02060106080a05191d010207060617010c140a09030212060f150102070302011d0907080f01090203040f0308070e031905 74
    0x800d04907908855015501c02076030031542d0044600d50341d030b0b842c006580e4600923407100e20070300b03429001c5905d0300760b031751407e240d442030340b0311030507000604000c00000c25031071249000c40307400d0250b010342ca060814543d950008107130003081511840e0b64207400c1203940202400034550170711141e0181c07007950f06110000e4200107024158900b46840c00c01046a5800441c22041106620b01c00126480100b103051004211025048002c1548001404000c2210f20341c050005c0703030050180a400b402003004c0860896010210200c0443c03140822440c4451010001704440c006a0a207150b00d40d40b250042803413000b6100d5400386c1c3c0c3d484a01800118051240110b80c00594245d880e6060300480d40001e407164980d1100906100301c24194204080041c205900c48460290500b14207103401ca1000b4040c1d030b02a42c1e000052a03101e000441c1d20031f0a40222486207422803e006107071405540c084851a40041007074007000b108261100c1c0c523680500410f95099203412603030303441c602281406800c0c108 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 186329829 1250 186328579 186328591
    0x9061d01060c0f0f33110708040b030c0d0203040c0806090703020f0f03030408100605010f030e060606070f1703091509060a0207080c0105012606070c020603150409120206 75
    0x80e0b501c0010001249500c0c1404026440b516101e650825803501e075505000390310040000000354510f41091505201844c0114504108148155100b440ca00351041c42a00760140014900300700034004040e0140081d90450132400c212880c041249003050100c2e0401e680840e9030701d400c0003040001c0b0b003080240c10380014050015040c03641c03850707000465180144074500c0c090f0741c02084101c125a000e10965004100341004c0d140d01d14115440d00b001840240103142c049003203801010002031091142080e100c01d200300400241c0c07a00c03c100441a046000c00310341c01015520345900090081c0c1c0030b445003030180400c441d1241403443d4140e08002111031540e1114414108004a0160000d55290454a4a580140d8a90141c20040b02a124548000b200e960811000007504a58111445c90f01000341b80c420110903400c0c0c214645400e01900c44c1e0b00080e402400050141c03401400468000030b00b50b840c0d040503070164001c242501d2150f90306039a03080002c1c030030364542a018400307154821 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 186330935 1106 186329829 186329837
    0x1a1e0f03100b0a0e0705160809120c0a1502030412020402120c0a0f03050115030b03190c03020f030d080412230c0106090501050d02040504080409061d0106 68
    0x20002d50030040c000c0701c1d4440009842e02c0b041006900450f51640d405240402010304c400c0600c08480003658140c1c02048649241e0707654904044031a01c0c4c4c00040d2881c040010200136140f401c80e40701082e91210007071000e80555010040380d054940401c415141c2c6410740c00418000c0c0103070f0110984e2040035a06102510300355001a14180e031160ba2031840d40e030041030044003902c00a10400010000c00d0315106051402a08540841c000180480d5007400b843e551f03003812543c624006a07071794102e9100c24419428840241045c002003580181070b09244100010180c100080000d0300340411401d4001e1468410404440e05c485195600101e1014801d21240c0b5036120101c24451503190213030000b000f0070310740911412240d000f040090703011600c1d0240b02c00340c8401882121600010070000c12907590600c150b001808c00c10010501202d000490300802c83c106802c100300744 = true := by decide +kernel

theorem cover : BRFrame.Cov 186151079 186330935 := by
  have h0 := BRFrame.cov_init 186151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 186151079 ≤ n) (h2 : n < 186330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
