-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3959
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:10:19.744216+00:00
-- url     : https://prove2.me/submissions/cc044082-fe08-4888-a0cc-941116a9eef4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 711870503 ≤ n < 712050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 711871753 1250 711870503 711870521
    0x30e0c091b121f14030d0309030e1002061605041805071815030b040b0105041a07170d15051c021305070c02010e041407050a02031c1a03010b090703 65
    0x101404004044644840d1070009000741003030400c040482000d80f101d00b2501c00c982d006040d0160702c8050204055400107071800440c2a5814009503107045400c2c210340340368040342ea05802c5452090907144503640024014840c1d9007a07059041c0d00400502e00310340c00d20452150301c2c810f0248a1301d80c40110100e0b805150024114202940114105810488001107503440560303c24000c00b00c505509805005d1500c00d040101c03001c001411740b80b27002a010340207601822040041b4011281c0040d08503130111200c440d00240380340c079110b084860b10010796200025852400f82032030581000b402c0c4104140703054170402003135150804035075556990306120302035040c0d81c4640c004400f414450454400c26003e00680c0c3d48a600090b000d00007d086090f1650030765006500c0d083c41d4800c803204d1443d1a036080350003442c0c0956034002c5610100c0c40c601500c076210a0342e02d820000080c01c0211a4031107110780c41e000d14441e5200503148101400c82d4920024030760005650780001d918140300780e104400c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 711873003 1250 711871753 711871801
    0xc110d050601032901031217010f1205103605030f0d0914010204050f011701030807020d0c0603152405030c0d0203090d080c03092a0d0f03030e0c09 65
    0x2e21030388000f060401c0130300380d2054444d2010b82d140103802542c403880c1c100c0c048166030f00507005545041c0b141f400700300040c40742641c10308001751420100041448003007000840b4071001c2c41400c150b44080481000103908600500c0d90304569800203401080760801002c3d0014061800c20300d441c250104298080344401e1031469550109000003603e001c200d03c12114644001621241010140314030900300700396240c103000c624100746440c030724081d007203d041d29401000151a10329038804030f018410300e0719005189200f8200045901681035010b09a1a42c20052584d036040da07070070183d071003141c00e580c0d03a000340201c81081081303441c05007004541011180c1035840c5030400da11070130000c9810030307503214a00c1d0300004014a105a41711815a410030703204801c1c0b41c41c604010304940c1d81e82c407254402043d00e01e6515400c005803000350680300546503020b00140d461800a240c140780c0d540407000c0481c0440c0c604480043c680c0c07000038007000740540103072196520342c40d040319001d81d05024800e0420 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 711874253 1250 711873003 711873053
    0x42109030b09160b04180b030c0a090905010501090b011d030705030a08091201060b220b0a080f0906060d030e03030c011e060506090117250c110d05060103 68
    0x10020704001c1080c0c0c410203840c0041c0480b561000240b02800f50f90fa0f0103100c0400081c071090015140601c0641c024202e0840001800c1c0c20351000302e402d1608049900d40d000c0c1c500400012540c04c55003040300c206205500800c12070380c03510f48400880350061202707070016032201c004058a65400070a001250700c002c040b220a190b4030000240f80440e400012600c0c11000b24071048141000250a00c1c0d14140714000d12a19041000402c038074080d016041c0074514001080092010303070b1070f0034640500000204107030f817030031010809070040c0d0060396980007942090000904d074460105075a8003031000101104180141503d04a8041c00403404041d4103000c100302100d841c250074418400343e0842200e00c885014402c80551041300c0d034960005014600402ca0401a40c0e41b154264200401ca41d540b02d040751107044074442200342e01018040d410040b196031540441d004007007451803a21450701c01c2c013421545014040110030540c0010031a0340910014000221b198200001c84601c1262040c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 711875503 1250 711874253 711874259
    0xc080d091e143a0b0609040819110102070c03030224010902180406141c051c030e0106180b120a030e030f010c0909051f051302160b01050315042109 65
    0x103041d02508034000d00b80034601c10290703c00c00000f00041507001800302c0e0402207130b00c3c040c2c40e2040c0611400040029040d0303e0f411516449018010f9100000d803084021503c2c1e10503841c0c102d200c1da200e0300040e000b601c40e0305044802c29150805402c102c800d118401401c036480e10032948040d40142818001082641318074405940f03a41c82807100802c040d403101000890140706001c0c00c034868900d4004c0c0d01d00340211405c08200c3c005010049a08a00c107050541b05007030800301c00900c081500c1007001d50902000050f14000301e240070a4039848810204091580c040401081090840b0a82c4254201015100110340103802d504500b24002d0151601c80f014502c0040c02c483d180b40110b00800c00750307074084c400c1c0c1c0054440c066000800840c00c030f40e021900e038640d003800c540e9442002e120b402c031003414a5802c40c20360161841c203c540800f50051445600d40219804800d01660703000c0c1c86601c04102190380031070032050003260002021a82520742c0c40000c09583c2040803c1c1c418440400000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 711876753 1250 711875503 711875569
    0xc01020714010506040507110a170d140a0e01060608010b0f130e0118090f020f0109090608010911010f0c0611040302090708090106170d0c0c080d091e14 67
    0x1051440c5401d40000405150203005c10003202d03405001c2200700041d04090903041040010403c400907005034801c45c0c50300d0800a00c0e40c851145031180300d1428200342c00b80f9411b0924402841c02007103250000d02500041104185c202c40461007018001000300004204003c4043c0081000c3c0c2e0181c40401d14103002e032a00f04d4003251342a44035402c001d00d01c10040240405081d00f0f50341075140c11100b0700032042191980700c04c1c00d000741c10203407140d070080c0100f88003030b070099825400034940720b00b050010aa544211900903c0411015100c00f00c01c0e40030703600150722910000e949202ca94848030b10360f0780c80392600002004d003a4208481c0040411012025a503900c0c1c825204200a90b1070710031610b4455009820364000c0e5100070a0081402100c0c034035100007203140c401112031441c0400c44000c3d40d080070030322030b8100e500c0b01d031180c00340800059078180d004032204255282c07160f5425540750300c884007a000b0260b9200d1507009000406031200185440380c0290145001c4014603501001da030620 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 711878003 1250 711876753 711876773
    0x10c08060604030308181204060807030b060d02030601031d0c0111070b0301120501020c0304141c0309061b0210090501081b07030c030215070e0a140d020d1a0a09031b020f01050c010207 81
    0x8011789640022400304441c590100074151320bc07000e41340504c100700d401c60201c0d400d40101d145810120303401100042240e480307030740607662800d12544c4603c0d030034070340d04d014a4803502c48050a81c00602d400000305c1080100243d10400c840100581c2451070703103040900c9810300d1f4150070445183d5020080000c8000c2c4c01c0015202a2403c402c0742c43c4a80605c0d02000950f001810340b040509888814241c00f00e81c110042800311031690800b00c16030b283c100701c440c21701024003034002d5100006c1000f80c07020030f0344400c02e0b00590b0401c5c4c80e04111526000c3d020400b58003940103100400604100030340000e44200c1030640c0240c42170040392240d000310155800080e40881d82c0785e000990000d0710140300d1400c0103c401c02842c901040a42e80101c038000300314104002100139015111810000c0c1c108a4207405501e104907418810062900b00851032a01a000b243c10030380c001891042c01d844075507001413041c1c40a950050402103260520801901e42c0d81081c0c1541120355030030300854010641c8522 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 711879253 1250 711878003 711878023
    0x18030f03270c0102060f07031104030b06030f060417070206040b030a0903030f020c03040902031b0a020c0f0a0b0a1101110d14011a181f050705010c0806060403030818 73
    0x4119080c003001d0101d2180125000c526080041d8020049101166008140301d90452858812984240c4c0ca8860503070140150044c14181d81000060000a004424041034020070b812410788030030552078003103995079110949001c0c24371490f45d0040c3c2c00e868160001449403e1000e0700141c2080d583e2002e10000d6003084034010491611200c11004150b03051144400886001000b18209003241510325034a00450082045456000003c10650406200c004081000c003803c000c4d51034405401c025120f06000d88800d0013140e10003000702140c43c1030b40c00c0780188d48411032401d0900d143d843c022200c0c44440d1302030381699542c030019070700705404180041c90240d406032004071b100000503180c4525200d0503071140aa0380c070b103500f00058442050040b14a6910b014102c1082407042c0c00000302c0801c098040c0114120450501d000b1041e0040050320086000b4030003000340c80d4000506680f080f07005c07035206a201d4402c100910000740a201060f42007070300c485070701342d00c0c4601c288500c2c58003100d41 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 711880503 1250 711879253 711879271
    0xe0c0402031f0807150509030109081c050c071502160203190311030c0705060708120f0a0b10021c0c0c080109051018060b01021504150f05090618030f03 67
    0x24060050314000082010002d0802400134813034a0700c0c00503c1003806042c2e4141748100b2100040e02c480030b85d025003207203c0042e007040c48240d450509444408480340200aa04e2005040c1070000c1c1004046100795a0240d811140c019000c07040c0280e00c0b0025400a903221043ca903108565401580702008500030920324124131864651103424041d005084180020703a050b0300030040c8040360940407400100b1180300340c92243c0c0341c560324900582d41d4043c03170004840d0041300008024890303951085003401800d00d01010010303443e914044c00005100c200c030784d80250303000b190300f000520080155402181c40c18075111165400176a58031711459a160702000c820303910b410080c810b00c1028001c4000210008808021407144507031034800410411001401e800d69640400b20035074000e10610740f4012030340c030610049161629003040b440e4950707030203032080f185070000210304414503220b46030080c540e01c0b0041c100d951f2103440c640c4d00c010030f0942d090f289000a20528201031180740c0914082c81d480 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 711881753 1250 711880503 711880531
    0x2280302120109200301230d1707020f041401051909050c0d0501080d020a120318060f060b07030507080a1b030c061a0d120e060c01022205130e0c040203 67
    0x203080c24040c1d4130120641201041041004014a291076a141c110303040f4482c05078041d2a119000103058031034224000351070503072043c4950a1041c0044024030b0300320f1086410310030f000c01c16000d01041391008000365403001d18560062000b490240d0340e50f505960011410802251503d0786401540c40960b0001441c140124040403540c605016003405803490310010546c00000110095841d00e0000c40940410708402011036280d00c65089804110013400e112200c003840d510b8004020814a8552900c040c540140400e11600303043c116082d90341c065035981e050075aaa103507040380d64001a00348044c045136541082c81c44091548012045010391504407402601e400c080041e100d5050606100c02e00321643c3c0741981c1c0d01c4006074071496030880f4281114006150050750780107105210680d2016001c202c440e08514150028044802079542c6c001c8030001c906041d1000c803141b4040c8a40c0503c92101000b801c040e190701410b07058410300100c40f4041441404501241c1c01592141004115 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 711883003 1250 711881753 711881771
    0x2909060a030f14040c06050703020a0204091109090c0109142403100509040201080406091416180c050405010c08091816020604030509010e0a0b03090601050109060302280302120109 79
    0xe0b500c6149000c1e40c021111180c2440c0980d02c80b01411410302981082c0000896010b0905108000342400664042c00800140641e801c04000c40c40070082850b10420948001440310580071803481001001a1101e0392140e00302080c40f003480c0b107204202c070703000440e14040866000501c02c030342d1034094060f60281c2c1d803070408402501e554202500000d018501c0c8000b4007005076403104030b00d60302c160000c20029110311329242155085000f17424240e00c9120f0000700903c1286890700e00d07800c5810160b1207181104140c400e40007540c620a8240e004038800b13010811440d40117000d143d140d035220792001460001000c2c001000121005001c6ca03011800e1070801c800c02011180c0ca0028140e01d0000303040d2440c05540c010503e1141000040c10041441000192600e500801c40c000d0000c00960545914000d82c03120360b80c400901c10742c0d00143e625180001c0e00b501a100300e901810b0a0001c1c4004048801d0124140c0c0f42e1044043e001c01d5400c103c21030940304100c0c4514060142d4450104003200 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 711884253 1250 711883003 711883031
    0x2060f04090e0f0706020d030e0c030d1115010308040902030723070b010501020312040615050904080903150c0a030513080c0d02011508060a0e010e0703050607080106092909060a03 79
    0x109101c200640341c4c442c840a000d41070700010703a41d0102d001c914002c0360502451641c503080444803140d03d9010320507046844651504085500616200003089541e0100f213111002c045050a1001400d508820002886a02000d40041d0f40c007000c1400e014482c40502e0740c112240b00220303804050305c01d4001c03a51004020003080c031346005107001d1005604004403060000004a4050801080580d4075030000c010382c80f81d1046200100802004c0d180705140c607060a01c4154814403e843c468020044c03c40c0e203c07000b4426943c02101800c03020b43c02c045203110240c0c000d187c041d008c03145222020b582e003400103c0c00001480b5881e42c100180c06001d0307600d800642542c002e03c80030300d04500c07800000d1041481c00601981e000032a80400701c1e1080c1c01600782e90040034201c5180380b0700c0c060054040103001300095010f01401c1c80d6654100c01e40c0c5d0f100740880780040580100d40d00700c1008a1050200340c4103a00c03034089242400499864007401d14000b0f42e256102501d001e01081c3c8486c0f120703e4a403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 711885503 1250 711884253 711884263
    0x1207050109060504060807120b0301150f05060f0a080a0b131a03060618130f0f03080c030c0a08040c050a060e011e02030a05070c0e0c0d0b0d050d050702060f04090e 72
    0x201a9007002804c103414017101400c2088010030f044100b0280c4060b4868080703a54218161500015008100c00200c1c15445c0c14000414020042e200c0c00e0458000307001c0c03c086c0202c50000e00d1002e002c034205400d4000031170306ca00c0060580040c1644800004e0116518041070102c00e0b0b801c4907001414920540c1c3c104440c820982041d40b10f41c2000e0200201c42c2c503010006200f0b44e101c0422a04e06e555102c00140c200140d650029020110f10310304030742081080842602054000e0f04c0721102075071b900c1d070305039001e20040b01c14030704406c0d060100205103405125070640041c4030701e60380301c425a110b00100380402400d5209600150300c60071000855604605040064001c0080d050300b2040c6066000c1d680c2d1090070404010080001080014072090f180341901404072003643d201d96050420380500f00c1c1d04500c00b07100b0a64540016100340e46450041c40003841c1d80311000c1e003202a22000103031100d8008220507600100204001c1400d0055140104007501105000080b00146d50ba02c0714685 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 711886753 1250 711885503 711885509
    0x302070201271511030307270f030f05250609061803030e011b11090a0b090a051306060e0114060406230d05040b0a050603032802010b1207050109 64
    0x2d0015102c01800581818445020385039a030b881c1c0000042c03140380480c2c0d09440601c144c0c45074040841804500e035402248403004100c030402da60380980000c1d0807120011b032544589512840360b500200300003001000001111130140d1b0070707500130002e8108000003019040c0c017442e1b445440c03c1000d03c04241c0064039000980302e1440e142d040381030a016070407241c205501000d014058a040b100b00b0300c1e0b02c25500c3c00a065a003000b40c19a4801a180c10300c185084e805c2e00d24818802c54001407204041441503002092000f08a01c2c0103840d55410040144005410710901407440b0010202045550180400800340d06400e00aa0345c50030025030880d50205510500c034100c1044100f00503944040078031303048030100001b44848038038055101801e120b201c681107103003402c0004000c2440151983d0920400700220280003d558400802d0f49a214a540d1500e54403091024089820b10640c5002c00312900c60000042e550640f030002404c5461010007848a580803201c14841c95034440084002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 711888003 1250 711886753 711886787
    0x90210030b10030c0203070b0a0e030c010906050609040302100c0302130b0c070510121e0915060902130e0c1605030403030f0903030903140a170405040e071401120906020a0302070201 80
    0x13544039680c0f00945a200381c41c000743c031544042e000f250795400706a0001c40ca2100c010101c80c2d4030380144079071502900268006503892450f000010b0308074100782108a11030780d8182d01070071034000e6440c083c070001c0052001031010140e09006424104207003c0d1150003402080d09955100c54032500694034114041d0421401103400d03003896010b09030414041c5440300100030000c5014440540101503040780a20014051818001c11320180402d1004070701009842c940148041e40d1901d201006070f02c03e0146c020700b030360311043c003c0010513501c0300d015070007051480c0b58a150441c1118040c01551100c1e03804e5406400002d000c104043d040808190601c40508041070030340e00d140c07406801400c16120213001807580d04002601400248203040c50140e00c800940c10900140c1c104c4681174020b8000c81c1c0c0504e00d00b005000460000181c42000c1341e900000b41c00d2000c12100044030300740c104140c0a0b0b00282c903200c5010020340640094219a505958010f8444e83c150000500c0780b90240030b4050 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 711889253 1250 711888003 711888011
    0x51e070f0f030807020d05010b04050406021206011806031505030f0f150c0301060f02010e150105030f071a0c0a0b010303022d060103031103070506040c0e1b07060f090210030b1003 79
    0xf800c46040e160901c2e0116000552030703036907003002400b41c142045002d502c549010200070401c0850743c050810f07403082908800076a514140156840a0b10904d240c204e24048103040080500c2034100c1101000e043c00400c02c140d030707280701103440c01c00d07004104903464111800d03445246030108504041e8204022000354582050418180b1503c810b0080c070f02045900da0074540303868000d41201c12600d8483c0b04272020f1001d0100312242804080c01542d11034020350710b0007481084001400303001c4e103d8039103020300c00c081680362005242d805540c41000d64021100d148003c11035282100d40211b000382c020f0400d107440c00d01101c8010a4010b5032103034100324089514905c84c030000d00c0b40e055982c5420034100351800c0a080910314004c0c0c0200400e2440381c4000c0108110400200104958050000e90700c03a032110034030a54a03d81100c9d0020704600c003407101c50041202e6030003820141c10318800020746000960003150111410544060110b40c960b4000c0046003031001500c5654815468104 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 711890503 1250 711889253 711889259
    0xc120b090a0c140105160501060303021009020132070b06090109110313140307150f0621021f0c1101031e020906122e0e010501030207051e070f0f 64
    0x281c0c84140c1d00a21030303441c080d001c3d81910350340110b0440d200810340030505104000b0360303d480c80c040c2059000c110300502402c15420480c050501410103501e40c140c4a1f080342d4203012403100c07604e030707030006480403404070812a8481c3c005001c802440c00034003030b00341c4003002d00d0034900380851010181c0c403500f25180740000004655510500383e90704041d881440c1c8800b00b03028100031411790f01c080032038201c0340400140c8000701700709000c0c0c0d1701c5040112041400960221014581114a00c4c0703d900001411b000042500301d510403600303d5000d1008050001c0140c2803001c0350070011500101602140c01a1507010502049000d41ca00b128070910741072010401d040b20904070541c484468203007092700820320029650f280300903102e85e100c031640c03044503500d08454051000d26142054200c19001d07140964080d42502e102072045d0b0368003102c40c480c1641303071100440003948804415206405106d80c2c00c002c040d140f500d07980d100c5180344010803440d4140307601c0c1018802c0e554020020791412560030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 711891753 1250 711890503 711890513
    0x180405010e0d050d050a0b040c03060f1e05010507030210020d0c0e12210d15030b130c030803060d120f02010c020102160204020a090e0f2d0c0c07030c120b090a 70
    0xd8824101c4180003040a44840340a0409400d140c040c5030760140c00e089803501075032b074940c0c050740131989503440603050141d6031001622142e0795455600360100380d40000303100301d5001d074004013540b80c032a01c12a015558160171322412a000802d0440341d1380e0f161484042107a80c8004000c513201c40890315078044001da064699903891510240c0403450401015401c081c0e03101c0d0381a04c003081c0c046482400f040b4600003c100200703c980c0400ca50b0f1440c0b0001203030040740046050468070346d00801c9a40d841d42507807151140f6410086c1060380c8004000b8502000030120b1044600b911503030744400c1d1000711591303000390a5a008140040842e881404618440f641c4481c5620f4082d8042da00146d481e110204126940300541e089020030361800d4051050205481c0c42d018401d02841c02a016003560301034212500014140407000c0302c05502010500003c00b0400800698640000f01c030440da0303803692000c03103600d00d5512a100001e000204c00301408203249003035911407880d40c09002018625951 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 711893003 1250 711891753 711891757
    0x102060f0f07140c0d0f0c150504020a080f06150315060f010c0c150207060302070302061b0c0a060f06090504120311120411011101150e15180405010e0d05 68
    0x9001e60031050000c54040e900610807600120024020300b5a904900048195240002c1d6800b9000910305801000d40521444c1503115090780000001d001c81c1c458010b11001d4980644180c0c2e01a60030040000c1150f0100041103082c81e00d00045c0081d803400d10075040d604116807498034002c0d04040035144640b000d0204450b80a4012221001c03014681801265507011100c401096800c03a401e001c50040206000c208441046070700310740c0450b840b80310841c1680240307000140580d000a0114103405680350001c10307100d180145140c2400500744c2140d10b0010385060940c0c18a035110b45050254401d4020540542401042401241059900c4a5424158150f4034040654403840082c4111951048500e42e00c401b0320b05035803608082c1045050843c01d0f1000502140c2ca08400581c102c0040c0604048488a40d40005c8028603000700d0702088440282091840003800888044566990442c80150036080380558103614091400908468203081b904100f43d0040c680c24807a0b40e4403a00f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 711894253 1250 711893003 711893011
    0x1103100303121803020a05060115082a031f05040c050a0804080d050708061008060109060e01020f1002040807060207050609120f0d02011e0b0604032402040806060406050102060f 78
    0x2501d5503400b00e50070348400c001e100b030b8180a4038101d02e0000002c00d0540c00035207890424043c1c01506e04999a078030300d00e4440d415103a060b00104002c0310006039440404265500203100c040815410f0425010000a441d4011107400401016007040082d4100c0e02000c40c00180000380c0d01081400c5040c60b001d065401083c00303003020024250002401c1003203a1003651805603004200707002c2810034040c041c0c004001190309a00401d00746201e801c031a4072400019001c1c10068441005003404d094007101c4860300100c9040c1588200d0f91041d1019204028048217031601d05001078849061000300d50030500540e00500441d8400c4000b4802c40d40c0d840f0803521032007000c4860360050315158203c142000016a6480351500071442100825034040d0046040384060342d03d000c0640010391548800c54019000c0980c00030300034041840044c0c44442c14152003c941c0100705040ba90201c0218240d9025410003440358020800f40f040c20f041500a001c09411f00b4006031205d450000518484564010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 711895503 1250 711894253 711894257
    0x181a06030c071a04030801320603181f0b03030f1225030c091203020a081b070605070204062106091e08091804170a1808010903031103100303 62
    0x2c2840030003001c51030307480c1c078004540102446441c02d424054140e020034896824600c6100d00c0011313460b40a00d42c40c14400c50040501440c00c7c1c8060305000854000030300c5c034011200d850443d01201c0c40704101d41d0081c220703030032988610041100e203100c080d92804000213000394018403012002035520416603481e107492070b1440220b80d4481166603603400d10503400d48030b01d10803101d44440c102c1e07040e004103110495075220b0084107551a102c40e0f510800200f07004e401600700c00d28800014421000410081001006500d10708c81d0348071000341404020342c46040450030001e260021414a801414020103601084103002044c44146910700c40041c000140300f196180041800c205070100d1a43c45610410649a01e0b1455490b110011350301040a440c465403052a501d07140034070495a05219507030080c0c1c41c0071320103807070014031046802401d016800d02c081c014030705001c80a00c0f80b642c4001c0030003e001003000c0056050250444292400300c02a203a800c004003c0c0e801d03007000d00b0b01d04480d454 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 711896753 1250 711895503 711895507
    0xa06051012292419140c010b0f0a0b0a0c0f021206010603060603050c1603020708060c0417070803070213063c052b02091e13051e0a0507181a06030c 65
    0x255802c485c440c0e41c61440700009040450645d2200301c0540c804c1c4500030040d10a041c00001c41700800926030924401e800d07440ea4200014902e807441a041140702603ca29610b0003402015400201038044000071000903a01c0320700101300142c3c0c94010400248807504042200d4140406074180d580310f01440103400ca0b503880c0c4002c04140c42000840024440d00c0e090b01d00600b401100c0403915030043c420007402011350a4100c1400c80049230341e130102ca09090080d850903000798244040f60344044c1002d058a07035035880002c1d5104241c2c90040d10a50168002c00184100310741d0304509507255880a20707405541c003420700003500c9545890300440b0003801c00001c15420a44a040d524480410094200548400b4030914618120342e000c180e81d490114409143c5d03a6240c841c0e501d000283d0040c18590103922810507a0725030349510015a141c1c8000d98104405588075289000d0382c42e804004200c0a007036500303007020400d12400c0980c100d0311f000012030103041400142e480c0805842124041c81c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 711898003 1250 711896753 711896797
    0x705120601050304030c051204090f060f060305060a090f0203060103320c1e0406020d08042616030e0301060f03020a0e0703090213050106080a060510122924 69
    0x203420007280706da0340041164010411030319440b446420034882c007500e090610941142100c42e60103000150b800c01c001c001c032281c1c03420000310084e02c0301418440c0c010304601804240307041c45008070070306e140c2204405641c0e030900f840014119002c42c500d41c140640e074840ca01d256108a20348100071243c1411641c40e1710b80300e0040100c560700c144000d098504001c0001103007000b020001401c111000c0f502680c0015080c84010341e81840c2c1114000d044014034003503900c2240144070031340b2402004071803082c05c0004150001e0340e1008041c42c15800702c0d0b100c50761003015290900501019100c000c401d22180307451179020566441031406542c21015410001500c030318460343c40800b14680003040560411402040c20307008003000c0c00381500086040c00040e42c081300e81d024401c100d4201801c41701c00c01c1e120346000c860100c035240341c802c1d0290315903201c84000304a0808403119840810080d0908500100400014510090705405002143c0002c1700e03070100304a05407032805042c0c9034050000c2c12 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 711899253 1250 711898003 711898007
    0x304030305040312090c08060702030306011b030c0210110d210513050a08040f08120414180a0b0a120b130311010c0302040602061b0414121c08070512060105030403 72
    0xa500000d41e48524604040101444540380b496001c0f00e0701c1c0400d48e1890b80340c44d80226101e100480c0c00d28007154907041c000b000355540e010442c01c40c3d4028a00300000122560000e41010318604500000500a444200360050144506030b40784041d0300f0401c1d074030f60803000c1c216490403400748601c40d803a80d1100000d43c02e491a50131010007a5005040e81c90b44030403407505951a4100d809a140000140100410042400150015410386000320300d07090514143d41040d103a020340221682100a005018141c4907503241c055015090101006c680d140c607840600c500000369034001054200e8500c110f1010480d00d81c1c0c020381042e2800c08100360b00380c2500b1b0641b41000c550741d01d40d4140d840c00e110300451a50503400390003581c81c175030300380d0f000d903100e03119182d00c20001e0b0400000070300d00400c0100601c14a00c0107030f60480c203002d0101024002041c0c4168142240c2e07200e458a6201044c4c0800310055004030160382c407d9040c1040c90410f4443d5900108024004104074148440007000c02c09040c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 711900503 1250 711899253 711899267
    0x20a030b0906040308070216180f0501060e030c04050c0f030702151504050601050a080f06040f1b091226070203190312020c0319140a2307050303040303050403 70
    0x550044140d280a0421841141e6a90000c840580000b0500000b141e0102d01c0410544484c030491000d4211060070038140a9403021241c01018410342c2d9650815051803e9001d00d138020030040c0c40f00310b4410811001d25041c5a864540c41c0d1007a4503080800603030504a0040e90b070740c0d2085020503074581d038960400703a18111120300301c250f40c28450f504108002800030401200958186c60a1090f500e60200558950140f0042e0b00046484100018444840707042c417140d0108000300082000748001520004481c495944406403116050300410101e0b081031100000b40b40c1c28161005104103030b00d6040f5865103d580d06a1810328803407820350103088081c140c0f840150008d059031800480003407003025444280c03200718041000b071498003020100c4c50fc2914444580341000e1441c24008040c0b2015141c03e40740940140401010020481d2007824007030103105e9541d4440021003407a2110241c805800040d8103101d0040401c0f169000450210540e5001549030901040e03c0d1914a0190b4840c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 711901753 1250 711900503 711900509
    0xb010e03070e0603010b0409030c200d0302060f25110a0b0108031201090e070501031d0304062109080409090609080d0915051510090902300f060607020a 67
    0x507101d00200881c00382075000c090342c06250124000c014074407101c800e000131b1742c04084018020480752110107010900d0042418108120780c02074003070041c032000015003009542c401c198010b078060400c01400303203244404d85810a00040407903620300c04889007800c40c1007490001c2d004000e4040001341071480200306c10180141d02c242003480030b41e110001595280c200c10910306c05100d420000140182540c0b086040c444150301c01380c0030890405005401500410040c8180c406101120f0066901c00388054809441a41d42d12030445030301c80d041e0011024060030044265240a103d4400178800004840c212082e01c07102045880040c248030b8000c100d0b80303101802c8803c00003551600011203600154143e03200340030440c001c0b80003c080c90226182101e80ca082e032190360b120b1100c0d82c640242174494080e8103240c50244035403198018011381e0040b80c0e441030601314003c5a9100802d0900c040001440304102480e100e260040400000c4e20700074141a01440b00050400c0564488400c54006 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 711903003 1250 711901753 711901759
    0x160302120a030b030d0e090a020c07030f030c1202030408030a030c020a0c0f090f050906151507032001091104020912011821121e0e3d0b010e 62
    0x40c0c40034001e01501400412440d50f00c00d015070010900c096004051500307402d0005001505c0360351380d040805000354820940815603219205001000502d181c0c4900b21142c8603945201c031350517643c41c001250303c404401242c103540080c44213204041c8004255422103c4c2850040707201501007034107074100b410200c8050500003480902003a0b00030280840703c00c41d80f03009401c00038011030764a40c0301200d000385d444c00c100d0380114020504502d2a810340c0003101070f0017803001d0300c954510b51914800b50301c43e000c1240401c512410501c00c054140015484051b0848000d021440103544c80c9408030201012540c4070300c0e800302d00011b01c0d89801c0d4282442c0101c0b1002040b0b00c0c900300f03000086007110014215064151450f010303101d608642c00c62071510b800750b11a2646140082c03010400307441220b0450aa01401b90103078400f4401901890524441e1080038028070100c6544148054550314045483c0701e80328140c8030245480c0324000254481d089600040c441c1e628401215000960252143c0c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 711904253 1250 711903003 711903007
    0x80306060a091805010807060c05070506130e151e011b031b2109061e05070b0f040302100b101b080c240403090302011b0804120308090601050616030212 67
    0x5803d4003150702c90f6050b03400c14003c0310402503441000700c0326000f002c40010810741240004221504044000d800d2016045660700c0d009902c07054400403800e8200c0b0544801c0300c1203040c60f8a507041501a00310029441c02c0003043c89140c0304006080e40b007140060700c211507001c040910a00d881007002e191603020300000701001c80f0701d50814002120300882e071907400c030805682c461803c2c0e004426220031a0410345a0302442441040c01ca01c02801161180c0c052102c10007034900002c01410000e03118034849007845c0e04604146c240285802480c814169031103203003a80c403c900e60343e40c0b035500c01164803514229080704400740c40d00325409415203008040d01004941015900408581700c1c002d6a070659000203091900620200c5140c02510041c0105018150600241d441281c00621a080141d502c3c207101c0c0705640c4400e043d604c00e900441f400c1585800d00820142d00c02c61868022504100402076541800c3c0000c9007445022514560104401c80803404c040c004d0020200a00c00452616 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 711905503 1250 711904253 711904289
    0x10c0306050102070506031e10030204090c030b100e27060709051215070c110907030209040f060f060503070c050d022b021b04020702040207080c011404080306060a09 73
    0x5000382000e405514090300800002180b1400d140701a244504502c410700c801d503007043c0b400c0c15107685020344074040c0220100e4003c400768031203002d0680d0380ca100319201d168403455401e046003056005000785401e20940c0e88200030111800460503004030040030000d01e01c00c40148a03050079124219001824040d201c100101c85402406240403100e054816070b04414480404507125480503001d500c00c1c03c0404081404c540c451003003600d80d1480784271440e04220780b086c005420702c0000c032240c50010b60000350200f1301d0308103400f840c0c00c5807002050601405082180c0000300c0d0200d8041d65041200201c00140c2c0e0b103106080c2d039500a0f8100e001c0d29402809420001d4844041540004030048945041030003500185c613040f16110559002c0c014407a0181212000342d600c01015991041d020300203500984d50354070003000000c1c865680c02e079807401001e4042d829946003d09504a0344807020030031000c610f003401201d500078800c41301c1564515400d141039800e6503098111a240400440c195 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 711906753 1250 711905503 711905507
    0x9140a05090c0c06180706030908091206090c04020708030c0a0e1509180603150705040803040e01090c020c06250602030103060903090f050a09020c030c0f030d1104050a1214010c 78
    0x801500c0418004d503101c80d5505d6034010301030403080c0c0715160303d81d10804042240c684254401d0062511828080380b0f894004070000d030002101c06048900d0360440030a02c001c2610400c5a80780c01d4a080d0740550800c0f41589035420203000042484c0340e2450300181c0211014803034520040f4a00009086070b001500010000c001508040900ca010743c2101194500c03122680c803c045c444d100060080c21801011410b40500d1003015040c10300b803040501c0085903004090000c3e202034402248503401661506080794240c5407103411180135504020240b121540760030049035030101800c0b404401c10003880b0080950380d00c005202504203440072001004204c0950460402c0600964a07422200c1c5c03160228001c402c6c40e4440d85520404884c0c00300101016074015100380007180301070360705090044a80761300344260410400f80c25080080d040c444915940b20350b01301d418030703500303054203050421000c84c2d50702e4000d00600850b160310f644004104040d2030710030b55010240b100240720856031601c0c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 711908003 1250 711906753 711906757
    0x1e12060506120901150b190c080a02250b040e041b12031709030409090c2102010207060306080613050f07030b16020303150409141507080703020a09140a05090c 70
    0x20a440c503500717002a03a20b1241c2801ca801c0242c40704803c3d00d914040202d4110281c2c1c1404200c5081805205502500032031a0300c40642000001d031b4028144420390001c80b0760125280e0604041c8040541c1801e110204101c1705440944580607025a8583c459052241005510040034130400f528020007044c8100d070710145082c0c091282d00c40140103041151071042c129002c94256030640d0047c041000590303d15084150014000d000380ca1101c0d40b108140503a1403043d454680760b90421b01c002e00119641046803e000700003a203410070030070341400c80d8551200000f422804400f6040d07013181d01840b00501078903031904c0e000b4040314800c55592402440340760013280e20a1885403140c0400642900210031288a001ca9040c0e04d4642d5803844100300013013409110942d007060300c3e1410204c1d400300800607440fa0f0395404111410320300c3c00400c0100801d100800ca402058010710a0b00c218039081511001614140444440c0a40405003c215090325a03801260300a42220922000c4201c07200 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 711909253 1250 711908003 711908011
    0xc0219080705040606051216140d2a0c0201141b0a0507120c091a0a08030705010515030d14091005040305010615170c12090c0307061e1206050612 64
    0x400340101540c3e80b400b80c4c0d1b24061180220318078041000080c2c0c1601c880c8101112140040c205981e0304100b080e40440d198108210601066907a0f07002910001c59000a4100203c07030070f5280c14120b542070a00030f0411030b6204000341800104250300721a0002c800c1580ca891710824101400200900c0300759607074201455060300c89018030038011401150314840b005030385412200c201091460014a28001c2480543c4054908655001420603540d0444504024000e180c021038503501d8a00300306003183d04c090000846009103209441d05510045041c00480c0101c5c02d00c0300302c03010050184c0086220720399815921508051406909540240241007500d0044000300011500c0e84866000e90701a11030130300105089502000d4089540c001c0150320400000c501802c014034480507030714002c07041d520300070315422a600c03265080c1001c01200c8001d00c000d20340b04d03100c43c00d007a0846260746001050401000742c4a050001c040090b5000032008281c0a418150f550000c04174031400d20405072 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 711910503 1250 711909253 711909259
    0x15050405010c120e070b07020a15170a02030f04021903050f070609170a140307240f0618022104140709090201090e19090c171207030c0219080705 64
    0xca6003e0310100d0902c58007140100340030080054904003032094240b0341102c1400c981c031080506021070ba0a080501048013600079495205101b0080600c201340b04000070011011544140308104408420b440d401d03400503010b0380e480700824895501c3c10000d4015030005481840b845041684030100041c1030421a0425070b1034052442d1941d07944410035581020980c9150320021301ca03800b0a104030950400c1a80c1581220b1600d031300350f0f48480408011000c1c5d640510300e00d4492076039940a074000c488098401040400c25503007000f00c00c85481c032000141403d4203901266042402d5107103418680700710040000390503249428508000c2d4081402020000c1c2c2c0105200000d00010500030703142010b41c161a160031260800c0308611610600030320b140100c64a403881a6400051071040d9040503000d2021120124102032000380c1d5a10201c54030b00c0305030301070b404240c140c04074078083d100c1c184d5051410002e00c1016000045840c00c62400605c826099000009070b01e80d270000d803c0302214019 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 711911753 1250 711910503 711910517
    0xe0a09170406110a0c0302121501062120090301060b18031e0a020d170c0a0203061605030105090705040b0c0616050c060f0a020c010212060f1507080715050405010c 72
    0x7940c0f03142c59280c20280100703443c2d0004003d000600c0c1c060200c10100e01d00000300c8582c280000c4401c00f0106080c1d001c1700200d206001070340100603200034211007210b0054003d2124400f800070304007803001030214450814001054078500da503400c0d0442c8005050810320030381c80c0d0000c4891140340304100383e52144a485140364120502134030703035a10400806900042c0035019800d4082c030281c07251826049403d1145070210030589a07006016121009039000203014400603881894038040c000392040d40310014011000514991060441c0c1c1510030544c0d200740e003522050000c1e615800386800050034900041078074a02000002000c5200c3c24103140c50400e40306401c0b4003030b10248515941440d058104400061005004c040f002d5003004403460014540103080d59100c2c2280c0204007a000550301c10001c1c8909442c0082c040c04090b40111100c0d100e007003045090703442074441e80380c0084c030440011541400380595490441c0d03880f01d0140040c0003074a031515149000f40a20000c0354081924 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 711913003 1250 711911753 711911777
    0x160f120b13060e1501090e07200a0507061b020f0619080a230420060c0714030622030e040f020d0c18230607060b03061f0e0a09170406 59
    0x1900d00c1340c0001d001c107844400c945802d04c10f80225072840107010b8424001c41441e44000490344201503180d00d150341d0040c20300c3c4002413401900b0320110741e005a0801c0050040e40d003078031130141c101000e15a8100d8101040050490200700107014032006000e502c0c2000b180168102d401c440c14521400f03040303c0402c0842c100f10b96551141d042680c000806059400c000b9000510303480c148081c580070300214030700c10f041150008400c0d038450105100d040e0403122007000300d4038104515000c44081200a8156481e01d070004012500200c11803010340701000c07020400b4140950180f51000e200940b0510000708034510040c081d5200444280b61246000b444045091045102800300210855241100f0f0b140403c600e00c01d03d18042403d1505420b100d101c0c2d0380b940c0b118004d250051041c040861a510b00341d0802d07050801c001c050701e1f08103280c0312450040031480d29480d025103001d10034403005604ca040c001c0f00140902280248800b003a030300c841d500800e290020b081200c0f5107a60308869052 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 711914253 1250 711913003 711913021
    0x1506051b06151302120a02190206040809010521091e0d08180f0615040507080f071b022d121515030a120206160f120b13060e 55
    0x58110303000c81a999001a03411160719140c403098103000c0c42d403c80503050500450890100744000d030b50705609158001040d0000c0f0500345d00340310f0040b0b1240003800d20313450152a43c081034030078440020304011001032a0145400955882d10b02c111614003500458505040304507503034000005c024034000d04040210141c800c0000b610085100550f8408041d912a9000c41c520711200203070000703141c000c03402008d560003010441070340f0414000d5002d51038000c0000901007142d1009e40980108a071000c200504d48140074406174110709203207401110214010080c0118010041c0001d500414000b0f1000d04085250f1540c00d544040e10140e24007640c0c100100541046841d9441005400020101c00b40001d240303105035210f00c03202d8003400d500f09100002400d02c40420812191171715031038100402c0c150b0401a1903131107614a0300d00c2c0c05000601c5005807115241c800c02800b00b10309c0c1d4114940302482c036006480c2f0448080c0c040c0c9001d9004003ca4006840349028404c00c610078280008c070052 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 711915503 1250 711914253 711914263
    0x1080a05010f0c020c10140d060f090b03030a0f20150109201602040e0d0908150103022404061205060402070804210807060606170907120302011506051b 67
    0x80d403035001845045600c00a002a0540041080e1b00788103901001da0441d080c000000d100b9000c2c41440002c406041c1100400c4040682d00480ba1552901c0e440d00d105d51400421507001702405d0810349042406010200c0d2910018205a510b40c0310410100703071100c500280d18002e2038404014617200307a032110803e02c101c44604c040440010000054814074100702801001c9000c12280e0b12007094045402140c00c0d03848256404805502c00d52440c803155a01c88020340c0500707400c02c060300382c01612140c42580c07070030b042c00041e1140391a219003288480c0c40c115546405100e10506503103542ea10341c1d020300111249000d0304180d83c1404002415460301d44212031005a00074940e40c1440e0810f600b0001109c103452081600300f07080701e90306001ca035481d0045c2a00c07611070100450740c2410b14400910244d8040090071000b2804010b22500040c0400c91a090f0399054280c00351240c114181240907000449421210a129103c0030036666031000041018480725640803238003801c00f1411545d52 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 711916753 1250 711915503 711915521
    0x31f0b0909030a1101020903070b07020a0e010521030910020303010501020f0303010f03170f0409060914060a030b09010906092001110316020a0914150a0e0606030a1401080a05010f 79
    0x80c1e041008144100f5000c1c103d6984014000e000050400b80100c011074500201500017036800c0d100810f0190440c80c004401c040039050058000d0040d524280210f9601c00c1c103590325283c0c3c43c100d03000c2c401c40003408005440050070010f001540d81d6042c408081e489500078012240103004420007480c119900004480c1215001c01c0c3d1085181d180d511044140380c1c0582445c1c46000040217003280600c000c00107880504000f840000304107241030140350032a00010f50001c884400101040901d5844540346001ca1360001b54941c142e64a01120900424080100902172031404402c401805070112074822549651007000400305000390040d00d595030821032006595204200b0036850b00444852149414030182520034085e850f4100e60043e98002e26122003024080e10400203506000510414503c405560050809082543e5203082500c001e000c1806020000082640442150300002c1d010b212140c168a0f6541c41394071040e240c500c84042920070303600b002070381c482801c0c00344600c01c45 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 711918003 1250 711916753 711916771
    0xf0412030204180e1905070f0906081c09090603150f090b01061407060608030c0c190e060a03051606030e0622051e01060302040e010507090b07080702031f0b09 70
    0xc4400143d01034001e00040b4003031205038001c5c00082c02102c42d5500308441454816030290000904000d20f10514502c2035000f00c40b8141081c408108262021a203901c403d015948140001c2c0040c1009441001c0d96600140c0164a040b000105000e4007502e450600e0390307400780034002c112441c113504041d80d42820026040e000000c0c01000000e00407803203003520550711701c04241001c00ea40c80300012a0000d03070080d03000390400034110f032504d1424030079640c0c0d00e14202c41d04699040155030041c001040c60040b400446a000c01186071951604803c000465000084410030046048101c04030340f0103101d40800300c0c0c01c0000c0503ca0460110b041c038802c041c400141c8040001c00100d645e8050f03102d02e0161824003880100012101c001070540440180c8980003141e540c0c034500c1448200e8880d8019604581d15003028040c500303520500f000100c6010543c001d0300c0c0c00b00ca040204d6035116041e4003d516100340344c4c0741c04254503503000c070340c480c2050004200300c0072440c002407248040e421034071008 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 711919253 1250 711918003 711918029
    0x1e1302070b01172104030308100807090209210705030610030b0703050a0b03010f1a091e06060c1506090901020c0616030e06011206060605181014030f0412030204 71
    0x3100840b00f41007485080750722000c035081c0980b802c410120809400c80c00000c51900050144207158200003140c0e0800c00071490300c02070030300d464807103501c8001e5801761328207003500000d8029140c0c1c3c400c04101c1103000854400c508840703840c00001d59a502c14442d4034001c1c00b9000000d8084140d40c00c002d411070703030484041b003419500c500c0c040700140750040045026990300c00c02c6084a4509102d40640d0410514000030a0880c001001201524006055119588080401000d61b9420542e801c00320b54010700300720303113840d480f002450303d0080d61603007451071103128240c6080c80050400f240c062001560002100c6d04d4101a0030300303074072403514440c070710b07a01407408164032102880000c90040124039000440c0401d400000341003000a9004d80140c035088545441800308038030894000b0510b50038070301c1c58002480f803000a142e1314403101c07a00c5900c03407402c3c8024990154091b440d24541c0401c056a40e0714143c0307480d00c0d2a4006072020f8400010038030420308094000e1084406449102c08021 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 711920503 1250 711919253 711919259
    0xe01180606081b0703091d040309080f03070f0c1503060905060d030f0e0604050d050c040b010806090708091f0c030b030303060607060504170c1b03071805090c1e1302070b01 76
    0x4510f81e80198011010400301c0540000c084503e0103810044108240010b400d50410b810700801e080e0701508482c501307030402c0304040d0303010500000311005254880368a00986010f400e20203c0d101003a4807a000103560180c40000461303150b0b02503015500d208404102c1512511305008036803099210060102d04c840090711010385c083c0010302240785000b0162403605032254003040d4141c0c1c9854080721280d20042e07001c40c0c0c2c0e04c0d00b400340e08582c080a1a100f140340c03a101000500001c00a42110148501c60012130000f003000d1011000e40700320081e20f0003060345408598001040c8007114100080c0c9480d80121142c07502104903400f03803000401c2d140c205007a54a4010050501800480701c0c1c4056418082c001a176483c00b800b0380403030034070207402400441f004220b0640c400e140307294840d8005c1c03101400950a1701440492200300c1c201c00003200e50720403501034641201c01400c0d6501200e810800400342d00110641c00d5180801d5403882c0d0501410301c0c5800580c01003801c02020305100310014 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 711921753 1250 711920503 711920551
    0x213090b090604140309012c040c0c260f0a1e091409150111010204080a08040501080108011b0e03010e012d020c030702100c15140915040201030c090e0118060608 71
    0x308e00c0300c039050000c0c1c206401346000201140c100803040000300381501040c03818010700c1070311a05a007002501c140100c02181401024522401c042d1012400010030112881ca03c20f40b0003c42c1c111800002603181381c8110005003090740144030700e070765007201c05049694600f0807400f00d83c0030b20340ca40c4542ca60a110b4100540707100d1064250200f2644d40dd1100081035030b0100141003000d402480f1040e551418440010720f0042c058012a04580c101060040c1c07200394800544040441c611b00781c0007106c8000d0001340903080d00c41c1913901039820704e1030f641030075060601400c0004244222007903205554801c11801d902a1200711380198005025000148c2801011368a42550b107180c502010150342d622050308408402454074010750b10303201240300c03110910311160000806402401084824503440d02c000340f000b0002410561075803444404980121905000340c034240c610400c103981c6880309103401041c50018004110f0034403000117010fa010310445400703401281d100500600001ca0f013 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 711923003 1250 711921753 711921797
    0x807050f0616121206090b01030c020706080402060708070209071d12070308031e010905040c0504180f060b030d0e0a090e0703080a09090204031202070e0c070213090b09060414030901 80
    0x3400e0520044c48540e41e0701000b288a100060904580001400364100000500710f44c50b40021005651010304284121a000200282e1041d4110350b500c0d03a420742864006414000c008000b50401c2c581d80c00e1161003500a0320010400c0400b2440c0d07101200041c00300a01004000300300c0645400c00c28041c00072401120045a0059860700500000d841040d81c00c54082401d07400070f0040c0f555402400104012070b4040d400610702128184036811946051050fa5034134a20020001d800305525507040040ba5001540340c900000c09850301003040440103040207184416140c80b4600000000c85c034100c0601c200d246c50303160380d4010020103003180e4540e0600d5005c030307030004d062003415000080c1200f100e000410180d44103400d091004010500f000c0c0c58440345803c0394a0715410501042035040318503055840603501195140e041006110303d00006200c01d10000e0441d03000301c002c005c004a0002000c50185218031461040e40e010004c815441e801145101070001e10500b0380c200c039200c17010394 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 711924253 1250 711923003 711923033
    0x21011160206070f1a07020601150806030f03040f061205040f0213020c0601030f0b0709060f050a1e08420102010e0f1014010f0302010c05160807050f0616 68
    0x210b410728151280e101c1420301181108200c45602c3c00d40103400c8121300c240b20280d00461070b800101215410180044e0541707400d10070510401c241072000503050341e410881c412511a161007501e0381da540f10746040361040b580d03001c0c0c030001ca00d6511049509008920a40d4030558010b0305401c1e81d00c01c903071308011071119907400112500382c080c4600a180f001c2401540d0080d072203202d070b40c08010310500c1c00a0140703000500a005100405104102c850b4000790a01504280c2d454103940d90029040103540b860184c09240c1001c150303041181c3c58441c0c00561140c000da010030300303d6001800c5612080d21184084c3c405602c0402d00c0010041e4860241c40201c2401c0f50500021905142c48030340036151202c42c0c40620703540e51104100d074002000300e10500c2050300350150f501181c0c4d818250551004185440b0082c10016820f0340d400510030184800b2510342a10509050740941d42d806080e0750303000a00820307100706100100101e203494228110b80254007180800c020b41030960311130303a03c010b00d050b03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 711925503 1250 711924253 711924259
    0xf0608121204020a150c120503040302062208040b0405400b0915010912080f030702121303060b06040e040204330306060509010501120c140a08070210111602 69
    0x120300490350040d002038117640c50040755035004408001d81400b41045c0c07180c041d41805e03c2001c005001c00f0940c0403a04550088040c0c84000310046480079402e0360040005000d46a11408030700492400744160050040750030071500140c0e03114403c10f22150301c3e440c0300d000c00008804205c808100001d40d100326000d105017130380005031050b02d03640840d10100003160a506080e0001508031065a044000400a4100303002441c0e0090302a503034544c010f1103401c40008900c54080300180005200304190455201104002c58580441a842080f016901d020032034485050401140c16402d000081e41c00300e6101a010f0105030700d5036000e010080903903801c01c8010341d9541600f078a00100010b2202040c0070b08030715000d40c0750b02d507040c040100da8551308428451003a0100400c9a47e038400201c0032342d8480303070300005000040344006840340c01d4102e81b02032060002041d61100f25130040040e80c030451454080e1581c8901c4204c010b0126030114a08687e510700500206211015120342501241d20103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 711926753 1250 711925503 711925519
    0xd24060912150f05190203090a0f08041502070801140c04030f05070e0709140303090102151806070305070215070228080f091c02130506130606030f060812120402 71
    0x24054410b50b40c3c40495014981d45a0050000c4d12202c5510211080520b800071815070929403500754a503400f400016040c1004101040c0a12010000301d4008085d14501801f402c841524003030346418140c800d1440301d500c2e0440001e003030380b0103400da980300310b0050803104d02d8542140d803000d018203080042a0380c58460900e0104441c2c1c03400039801d001e225251560103000385002c070180340b0703011503a0541e8000d41080c0b001e421b00782d80000d8051142443c0e8084508255104030807084101d21120b0381119a208030024044a9038041d80100d0040103103a00b5103031442044107155204000580300b030070040c0d02034000a440204001c0c174291060b4014000b01c0342d48141619000059040002d04c0c40625400240e4544580762940311040146d200200407203440c0026000a61040942160080f108e034540000074050354a02000444010505038200105510f4000080c01080ea0030b456540082c9400c80120b0400ca00040300c03c0c0d0115941a190f107040b0841650040540303001e00200d0300f003144 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 711928003 1250 711926753 711926783
    0x9031712090f0c030312011202151612080f0c0c19060b010320040e040f020d0308060a050d260c0a050f07050d0b15010e060d24060912 59
    0x300c1815005103070080040c000311003100550b40c180328605079000d10952080146180360300c1d40782d846504551401321100314204050001c10041c00c201580c101c0d040100103409120b907840d0710700d50020540505074000e14550301f040c060310344e40400d50340c800590b41c45400155102e205c0d003000707000c07202d5810181c94030101c00c0d0300241840b02c2a000700325000c03612034414403080e5a05120328048034100c45002404048000cdc00244241b056014100da203040c98800a07081c00398440d000c0d00714680c080c10020001941d410003c2c030303014065071b6451027900008000900c07031400e10003241c18a9000309008000f055442e04615044001981a999026060080c203240c04014419107180074018002f42c8468074464001d5070514100360081c502c590701c04076128011030300b41c0880d1548600d03001c0111500f5400352005845800865840580c08040010425401232140e04942444c6c40300580c9186481c120380310004007202d040c02503070300280c100c400802c681c91a060364603081c5805141d200c04407101d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 711929253 1250 711928003 711928027
    0x302061206031903120c080709060c02011428020f1207140303040c090b010203030c0a030e010920010809010b0916120912080901330e0124020a03090317 67
    0x80000d042c1c0210300105e80030340044205010740c5000c40f500d482d00b410b00d480d10600207400750109005803410002c51161000440e4052180c04042490140f85251500c4d03100c0a404e0054001e50312102a10b03130300d050039030000390000480c031126912030340107011003c1c25240b080300241c02c98101907494916000c1c1c02d6a9080c001c1c40190300850089101c07940c80360524000c030b426140000c50f0141151b004204008102c4070400c00ea41300070324140b0300410104803401500d4098611050080d252400300d5455810060b00c00c9011001e000c02a250b41c0019034480c0401422030301200f0405410043d00c0300080c84403609100c0301d030320308059402c21401a01c00a180f1801700c501c1d048044500d00ca0580403202c20b13541000405a014116400070b00103550b58103020a00120030b0341a140c0c8800c1401404508000304030140030107020301032585800c560751405c6084800603507022889000440410701001c191010a800c01c40b250580c407248080f80c5113644c0c0c01c0c44130310405201c4000960070f100130070f4514 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 711930503 1250 711929253 711929293
    0x6070c06080709121e03020c0a06030c02280f1e0609231209060d0f090c0b1801120e10051009060e0f04020d020310021e04030206120603 60
    0x4800e0340d8400d007910b003080c4090818009600444004290380c4034040016516100f60028042240440d00000800e4030701a864a403801030b40c1c95101c280764101003117090340755200164900055003111084404c0341c101c0c100e0b07858148400c6003904529050302010504120200710482c0c8500c070301c00301d10f0381400c034501e880c0300c8520422a0b9103515034a28009100b00710b030a402441400307907404c002118000c0c079040d98840300d40d00080b003006008104400c4960b103c01c20341d80f0f02c409402061125060ac20200300044c65024000ca51600098401090911059098410f900c00040428401003144401503e544960200080d0720030340741d60307512803414401d01141c0840b07a00a0004500b82c2000461b00b0250800c40d0048000180f50442c1001208008444940c12040f46c1c032040041d41ca9900124840114810000c0d40501c0384400340020701d44245d004103034000080a00320a21402039010607058842c5102c0698011400d004101200490000044c0c000704010215a051806e00308101080 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 711931753 1250 711930503 711930509
    0x901171c1101050c0f0306010e0a050d0302061b0c03040b1303061a0102070501081608040f0803070914010e010806060318010f020406030b0a050a060f11010f0204090b030f0d030b06070c 81
    0x10769520303034554200009020300c81e000590b5030311050800000e581c0103841804002c00403410040005101d08041d250524003001901d00640410705c0c0400c0b0f820080e590310010b4842e0b0f1613280d00046c100b10002011006e8410911342040654602894a040c42400b90000078a0b20342c5240d60080c0000000d0291040c0031714010f01032030860b00d0440c040000f81c1000502c0e40034a040c8002001001001c11a610759102d50303480c1c6041c940c0f45501c4a04240c0700b5400c0c07001004002c110000140280d03160040880b008955154680c2850300749810011200130202007641f07808181c030140400c83d94a0b200000e50b9200c0e904420341c070314880005c181e007820b552285294110b0035900003001c0c0030455060098024420040c1d418801e554a4100440d03001015842104100100d80b103600240c03e01c203008100e10050044e000b84001119100c4e200000d500920884405030f10340310101c0300d14140400e00c28000300c1040041c1081403c166000c2d4042c080484a8680c00001000510009403050f00d401c806 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 711933003 1250 711931753 711931757
    0x4030302090303032401030606090510020c130608070812040b0c2415182d010e0121031413030503030f04020a0e190f06080a0f120e0901171c 62
    0x1e041011040043d0300d03c3c5c07241d10704041c20040140302c0580c114050804445007656910040b10000c01c00b28103100380c507036106a000c06c40002240c06c1301c049401803015280c1c04402c3e240c0a0766189800c55803200c8005074114003800c2400304124407650758014102c49a000f60950f130041c03280d1448400c50b46099040544034040b500148018401c81545080030550140c0f5003001004042c1103684080c00002c011403000003c0f6401c4440e00a09034069401d000a20243c0c00c440b541c45500700d03c0045000d00609501c00d0038841c4848505000c03425541c0e8076501515504000f1140c943d4080c440d034003581410f05003013240c9500000042080004511607440c103c1c000d5100e0038a4030400480074030f1030748014442c2602d8014886001000c00c9041803d401e40c20f00001c1168050b540000034103240c0d4410107580c014008a0350511241c0591b01451503c0b85213902e00700b10f604101030716120160b00340d45411100213001800381240e241f5644000d1401c0e1000c84080380034a030f84600c1c01c41c4051410302c0c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 711934253 1250 711933003 711933031
    0x11031504030212181009151805040f020708130518060f090c09120105010503010509010c080f1e010801020a0305071b02010c0507150519030c0806130f11070203071d0403080403030209030303 83
    0x2000b180361f41710b0b060611046141a80c12900c50440881804030359004c3c4e41e105660780c0383c04203007804c082d034110703101c61740e10845443c1c440085120300801e40400b441001d01134020602d00030341440c20348114500c05d00e8010038817081016540300307102d40103500410b410b0404204000200c40c80c0c0c1c464401083c8442c0c10000402e4941c180000d050a40710007501c08110381c0c0c14004c0d46120a500001c24550143c0f001014050580c0c503404100c0024112692031003590050707100101c0c2010041d0010b10783d00003103031002e0050b034940010884040074003149006145020809001c01988034080404a6502401c01c41d500d99842d03c564544070120b03180c0d0440820400280500e06510200003141c04070100d00702000442107250b4090200e14000300902d101f2020364000700c8021304940d1248003642502c00b0100004602010401c1c1194440c4030264403d01c258400050304002ca14102042c0c1c914a0280c03800d50780f2250350985840c04094411001d0540034401210b0f030303443c20000303076100e10107441881d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 711935503 1250 711934253 711934259
    0x108041e0b090a11060c06041401091502071a0115120f0c02060f0f010807141306270204080703060c091d0414030901020a030f0e03010911031504030212181009 70
    0x1e04c281c1c03030750114180240c00034812200782c083c4c00b00304075038010341102040024248902030720380101090b42005107407010030b01c20b178102c661040d800741030054800c842010380051040001c03e4442c5091049041d0035007200c850100040c41140c00404401076444007003250060840c19070180c2e41c08142043c01a400601000046110f030340350039810550321443c9162550400450035201c010700d01600d1b0325051541600c108648071890112442c0f010940304122998550781c20803608203854070800d00600c58a40c04004001ea28400c460417100340c14001e2000b50b00c2c5944107000f406440c0c0e101028005110b10000c0c0590703901000e20403d0303410900d00c040c07500c1d00c0d140c05903072941c44040d50300e150b51003840142c555980000d4042d02581c0c15007403180c1d01c000325200461311122032040e07958155080010405c10403980380205821403504405640b50321354040031b00e59280c041101d02a0059010940000100103d8001407407401001d481d0080d040910b00081a0898900740c02840012070200c010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 711936753 1250 711935503 711935513
    0x30c03061d060a0501140d1a18010e1b090907030605090a020c0d0306030b071206080709020712030203091506041107140f0d230c0118030e0d020108041e0b090a 70
    0x50001c0c200900b8820441c1c001c0d42034900351b034050440c203408030680d034030360050402030803484240302440010410230141822000080c8070603c00c1c456040c1010720200400e010100b1048400040905200d04a0500040b04100400307081c1c042d0492082c566600e03404a000c0c1c80b001d0409109048100c80941d890040302c580c2880d00700380655034004c02d4030301b0740244002040710032040d8110080303242400503074541c0b00c101c80007051164410081c5100e200800250512160003400084d4000c0460914500d540381c0d00740c003a440700325800035058001010007951402e16106190b0095400f03840001c201c4054036400256074864202600c01520a80c400b4440427001c10404017001c0300c1c0e20242c075012440d140082c2c4002e0400d0b22611448284800c14050030345101300f9641d0780760001000384a000341c54030940e98800f440d24000d90001d418500c5d000c4a0b8145480d00f4800d03964103030355000d0f184d40d8039243e003107079204c0c50782c1086100600a5901c1d804560b0703180c9210302a0007544090105280d16180c5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 711938003 1250 711936753 711936769
    0xa0f0e010e0c070c0b0c010b031b0909032a01020c0d0305042907050d09060c09170d020d1d040c0e0f0901211e050a06050601051801030c03061d06 64
    0x20390b81d400c1400c100030303000a401c2d04c504204555020b0611525030702d900c02814007400340c240c14560507100b401c0d0001d0340020082c051110009041c2c0d0301c400d035a00c03000c8500c1c0d180d10031104c01d100d20f100a680d000440c1c503010841d4440ca080410001410030518100c00341c03e2400d81c44c210000203032a42d042c041405130820f00158007046024410104080340a07211980c4e003001494001848404908000764664070f4028840b1540d100320208280d00350214043c1403091540203142200c203920191150041001880c0f500a450603002010000200401110003000c6074070300d5042d220602504180070f445a019803100f000081e1200703040d1142e204280000c56484080b950703c501100c500410501c40230806980603100303500c00304000c0c02c1003030800c076500180048410603607400d1244048144103010846070b594a105803024052511140d0046034107000d01c01c2c800081981a0003050700e2903003e98094100c60515040c0854865174031036060103410301802c0b0a01e0300e0780d10841001890303c2d180c14 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 711939253 1250 711938003 711938011
    0x5030307050a0806011e0e06120903070308060316050609270109150f050d02060c0a15060504050c3103031116180906110d0b1f1205060a0f0e010e 64
    0x41e0000386950202c00404c42031b207000219005000c071121003a1141c0d1582e10480d9404201c43c040f0441d03500340b040c101c03a905d52020b030b002c1c0e001a01000115a003481d000c15103a000c0e00089413803040341030412003080116440004804d0f8854407075400410b1042110685000d088400740c0201025894040f03820180c2d0180a00442c11515102c001d01940e80351150900c192401034448a442032480d1011480074400d40d0030ba03038290700c100240700003040403040b030f4407103414110344051203c5540d680600080c3c030400d50360309120300c20510084140715201c500440c608580a40300c04450000a00e10151102c1650401d60026001d2203402c81074040400c640115103a440c80700748042854422100d6606600d0485502802c2c0c96140620034000e0f16003000004c91032800d101640d513200e0442d100024144158554014814600920780300d106a22080c0c008002c1911260300c40551450100000c1800030281940100d844502080c10151282e10401a060340e0001100e254144281142c128070010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 711940503 1250 711939253 711939257
    0xc0d06090c1e050f0c0a0f0503031005031501051c0204050705090a0b0309120a0309020a090605030105090106060203031302030703120230040306090f021806040b012a030c05030307050a080601 84
    0x220b00c84940d940c0c8102101e100c244008000c0ea210506111190300701b1340c0c40800a0001c0e012031146d02c0178014088000e601070300c4007845003001999104141500c640440c0354005901c0b802c1d00c0100000d0400c040b003002c201c1039048908011749410380c0064100e550070b445410001b080480c514210341002449039028101e9605031031304501c1c060f14401d43d0b801e06a0010301c81c1200109001e01d50b0750103900b001300c403e6030040c0310510582c1c5543e45500203000701e2050510a60804021490111061180c0c9080e298241c2c091031540e620381803014040c0c401200102d03010304c100b000020101d400030081410303840b01c40d0b0191881e000207286405990440c025103090102c801f0003241200c070b465804031030443e40d00c4a8042204026414281c1e2a00c4071081c000e5046815a4103007003c0505050754640304205c00c5070108242210f240c011103080c0503035a200900d102495042814110140c0d1074400e03c580f003450501c03400d4840d5621a41940c1040d103010300403803801300b448030302150818443c60f031042d001c2c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 711941753 1250 711940503 711940547
    0x150b1203090a0501050a02210703030b09190e030d0204080606090709080a0f170c1612030c060b150f04030303050708071e051b0303040b0604051e0c0d06090c 69
    0x1c580001c2506140d841003c1c18000c0003d01101d0303980c024000445449088130044101d90405085000c5650001100b00e00080c0f402c0708001d19883c003003a41a000da0701a8a612240312403860702c000081c070103c1c2440e103242c88180310085000c0080c0c001803020302400c0024107210306154061240e5528054901401e010b42e5107003d001c020b10015001c40010780011000c000c0000c3c03810200c030701090440c09401801c100064245001c103000804903002c2542959000c0c410ba581d2101055600301000c00030002409203445102260040e001510318400c02030561141c81e101100c0a910f9520a21240c10350600c082410014076405220740e603401412410b00030040d03c1d10300360041c010945044142840a00b00d0b1140106600c41e105943e050101c00c1c400c1e01c104005000503682e2500f040b54210380740e00d20000020b642e402d10b402203a000c0c2800282c001c400600086242c4191640108a2810b400c020f101d040c10b02c4004c3c4c0200c200510501c000020b28100b203001c001c080e1401010f0000f045508 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 711943003 1250 711941753 711941767
    0x60b0907021002030703060302120c1914010e03010e071e060212160c03020604080304081603080405220207080d0e060f1303120c050417010605011d0607150b1203 71
    0x20070b0031034461030740080c01640c036914101c0550040651341c2010790441c140c0c1c080c00b004007500190b54518414102c1d074200848551b080b03400442185402609500302c050b94000300700327500526079079080350802000412401c50fa100590700e083d072160b008584140310001c1004e0f182c00b034582c80c00f0240c1400d201818080284115000c4d507072041c059a8030802054051a50070702c03000b60043c2014580c010201075a440d51000c00560b44c0e0071a00602c00c1c00d000b010303e91401032186c403003d8011640e02c1400c1a00302840c04080106040d0302016440301400c031182c8051050b1031a1004220340b5200e402180e0311659070301030b140221001c0e11040040c0e64811410303c545012004442d0368400c505800302c04406a241c5070488181f0840e0203402440f50901018224040c0c00401a00c103a544082c0c2210b40341410b0100300c1c0c2a2001440b40e035011075941c0503088005810507411309640d8001038a40c07441d02103140e490f0031558400c1c2c0c0180d2030307080d66500f0401d042d1526915101080504030000c500b0114 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 711944253 1250 711943003 711943007
    0x1a120601030506042009010305010b0406080c03121315020a031e080c03060402040e1815190b0103060314010606030c0e030c0609151204030905120c090403030e0f0703060b0907 77
    0xb4001d08040c002d209140b101c00045d0030300c0c1980003c16207000e03012985c6560f6a00c1d100703010309810b40e0918461420100d01165600c00000d906151b0740c0000c0042c0000340b49400351018640c0a11010488040e105c1000708640d101034124680903c01540184001505400c0c000c111002c0803c00b40c030914558810844490382c0300c05070030f420803502078883e40d03285c4601340010000d214641c41072282820071070401c82491414041191425007901c1511404119180012030400046500c1d4004014064032050500d13a03952050034004c1d41810000b9100e40c59440d50460365440c0f00f14103225a44681c020b0000c10b916006860131800c9038141300c80310613400c400082d120a00c81e0302450043c480445d01507890f0750b038802603205040c0070007503180c1c4e40d22001ca8441c005160482e4140c01140f0000c50000b0a82422160f0480d030f00303d014041c0c880c3d043c18400700300030714101400c254100340e160281c1e0380700c01e141480b50b45585290603004141c0b980c07851404109460000080c05d1089000b2010800300355 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 711945503 1250 711944253 711944263
    0x1205090907030b01020115061e0302091509180112060b01111915141006023c0d02010e16050609060a05040b0a030b010329010507151a1206010305 64
    0xc1c91a04001c0b412600c1440100e00511032002c2041007280c1c0207000240e2036801031f0030180d9100d030070f003035100c0c1c0103030503030800c0d4240e120f92080690040c102d2010f41005401510141007403950040482d102040d80840503c64400280c1168603000c0c1040400810003d103845114610344003030a208507581901c0c0c1519896003082d89501e80c42c1c10804000004003c5030f03c0315980001c1c83e50600300150145803410300940c01088481d61200704501002080e588d000003018440c003040e13800d030012501c160140c800c400c80140c0c1e84080d20301c0c80078003c1401001080c8000010f8510310303400080c500d0103a0911526246204c1400c000210340c8043c20701c83c40e159003044503d1070b00d041d00c080d5030310f54842404552030700c40c90344040141c3d1808101b000100ba4140c2010070241c4c000d81c2c060240c00b811800c1d01e0084018144550064049040094815401080503080b1503005042e1568283d4100010209442a00d000130f01a05030035410000103140040e8449840e880000003420a50305643e621540e42e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 711946753 1250 711945503 711945511
    0x70206060409020a050621010909020a12230f010e0f011812030209012129030d030f09020a0f0305160b04120204020f0732031c0b0d0f12050909 63
    0x1c507000138028404447c040812a034625100040380300d1583d540800400406507202d040348140c2e0b54102c001101000321140224140c2c000a51b07000c5003420001c1a080b07a80e0021100a460041481d2103401c91401e01c540f507603800d00303c00034080342000741040758211211107040c01c1100444008500c0400c45410210204c029a4140103945054500044e90046811070000b8050688503096094800d80f54210f000d4030b681c507031980003600800314400c42c04009003210442d0903502c40545100000d110350040340f008140b040d400107001e021500801d10700f20b09030700003240c0d2100c010340400400a0403c5003240c1da821500c00c451021742410002a42880b03a0310035080c0825200c10b044040d581c17664116880684039000140d40e5107500c5c03600e04003400800c00358007640320380d4101802026035075800700c0b4a07172201d107005185402c0d190102031120b40c0b4400d00406606d41d81345030001c100e485600760482d06038007070345250349100042e01d880c3c26400354400d140010484180f0050010b43c88800c101a00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 711948003 1250 711946753 711946759
    0x70213090b220f140c191d060303070b1902040e090c4e0615040e030702010804151503050c0103090c0b070f05061006021908090603040f0c0e070206060409020a05 71
    0xa801d1194880071701d000c039402c070001d0b800070107221701e4256401102d10400071901c04a4165621250400c0c0c001c04185048404541540003080300c0c6000440e41c402c0340754410005121f2190761000c852041c012a040358120320034540c11030382440845030b070030886007110f4401151358141c070380040701d10130700c0c0f0303c070700c00280ea0320511540e5885d034103480354019102d040b6441700003002418000a0790242da4030016100014141d0310301d810b00b580780c1401d02940b00c219170310100461600403903500464051800030002d4548815211540519a400e8000c3d500c0004c100085000840c0c1582070607401c0c422079100382418145805c0112001a421400b010100c404601e515a01c400b09400c20109003c00980b008201d40941c4082080034502420f0f844291540340c1e003210440c20480d121405598562400a00320102c1889104983d01e0a0401075911911465440700d44104070340d07036104a401071744c01c600c40d684d50304010001030950400800354410000c40b070511200c0115000b080400006004180c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 711949253 1250 711948003 711948023
    0x1206040b0a0e19020f0a0807020c030d0e040b0d030801051302250302030903060a15090908120603030c0607050403140d0e060a2706080108060f0705070213090b220f 72
    0x5a10320b07083c0d2000c4a00503c81c10195520340c00b02c0d64800c2030342e200f0354002010440341c4001c502583d1000503a141d616001800400c4449003620003540c01c14104078800e540b05460755440000da03281d8102640005110380c0300c064583d4101410880740d804690702d488030181c4140300b400403080a0340074090444490003022102c1100a041c00ca05520a224109405104960030312814424560103000120415070000319400e45500d2558260707103070300c407024003151001c1c08448100303d505181c3c1c03500231f140241224601410082510b0610504130350715408508007290400901c900381800c0b0211f0150750001c0d000a980105010300640140000a4010380c400724000c5041d500403026442416052540c000004035581c0f449400c0c1d0405000e00d00001c1c07d5078000182500e000100c050145407080502803072640c500d607040322650000032060381e008448003500c007044069841f800e503c544c026034048841d49000308a0a407810030b60070699009011202080010582011150440301c0e40a609070b4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 711950503 1250 711949253 711949261
    0x9030f03090e040f0201080a0c080105100912050c040f0e0627072909150a0c080d0207060b151606060806010e090c01030507120507020f01020a051206040b0a0e 70
    0x141c90055540220100b42c11500511050103000141c2d114054800d90b41c004540c3c1d0361101c010240c852881e218000b20300b80100500c0b0320729203c800071101d00a03c1c507221200c60b42c0c80900c40c09101010300103032003a400001c07003204942030600401a15290380c10040c00f54512103608c16a44190062119810f02c0c9119024420355100c001d03241010702d1008201c48842e920f444000442141900751024504441600114800300041c00d584c030721a0300419915400103283d03001c028660240072080d04001035080c03101c00042d18007000c3c02100700141c000589a070000d00d800003c9901d46000d0a2040407a02401607248460350125000501e0f030011140f02e0203010302c0c02c40c000d40417582102d0b065000b4140089040002c000d001e500c106404401c0318000c071307007010065044400585096000a1054820750060400c81d00600e41005540c0f04031014907001e2201c081c2260001d0a031400000e4002541e108440020243c6a400c0b50b400c6504100e50424400000c003212120b22416004c156014001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 711951753 1250 711950503 711950507
    0x80f03070f060507091505040f12080306011407021008150406080606010518040c03091e050c040c0203130e100f05030309100c060f140703020313140f070e010603050c0a09030f03 78
    0x406001b1000360a80642007005072864016004030080111044030000f03100102c44e40c181407181d00040050328544a58004407210340d1410701c004448001002104016203a038022088004101c1c4e40706c00c07031410401d004041102d001040544251300f00b400c02d101c00f04000c2403050301300009080907640d462038030b4004003e42101c401081c3c0c0c41071600240e40000358158002504891282c00c101045031040002c020b003130b042119016000390710000111071141030660124031a4a880c0c01200d05000000b80142041d40d650340180718403074884001c0c8100050310601c12809420588a04400c05041102203580d90290010051083d5001090780070820701941000ca4507032b401403800e025802103a404140070704082d119501e0015910b00c00110954402c0c801d0720b00901140c040701074064103c0c0c46107044803251041e10344003805201d107400c10303802d02008035500900c4c00440c1c1400e5985003020150460f41c1c010440483c0641c10454040b240d035110740c1110940b5882043c21250010605007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 711953003 1250 711951753 711951767
    0x507020a020306090303011401170703020a03021b0a05060c122d1018050708040f02030c041404050c040e0d121404051c02070f050f040906050f01080f03070f060507 72
    0x4082d4040c0100428042c14103c04002541030351520640c04400c0c558203401110303420810082000105040310100e40685c0c800d4000b8411816145009070814603850140c2008044425405100e64000f80715501042414451554480010f11041c0e0900714000e0310150541e10003003445202d51814031180c140c50121400daa6060703150210b607054540b4102c100c4205c002c5160192422540020740c0308580610b960003141d200d00700725560445240c840380c1d40c84134003500d010022641030080d4106640151680d2046076208035003484101c40c24142400d00d6810003a0006045015a052031246c5c2e500520018180107114034a25040c03080c2c44d4240c1c0080c008101910081244140c50414132050200000d80007202c411005078401099942d44800c0c0d81e500214440c8206801c04c01d1001c01c080c5c581484034201005024001290504007a9144d00c201e9108442922507034130042c005001c6110104800c0c800310300503030000c600d00441c0c1d440d490701001520301c00a00d21511040018545807181e99 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 711954253 1250 711953003 711953023
    0x13080705010f0c02060108120732120d1407050301030f060b0d0804030303150e0105010309060917030405282909030a0f050304110f0d080c0d090602010c0210050702 72
    0x1004003c0055000d8000391240402e10600000340b00d100012495008034008540360b0a9101f586103d89080c90b05145013070040591000741c0c5070040600b80d540d13264051101c44200700b580440140e40702c000046201c103e82002180210701c01e5004200001c0c1d0b038000d01224152508880404110305440c0340c103c2c0642071605800b40c0003501c2c515004100803184001e032082e607100c0c3e101884400d40c404c2446c140040d043c8a050244030f07615004020f654000da200c051300074010b0301c0210301da001303d494600600c0c0c0840172604550030000b0403c41444414444140c640890030b003072402c008051080c5000340d0400d4031b40900f039200001c8249004c40380e14001e00090f400c600040e10002d2038010301141c0c40e90064a000c1c40464078400141010500c2981101e1107580d109080300e031071030050420b0180c0142400341d0160403011201151000c0f51070200034003061004500203000e4800c20b00e10040003503a0644c4202c00356030400c0314042c1034a4000c41e400d8a8218134030700024144d9100001240b0300300d4508 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 711955503 1250 711954253 711954281
    0x70f1d03100b1309080406030f0b09040b101a0a02071a0406081305010c020616140d090c1a040f140d0b0c040b07030c1e0f0803090705060c0102130902031308070501 72
    0x5642108120517400680100c44807a18108565131020303a00c00305035a03040c02c2c0a83d10081c24800100001e0508900d40d400448078103008800351340703c61404040160a21031040e43c940040b0b081109141c1c10400500601000c65440003c081101c668003924089c90140c0414425110b002405003012121410b42c8250010020f1010b801076060282d114001540c079105899100c02640b0711090144410442040c2001c070482e00e820040c10f0607000620006908032030550309008000b444050102c402c4544800c0741c00b0325aa11460800d00f248aa091a80709040c01110022500791a5960b00c50000d116074214401440c140d0324805034003141e11480c5c001801107500440c40d44240343e07104107800c0059210b9050003401080c9004d07004c0040c4084003000b0000801e0303680c004001800c0300d000c0d6420000307590403901e106803030300001070b81e9802c99007910040b81e501140800c81d510f0070b43c02c484020560200210b2a40c240341001c90140443c0b01c502801910b400540c071000c100c02540f1070419480a4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 711956753 1250 711955503 711955511
    0x1a0a1b081c020d0e0c1c05100507020f06071e05090a05063112080c0f151504090203031917130302060906060d060b18070f1d03100b13 59
    0x80c020320003c0d0000c88030103582d107140241d60500c002001900c0e00010000800c040c1080e85201d0304c0c01001c81070352000302d460b400703141d415a410070304ca40a46806000140c01420300c4203201c0500303500d4001c005020b0002c0140c0300348d948005130482c10a2000e02d10303091a24079651600ca102140c80c5c0786865100b02d800c00740c0007540010000c03d055007100c0442d000036003030030000a010340d01d001d840c5aa00a085488001d013810500007414a401081648030180984034537055201d0340701d0500c001e00001c18403000001741080030070091007014040081c000c039002c2010030490740100e6030301d00590414040e40303d52200c29400003030180000004010401883c18028a0050310176485e500c1001c2044000d0321494010400ca0000131482c02d00c900c4020700000400340325030b101c0202901c030882d0100d40101c15032201c800104814081c80d0f10446060f00c1d084000e603070308030b0020128116503406030798600c804046143c950380c01040c041c503142c054039404100054a0030014628041074211001c200740b070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 711958003 1250 711956753 711956797
    0x308070807081b070c06021f06051507050f010e0d1b0506010510030b0a0b1803070e0f040c0806090610140105030f092e1401031109071101151a0a1b08 66
    0x10000311806003c0050ba88180703c404070700d40234400e940c107a00a466100d50614401880780106001030000240a14201c1d4a04000f50041d2400c480510707800d10f0080e00f016003c0300000d60416000c4440713281501c1181520201e81d181c5544880701805228441c1c2000701503114018881c2c1c0000b0040d80004100403065555016409015801600b0384407800c100c3d5030145c07000e490003207190000c07101c02c840c144059984201e10746130009002041160040041d07400403c10640800c90ba80c8074884000040030141842d610405607e03005620a20100e228410b06002d140d80c048103594201149442000f000e858403520310f07050039292000000a0402c940032001d80d074800300140405a1040e06040001d03407990700800302d100c07900b40400340000c4400c0da86400d250030300101c0c00e607100c030640c50300490071b803000940036007503400d020301108050340019018045900304003010b80b081d12580b00001e02d420a410406410061012040004800280141030500a102c800c49400302c3d500201220b141d51 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 711959253 1250 711958003 711958007
    0x30e011d070e0f060108010311010c0f1104050a0c1b0c030212060114040221090a06050c0901031107030206040b10050603190e0c060306040c031503030207030308070807081b070c06 79
    0x1010701c5040d50b00400200810030b03000800390345501810060703580c007510b40c0c00c40d2119000a265105a1410800004407220105a076800c41d001310600c10b80b58108801e0342e070800c2200b078850217481d080f043d6140c4200010804d4004c140300900750b0214111004550280c2011180b45800b6480a9007008034000c101c0418940441d656061325103e925414240c2c4c41e10782031104902601140008103004c040f4502c0444d182010301c0c40d84402c0d0441198001004d07a075404c02a95020f550b0f030488000041804211507030140200203070b03d01ba0071441c1e418800d50b034500039a03c030409031010b0402e0203071102003204103035411155009010082e14150742d030f0420900c5800d01c1d01059403061075040c0f030280f80d00e18005002c40c4081032040700420503400c544a20301040014040c2c107407044141a6a09048108103462007000300085001781c01034414039181d41070141441c940141315000300f046005c204120701c1e4100c0a400d400c14920583d078401071805605100c00c80c400c00c040944003420508000821036 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 711960503 1250 711959253 711959263
    0x21051f05070906030b0306062e0908070b071a040203190b04020a05061e090307031509050c01051303080306010509060d090c08030a0207051905090c0304111c03030e011d 74
    0x41c119a4420a40a640b801c04604841078190650f50503004440855994030b08100301011184407102d089150741c01c200d9800d8882070501c080b0030045041c0030400c02180b0000c0c4a424000c111440003549000c01a944031001c003034184484000c42a00c03480410190349003000001254411030000201c0c1320850304081d04401c800316000ca126040100c40400c5a0402200366483e101030f00c82c0e040204050b0310780d0000c10307030804d100d80354161046207070000c00b18500d00416120482440c3d4001071002417410020309040000b0001e60600c08100000100442c0303660808003103d4000002d10388070303241c41c03004aa00b072080301303243d0350b008c100844e6840600780243d00105641e846041d003550125034502c2865200d0080054182c00750304480c034200a18108441e502ca0326007620240c4813000d5884000103550f5000960b002c03021914044100010000f0003419184c0040b400c840000d0201100c008180861507610001010540c031007000c400703105000d4201c07222130026141024007400200c04059a10 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 711961753 1250 711960503 711960511
    0x17071a060a05040b01080a0902011e05070c0e0601140901030902040219021e15060310020418060803091e040b040204060f1b0c1509080d110f01050121051f05 69
    0x25101d1a0000410340383c6446201c80d0400183c41d2461a580c491071071030020046104141c5c18030007841121042402d00b02e003990844001e5844050b02e90300c0c00e00b07001c820f0700e4150700641148202d08050004503a0000c0710808407661a030a4150b42c1e53704440100d01420510754000e412038004038110b900400300407607003900410117038202c51811122102014031818001c6243c101500114007600520b84001c030415405140070703049504648111441d0310482e030260340a40c0d14040f00c2c02c6040c4410000380144001052090004c50400d07200200080f1284080340d4203c43d04807446034642855120398016180603080108115180c56542a01920003c000b070480300000301c0603131410000003400c0b0303600e600ea143c10136080482141030100c4201100c0070188a102401a208400a5650300401903240e400c0c3c802c0e590902d01d02d448000301da15000091070b25a400740d0401e001880b00c1d141100c01e840fa88103101c1c25038840010309060080c03e10700181603e2909808682d00219044007a410103401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 711963003 1250 711961753 711961759
    0x4030c03030305090c0609040f0b0613050102060705030105030d0e0415170118080403030c03050f040306200304031202210108010501050906030a030906080c0d090b0403020d020d080417071a06 84
    0x200e6a134001099850708960790346140c1c040b6040c00000c0301e0342444d45c0501c100f0f4522500000e1410304800002c0c200350440031384018601c4000d0f0060020b940d061100b00d8014006082c064255410480041d0300d030104070059804001c0b034642005925580c07038200101420088051144198441f04101c060700350900f40c04140b03608040380c140982c41a46e203000d500c2a008042c0e20704040c2199822101d23180307844402d40402800340324541c0d14900b0714000b080298403c20b80000d0101c01c41448071105a44003c4105e10521705002b0000803e0700b000f1500c00758044c0d4a001a13948540842c0818070740146254003003041e40c0b80b00089084001540224140d032401c6030325020300d5a41703108050340d40d0340160000b000956424000c004c0f090181030401d800041201c1c60354144904194040101d4022820070358400c0c050105010600d0b4041c00254040e825501c05041016a80f1001800c0c52030f0180009210140481c0001d00411000d0103807041203034098a410702007400b0300828070380200145c5050b88 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 711964253 1250 711963003 711963011
    0xd2007150c02030403030203070f03140c061e090c040c141c1d0a031409062107180506160503040612060f0f03030c050f0624090c1b010f0204030c030303 67
    0x3001c240004140d80860740e0580c001e524142d01941e40c1d20258600001c220180302941c91140d0300b42c08064050b047c01c0800c60001c00042ca001541c2e100588903801880316081d40d81c405101030000080b8130400c40060644010640c82c1e640f00b0204d5014400b80040c450b20540810031002809141c0c48240b001c4510000c00d20101c1004010f444810b11440211002c0303034000300003100082d02501d50301c2880406141098207100300c07900454400d920443e4074114110000410f2104402020b60b507640040351442d001c0036081d03480c40c44488102c441d0190724424000465030403030300f52102d20f46e40403079940182969122541c461001c0c1c00b03e16544013800039641031180c08035594903045030716011030311303d0114841c0841c6961001e0341d40750454802500c5a0081b01135180c03d0403c20000c0e540180041420410031f00094804030241841007036682d8070a8501034280140c02e40600140c032040302400340c035588010341d10b604090040c2904022003402070300106000080c0044d030710509044900a840c240 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 711965503 1250 711964253 711964271
    0x1080c09010512090319090503060a050105060901110a020d140d140405090601030906060f0501030e03030f011e0f08060a0e030306030a080d0f2a080106050d200715 72
    0x106000d00325010380050350a200c201c00b0801d03100c4030240c1240c40c141c15649809240184a42c0c42d81c00301030354002140d6500030402440c18200003040d8000c1007507c04101950605c000100c691045584180c10018110310400b038440c070901c10750504583c018154402d100040c98001c0f80d4114403e40411a4003650150051540c0146030704401d0500610b1064a000e00702810071047c2440548103a04050307458100000103410751007000c010703009040500200b40e24110004003522051201c0c100203400900601000c60364076850740b81960741c7d88005510341b05070080b80c0000403ca44e404080510b0742e0000018400102049403402200a00d1040c072818800014440e540e10090351032a070107030301802090020400c54405000840ca040360049039801e503640da00e2041c2c0c2d00090011155100c08100d00c0c1d111082c0b0004240c0c040c00341c1c21708461641c50600c4c0541140917400351070302d403d84c40b0f00364066004c2c400e1285e9019180c448641507250340c12420000342e1240748884200314036103010401 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 711966753 1250 711965503 711965521
    0x200d0b06030c090f01050103110c0a060f051f1a0c03040b09010e120c210f0c030f0c0a0902090f0d0b0609010e09120f122505040f0b1303200108 63
    0x3c94401e0700521000025a46040011002800b18003200005900b041c003202541403000c0c0300b660081c902426010500e030b00c60740501d0741159409004555030000444400480190740d031541021920b01031410605400208001240c40c402e0149241182c080000c0c08a61101c0f03650140681907400c0e03840802480300a000c0c03014603003116081046035804144a0019031800c40c5420545043c003e082c6194070171400304040c941a42400d049145800c222000b140c43d00f020403000094424241c02801075078a10404100b40700014001c0308019500024010701c19203440501e01c41381038015100c83c46450701424462080002a64498498a140c000005d03420514034ac469011703070f240c90040d1101b070a21250000c100d920170060000300300001e0122403000c8202141c2c17503110302c50344514480c0f07414442c1e2000840c1d04000420506010040c8020b202c05107100b00c0c001d06841c500242155a8503a01090188825903944020030300410285c0b103980048001c074070703000300100a03240c1c2031503a150460b01d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 711968003 1250 711966753 711966769
    0x612030521040213020a200f0606040204060f080c090a0b03040326010909020a1505030403020706050a020604060c021903030204080c0a0311060a1407210219200d0b06030c 75
    0x1019510a0b8602d913048032040c1c0c0c541c010605450b43c1e06120440013001c96078200c1c000c072280385000d5a0b03005413804038101042407100590118045504501d060f040240c00351107414000a0b210070022444005140442100211005a0340040c035890703000350360301e00828079580102c2d412130000d124607400aa06180c05031001507000f81d484000c51a40c0c2c2040394800042c408441d0582e800010010300140140802c0c0901040041c15a5880d58a05c1c1a040c0689400e00380e90214042107410000312030806d50105030b042d00250302003c0403800350007030310003280380c08090400100c007110b00c45050300415406500030700449440d0001e548480300000e041000e66041444090802850044559640d1418030b008244c0c2d40c4040c18108404000203c1102c03040d00258000c031400d80049039070b14041440c1d0481b0640d81c400e6440103200090000c0e03400c2082034081070700144001030185044030b400d10302568214140e80d0180400d110001d00342041215880155181c45c080d0150482664003803e00003a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 711969253 1250 711968003 711968011
    0x906090209120f1005060406030b0c1e0a0822080c1b030f0304050409080c0f01090605010509130b09010e0d0e0a060801030b0c031b03070e18280612030521 68
    0x8083c141400440d1406005024004c1000b03038041e032380d4000400010a6001154011859801c0c104d40300c501d02083c44c2819000d40e100c00c2c041d60018825460840d51101c00e05038407400540203181000f0251703c3d441215081800002e02d4100003255243c0050800a42021150700c001501549210840c050644406440a0081080d0001c001c01c1c8101e04168002034103480c81052014503101c0e2080000381000351040740190580d441b258080140700107806402d015000031500f2039854140b952007284444220301d0b00429100c8080005041c411003940010f20010021095680e081d00326480100403c0910b01c40e1485011038500104a161080d6641d6041e07a510119503c100d03114401c400e0700c0c642008180d848000b412480d000140c2c80d120000d180038480a403151802d944842080054100d035018000e41550703983d4080040c680581405180380400d8096013011343e280091621001e00440d801c1582100e0416a8040c00c166000c001881d046d0840000d40b415641c98150f07150f0840804e0b9 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 711970503 1250 711969253 711969283
    0x7081914040f0614040308160c050f0607020f0a0515070201091e0501050d02040f06050c010c2102070519080304030207080106050a050913021221030f01030605070504090609020912 79
    0x42c00c18054a8003941076940380c0c07100b40c10740904182c1c0d80d0351200341039800f1010b1100010b00d4005aa8100546201284040c0c50102c40851041648401041c0303235016090f00644a1012510086110345401d4401e07c05000080d05c26242c110349112544c5482d80701c0b460803400a0f4003500001a940718a405200e0750800480000c500360b8500780044580e03030070042411014581c02c0100041064000c0c0e00040200120b480e150b0b11681074000c11402c41e075158990720148240402c0076199400345244c10101d08800c140e00603119281410b00070704c0c02030507290b4200020000a404000c0c00134034000703035101d80c1c072907803c656400707403900742007426985c0910500d5008038116400b03114502d4002d0625600035070304d05020328098075079000103241c1a0440c074041d03826041400d20500003804000b03191814450b00600c00d10b5070811011862288405200140045950381e01107040188140300711001840040814000f082c2ca51044100035031220740007910691080441c8030102e040890b40c001202011 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 711971753 1250 711970503 711970529
    0x60509100e0c0f0105130e1e06010f05031e011e080d050f030a0b0d0c0f09090206041e170d08160c14010b030f0304051c0c0303030c050708191404 64
    0x900f40268007150181c1503041c4081032241c9520030055501d200024400c8945040c0181481c0c180d06a0b00c81d4003ca80c22000c10101d402c07c02c6598010003400e80f0b0b44c043e40341041e03407071703581c003055107500c1000c0d41c5503e0b421400380d000001c040c04a1480300500c403051218010751207a0700c008160b41c4820801e815000b140c4203000228a8480032000345510044400340881c0c440341c0200028032444076400c040f50b1100306030b071041c00040c24203407005c4050420380004221000081c0c00140f414000e520890580f42c002414541c4a10200d402e040001d1500c903005040e040300c0780c00a1a25240c450700c040001030b614100003103d0812001b40c00321900c4503911050150340c426202d400c180c1c1c800030903500d841c2d074a0b00c03043d00e9581c0b070420100c280d0458075070207903880300d06020400c107004a20400610200c00245286000710700c000302000210380e0326080000310310504030740a0700c15004501e80900038010220b041d050304403000e00300c030844028035910f040108902050a40c200d00480c040c00200d003580d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 711973003 1250 711971753 711971773
    0x150c0709050606190c020d020405040b160201050112020d110913060e1f0518030408012915030403031e0203041e0803011509050307060207082a2704060509100e 70
    0x44407a41480360000c0d001f5951810190080303800d0b5807080d00c00721107581c0c00208015a80725900405407411503544020701c031079450b08105005041d501c040c041e10502601d0041010004440c50060034440050856425464445050b0320040700b450400e40e076031400c251406d0720904021034840402e2104060741d0b00304915594940c00180801801c202d48000b248428440c094001c01c050300007402e0060021a585041c0e1015081c510001c1c002d083c00000070344040302103a039402c030164010110151712035480c2c3d559401c0440190100e416400e044960100e51620741e803400350001d502c1540a0b0001a544955090607003082c44507099019000a005200600c29441850200842441e8506d0900c68054a400010b401c022440d4003010159021440800c0030100501448486001151401040602282145d03810f4072480030840e100d0f903030ac040103d080c8403078130100c40c0312400038040c10f001da86020314008008000503075110f211441a44150484003600c1c0c0913042c1c00010b03180c058100d17001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 711974253 1250 711973003 711973007
    0x30a050705010b040516030614060d020a170a14090d0e041e151a0a050d0b041e201317010e0312060f09071b02150c070905060619 57
    0x921001c0394a5500d6031024002070faa107004080c0220b80304102041021032010f400703000c9408507030140518015404203501159105c4003078841d0b10a90b5080036980302000722044900607107404c40e03024250034080c180300c44010190720000400c1846401c0502603190407000d1591002c0da40102400154110344400550400387c018070f080c0c68603a0380d89561080300e000c0e410161400c123981800d1200f4000e00c05c02040017515050031800c030915408614010850340024040d01c206400850364a4460304a00c0082d11940d0003003c0803980d00c11040820682c0b0322490001d000604840b42e4020ba80c450b00741c04e60801c0904a030103168150345280801d910b0081071801c201014a081c48255581c0c5211144640061000701081429803104541034941407081015003c0c82e01c0807607000d00c014004200140b5000502803490b0444080c0030403a01c9401c0c800164800e50a5075031150303030800482c0080d10980c00082c0c000a851000788188600c1d55110103007c842d01490210304c0c8542110041c00011074 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 711975503 1250 711974253 711974257
    0x7022a011110090b100b040b03040602070201091d07090603020307020712052407021b1c02030a15020a09081b01050708073207061d0a0305010f0608070801020c030a05 73
    0x107012a800c0e0342d42c424160640b40102d500400058845071046010012981500b50340300300602500041c003410141080030944071800020320040c100d40e03000656405580c01040c1440c014110303411140b050070180040410130a0042e02d02d5800306080e80400b19405e40280241c9200380d03219401001c40074504040c0390488518140c095038540101c003040c41e820841000117000d104042c031009074042c1032416000380b070b050304802c000c90704031100c0165548a6481520000d0b6200d05c012821543c6c40d140d000090401e0314005000b84500540c41020300c40c80b01030340140c1803404081c0c440c103454030364450003d40c8421801385038048070b4080f0941c0d804198080c2c0c01070120940900d40590400070155500c00443c0032070060403403201800b66040031a00140080d0994411a050260840c145041000b030a64920910021651010501c2207078060f1070b4416000e0045407c44001d120074004061b043d002000940a80c5440d809464000721745a0014005c50f51040d1020004518096041c50f0445450b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 711976753 1250 711975503 711975527
    0x117071b060b060d0b03070e010e01030b040201050d0f05071d03030a110a0c030803060f060c060613020c15040506061207051903052a0f03030301090b0105120c0307022a01 75
    0x550b901c044148035510b40001506a403100e10700d002540341404010546060f080c1d91000da490720700c52005200801190445d9411640d0280110101d83c47e903100503203503030003000580c41d2f482c0d2400d0311034100b15000d504103c0c002c1d400d85e1500801444407007810002072102c0d82800350180d10030400d0242c118070a1034040c0c140104c1105860800c2070564680940c28900d52060310041c0c408018040103251039524091a10801c40368140b0341502403a07150b0311490014820742c8140d20b440300740d007a40340942e01122800d1a0b401d0503102c05403c001203a6410f144181c03416643d0b84a404000b6190b410811080440120070100030f20b285882c1c5000c00850340003080070701c108807210310700000003c1d0040082100e154000041c4200031180311100d44060b0444200c170340d2141200020250b140d407008002c59042d03401c0d0030f8010824140200068615201c1d13004100500042c070750030009c0c402d80d40310107940100c0f2142c0c00e442001c07800c4079003071040001225000540200c00c002d1001650b0082803100700e1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 711978003 1250 711976753 711976763
    0xc090311100827031b101e090305130803040e01170312093a02010b0a0603020702060c070e07020c010302130608041b060302130503030406020a0f050115140117071b 72
    0x90b581c0114604540050b410303101781c891081c3d03290403003600a009140012544a03410003103240d00c500740404507001030304441c4240d596004c944040c0741c0301c1d008451a0101c3c2c4150bd50804da92480810b5a9901034410b0b0302199410000224602007010084120702050000440c14407500152401ca01074010300809007600c81d11810002c5c60f0303200d014420201c107004000c5c81c00a080c524110811084e108100b00c11a490300340001c51680d200c641e0b003030035240149001070300c4160380e2021402d907214011b070b00e01640c45500c1d00000c855802151041c841d480c56400d81d10620354880042d0181c0c05007500909884066580070b0094030702c02c03101d00d603200f409189070300300840355001c400da007080305a00305500003034000401300a2011441e144c400148415801145000d00d0700c44001d403201c4106000601e51518840c48400f4800250000010b080d0403000a0f0781095480794816440c1a61400341800305d42020701168600d040c024101d88680019200d08920b4824105085024114184100c038 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 711979253 1250 711978003 711978061
    0x612080a09050405040311011404081c0f0212060a090203041502070206070c35060708100e0c25020904061806060b070605091204050f010e040c0903111008 68
    0x1030503601ca0044c940030342e000792100b05d840d0100f091120300350740b0f2101c035134000f444561041c00b000906c45002c0b41c0d00303271240004c0f060307664440300907000c098070414400440302d034000b00d40c110032100041c0040c0e005a904491300480281d5801c4004c05034081110013801034406141003149029094008001942c07008010310300d0000d403543c400e007190800d03802886100700074600380c05112041c8014060074441140c0c00c0b6010a12260004e42e80e81c0b0003e00c4881003040c5034000c0b4407854580e000a0b07000e0440c140b201d04031480c041c0750070b01c2c0a8002c0355908540d980e14104e0342d08846110417410032480d8018050081c96520780c0c44000240244180100010000c40d52040c082007240c852000500b2a01054541e41d5290382009829100e0140c10404241c00c122118042d40350324500f11005c0314410703200503807481180c90040e58904c00c0d0707601058000b4104510b910a60303900c6204141075a20130559901c0b861160010300806003404050340000c6000d40000c1403112042188103001400a803080d54 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 711980503 1250 711979253 711979259
    0x6040320091303080c070605160206091218011b0317010909080901140405030d0201050105040b010e01170606040914070f11030702060904090c1d01060c0b0403050309070b0a1107090612080a09 84
    0x2c03085030012550274180402d0180c0c01103c1550500c42c640d000108071004210800006902107610300c40d004e0b482103105024040515541d002d2150038a02c4400e1611051030003c4500b03010384004043c040300080680f03036000104155503244940021150882c886d2810216080c0041d280d6962150701200c440c02c042c00001001c0d6402c0002c41c609003d2940082125450b04d41408252120301d04501e05110428840c8211079034411807851b260403819101c50391039124040480c0944c4034580001000e0360401048400c483e01d00030419006000c40d654010190b21b2054080ba00b0681103412034406402c00c105039000f500c3e02c40c01504006100401c0004d1030241652601d483c100c555008040700d0461100d880e00300c1c40706401c2c941c0140100e092642e10b240c45561a16801d41d4000c2000303051000100200307003040010807090b4058492075201d035965000050b070140110080008442e00352080c250003262121140c0184000c5078040080d040016605580718001078019400550402110398400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 711981753 1250 711980503 711980513
    0xc030e0d081b191a04030e04050411030606041a1002031c1d01140708041b060905150c03070327060e0a05040e0a0201050c0c06040320091303080c07 65
    0x2800d061100300c210400c8022002c52441c180b2824002600801c90000b40b4480410360209408046911100c10b031802c0e83d49525050751800803c201d40c680240c03a01040004004800702c0c000140b5000310210351159407080200400e0b40e01d00b000c020886508918145580e00b08155507000e0b02c459801075a041c5900001c41c2d04201094040409250782c403140318501030b006c3c4036030540e10500480c000b0f1083e045002507007200e103c000f510300c07010085000006800c0c8146d07400c0110304e0310b031500d820300d03591740d41d41c1c4000b00480e9240c09000c2c42503288403842490945c0700c0041310100000d00e00510b081c01c04684098880c0211410b107250000850190b40c0201c8551650a0015155540340d0300482c03c82d1009000074880c950f00200d010300e1412102c2d00010340005032016440d582481c00c1941e0310ba2004005042104141d1010b400c510003013004020000903011440396491032007800781200c0704000805c9500101504e85080a0740500c84080c0880c0c4114812907001a0840300c0c2840c0c83c620b91782c1c0c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 711983003 1250 711981753 711981757
    0xa030e030f01050c0301090b18010302090604110c0705040e03040f18140a0c02010617031824030a2f180a0b0d0b0301051e130b040506100b0403030c030e0d08 69
    0x442c2c0c540340c0010051280700c4852203880420003081d2400b5014490340f16062710000b2060002a01c60100040001c1c8a6950354100c0c04e503401b814612103884810064040e5510b02d00350150a2103981083c5440760078101c004103580881d50500400c01100d45400700701100c52170019008602c10b6260044140c511020581c0217008a081200001d0501e4a6190090866006030000f5003403840015451b11510000070642e00b0f50941642010a00207844001401c644191302c5250890003008070807181d001000360103540310f1104910140030040e1b24800300780c2d00f0b02040c07030000b032209200c903071000610a0b808054500c076410100f01160400e42440043c890154903400000600000114110b000040b40a11600d03054250b00900540c1410554400544000c031449242d100342840050701c02804081c480c14200d400011841840c02d050400e51b848680489060001540b02d26000076608100b4048408690701913880510114443d541120802c07140c04c0d00c540c0c07080d5130703043c000081108000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 711984253 1250 711983003 711983011
    0x90308180c1e1804030f0203070b010b0315030610030209060d2d0501181a070207051507172203051002180a150e030c0a050f150309030406080a05090a030e030f0105 72
    0x4030f1410b80e02d400d182c000c000880b228214401c6400078800640000c83c3c0080300b1b410741c0d000d44149512551550b00c49420031416503883c6a0500c204020301c020000c40340e12401c15a0300130b441c00303019030383c1e10801d00001c4286004000c10800041c503051005001660b05c0c2c507a0f011030301d2140301100045484d50f9003501c8200140c0040022500b64000410000e101076041e08040508049082d01d8200030181d240c2c1005c0c46002e0140000f03048042103030100d03074202d40384223501c803801070b40807405800d415190f40c014242400745030b1608202c05e0321190201031a84200d81d4014018220703d2203411100d070180d08040b5200c405101810280b00903a6140c11480026194609213903482c0c051b2404000d03e00c0d20480c500d24001e4001442e4000c00752035061741802130b902c0c2034410a070510f4943c00420030721600846c0031902180b0100500000000c04801001214525600c1c181c2603101c1c03601040843d60103a4082e02d49612414072180080e000702990b80c01c1080c010155040382d21062000d600351742040b1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 711985503 1250 711984253 711984289
    0x2030c04180f0602030a0509010b010c2a0b030103110105070b04060b04020405030a030c0201120b0d06090512030c1e0a0c0609030e031b090f06090117030d020a03090308180c1e 77
    0x5c0108080e9000c503101c0c880c2c0c082d101400a000e611200c40010704074511122000e400c1d8251001c4044a8141c58640c08441244004030919640d17941d0310340d6186900280001c9400c580340e2013043d0360070740c410f41c143c07510a50807481018180e15966070340e0005000b40d4034000d8126401b4000000d450313038180300f103850f200e00989400c603030312546100050105200c598a54000703403621101480796111103c2079011300c1e9001c0b00000e604420307070400c07900d440103102d04c8000442000003000300e40240702c0c011300b0403410960803500031504290b500c2da03040d004040c6001f00040303155003600081200707034020841c9130340607081441d095602e0901003400c1103e5030b00c43c0d0844401180c851103a47c140b40c00c1030366009000c280e024046080103000241402c5043c4140d45441d03041501803040707c070b070a1007150441a682c110442d030b80d603101c150107000b40100e11015004900c081d4002041e0390322102c42c155207841d41e18080c0000f080c2660811101c1c04001224000c15032645551140d20b4485e440c20007101188a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 711986753 1250 711985503 711985507
    0x23030a08070b060a08010510170a0204050c0d05010603060506160312020a0306050a151b0c0f15080a0c091802090a030507050a0902122706010312021902030c04180f0602 74
    0xf49041c0405050103901491041c0e141c84108070b0205010140d5030281d0b160a60800000c0c0841d00030700f460300159081c080c5d070143c981014040c5103042c0400511482800c10f00600c02603a842c0b2068048500c03500c52603402050811100c1c0e881c15400149040261003810b1001078540d00203503007000c0380c0010607410007103039480c2c1e010710007442e1400c180c0000b00401403e1312a903524814009102d0581c048050b801102842084800c00034085001d2000d0000a04041115030381c96450f80d9041c00403110f171501065140d400309003102100c2c0140146048681c65141e103091500c2c0008281d04e40081804026030350a00007a2440d07034408252000450103072000703003401400d080401c5040c0620390310003160188100017681d035040d400e0b88078a0313108240c2110071001054040b010025503203410071890b030b14000c000004c41040303240841c0149280565007116015140740d030031002c1032700327507920043d42c160710800b005802407401b0340040f943c54a10200085008043d603449180c07940380c15a04031751090b00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 711988003 1250 711986753 711986761
    0x30603011e150522200315010e0f090103080f09031006060201060806040b0a0906020d0c0305040302010c1b060b01200d080a0203130b061f09080606010923030a08070b 73
    0x60381c0c02950207048200c2d450520345886180101809600d04200f81c40c0300d0310f8807035440c403200c0d17070000044840d604c841c0c1155803450702100e1040201130624005c0c0c0480d40f00c0202c200181041080481c030080082e007a03a00716402c40d2180d0b1002e40080a03d80c407600310400c200dd0068a0a104c00c13401504000e00104902d42098000307425181e035a00031b0a0547e111408000119180840c0c55400a050480c001803018180c14400042e10800c9100e0b06860309058a10098550580c080d41c400d41c000d90081014001d201c50896150201c41081a64508041081404079605a00140718228141888041241c81042101043d0341c02038210501d9080310794844d8015801c04e0546600412407a811407642c601040c0d07440d00c0c0e41031603901070b2045404400184032074a0b209a1000b0990744400840c00030400d04030000e0005400b8010000b5a0243e907002c10740950080740001c0c203565200a601c2c820394801600b03010401307002101c003589841145407100100e40c0a03402045901c1c0140088562850 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 711989253 1250 711988003 711988031
    0x30703110405040c02030301170f0d0309050a060204032001050c030714210307091a0d0e011e06090b0607020d020915040515030c01111024080105180105090d05030603011e 75
    0x6027409000515041030302485803080700800c41e801b07882c04c0c1d424002000103103030402c0c2d0b1a010070410700030282403000a000c81070001608800b0010480c082e43d8844004940e001110310b4041c0c40206005a4000e1140c200003480101c401d021140804089034810020014986007074102d0001c00f0039907420001c14844519442010040035201502d001d01041094000c1104a0300c103441680031501e964030820000c40d0000e40104030044500e07007030030003e80d40032083e10b00105068800e00624900e441060a26800c2103426540743d15001400700311036150540900240c0c05c80240301003204a24400591031552f40c522070503001d041c0e0540812869a40b12080c549868180c4161078148155194440440c2100003620704142286002c00716502c4501d0707640c2000c0703410751101d10300d00050500000c141024150f1085102c2d90304051001e02080303503214401d007241d00030b88581e18150041e01e0400c030094002d41c025074000101800000707186c020710707410910740040314558580084c0c95001d130003a000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 711990503 1250 711989253 711989279
    0x607030c02120d0c080307022505030f12041208040902030a0f0b011b06200d0c03060605030f160c080c0a020307080f150601030605030d12110906030703110405040c02030301 76
    0xd8484001c0910714260940500a414504c0d0300801c101c10000000b400c4074801c0c808003c1c02a94184003460340700d20441ca11603210450f000310782c003034403603d502d540844200056500c105940c8100c041d240500b004056941c0d40e40c174010681c3e103100c08220001c0c14100620055104001c1d405001920320b01d42184c941c2650150b8100604121076a40d101a03441da65402e100c00d460b600c07040000751006100348501e49542d101c80705440c1010041025a1400503940000961030225a000c1182985414040c0d078a400191740b006070095140d00010001c036003948801b0103000050410034121601692041c40d194820304241c21950841c0307080030304504042080340d01070040500500f907040348400f411540e500100c4141c2174460845808118683d0087c4e000601270301c0041d055541203020a04042c11041e202550000740da841d00506590301c0c040d0f0400c0d02c000e05001450710b89161983d00741200503018203205d0b461041410007002440d966a0b126001c15441d568000e9516980b4003000d0703284034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 711991753 1250 711990503 711990529
    0x110d0807060e15042a05030703150507052106060d09080720030a02220c05040e06040b01050405060d06081b0405090303090c060c0f010632010206180102090607030c02 73
    0x90302d80000f8000040c481c1e0707409034083c607205e980f42d800d242d0588050210443d10395209540502030b140000c030910041191540319008005024400d07520350f6142224a44a041c03032485200091018448041c41141d103640d40080b0028006400d00c4072120300300d0112505404122020140000d078030f400c0110780f250b402144d100036034041124072125000f01c0e8880305a070000902c02e0903c81040490754503400040c82108202c3d200401c0b07100000ca0001d040d950260280e801c0c540602800038002c4d24107400342044260040c2d607914285460402032111036000300400342c490507102d140c049140c803810000d0320601c42c48501c08001c0f40c204a4244012502d0103441c081075a0000c00800c005810002600407102606858540c0d43d81c1b800d030340c03540c180580d01c505680c00d03500740500010780d01c0c1f0606105240d460000032202c45420440c0c405d0b045144071910450150308003070b002560b550580c0c00022540c01c00318001618003107a03240081e89990001070120040b071b944140243c25401e01010000d00c1d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 711993003 1250 711991753 711991783
    0x60615050403031b1e0302030c0d080708010807031505090a0f0602092103250c0e040b090a030f1d0411040608090a0b04020d080403120210050703110403110d0807060e 73
    0x31340500d030b44920441248071140c2c400031024400c1c403101094400c00407916090714540a690405c049004c00908114080e1080c000040e14400080781916012450318200d030307800507130088800c2c0304140183c042c0400820582440c0286640c040101d0055004903080078803403100141c0d81d042c11010421708081c3d500c1c00110040f1003610349041000f0000488040c01e40000301c40602d1030810007085031600d02e0700308c01840c8120032400007580350f040756a141e000d948100c031000f0141d0b03100e6810070360301d00c5110006000143c440c6038045920b80a280d14180ca503907900b00c40c10018201001107000e80c1c0c6c9802045451403c005002c008843e441131016411403440b01c0a0300c00802245c41e081c0304800040c0001e0b124070211302c5c004040011040456005551018400103000c2101001a4981c1111107442140c141000700140041d0f101e880b420389a4a000991035040c01e08648075000000e552200c0c13690402d080b80b0b001000700d02c00c44040d040c018801c68021405200d8149218200403018101400c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 711994253 1250 711993003 711993047
    0x708090c01020a080c191113140708070915020309190b07120e09040b5b0803030907090506210c0a06020309090609070509060706061505040303 63
    0x314581c0e0105107001c00326001030b0100d40314400160620f04081c16840c0741b000803100d9003050001c10403441031120782002c0489400d400240042c20007016210101d0380c081c0c0c8111000b0001c1c40f000d011f6400a1340040c0785190078840540c6446c450054596002c0000d00907910102e502c111514210050106030207e040086001900d40040c03481c041c0100d2500800100180021064031441f070700690060b604028118503170f504060900135645e000642d5010b1140000740b2544540102143c08501c20080035072030000d80f8020423000c4a0b03061103ca01e581400300085911021114510414070003403c265000b85030340b07042010401c0e140c861203070700c8081c005052604014096554204601010482074410180048041d0b401401c05015000c2240d100e49003420104400350b000014103260001512108000c0d01c940742000b2122808403180c4001500810131030b90142414000780401d03500c5020f01140040e00e440030301203a914100800b100040e0f001c40d0400034143e00080c032a200d003100f404454 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 711995503 1250 711994253 711994273
    0x2031e070f05091b160c032303030c0702040f092109181d0d05090f0f0307031e060c0807030f02120705090f0d060b0a1a0720090906070809 61
    0x80c54851008003c0b2215444114508050000500440e003540b904001c1c5c049080303c0902d0103511000700f501080d9240910301c0040c4140c150201482d070800c0300c0c2c9500560560356140415040c2d03512800c0101d812684802e046a04030303140b4003031240d4151217408504001c0d240760000820200c06010420100422103804205080c50000500502c1c0f030641c40114084560b140c0341d070440d540c507500f400c04510503001b6240c245603000c03028000b034040403103042c01ca0102c40c07810441e01a00038180030380d05401010042000500c04001481c200140649454080c4032688030902200e2112043d41e02181220b010002010b6041c41664032000f0401000c50400c400c002500f25440b500404040074010b00084041c2c1554070034090020103070b8001c014616070307415440c054014024811416000b0140300f0b41c041a800360300005080c4154102d1382e03180c100740590701c1d4040c014005556071481d09500310502c81494542e10a0f1601c07030415500180020309180300014018040108101040d80042d600e00c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 711996753 1250 711995503 711995509
    0x110a05030a090f051e0c040207170d091a0f0609010303020a020f0103022b11030106020a080d0212010602151602030a030e0c041b030e010204031a1302031e070f05 71
    0x40d9820480c07010001810500d5442d000070406030400300502a8800d04031040100d90004007600000806a0107491080040c001408160301403c10001c16800320007000c85000014078014028180103142c020031410001e0300c400244900c007140e00d6208045031002c200c5401d88802210344c100c03d086d0b40710401507256441c000c3d01c0e440e4240c402407048298094880b400e030310036011349207084034136541040e90005404030783d41c20044c40901580c0c0f03076042c01c400b0098000018141d0f4121851034003e01034014140d5a80308090340b080410707480066080c4000c548080b08086210301801840d001414122031a412010003042d00529681c095142402d4042d107c3d5804000d4446215803400e0205491881100d82810704191480040d086498505a46401c0000200703542440480e074604100c903c9280396494280d118501003d05880c516000c0d820b03480d4030580da1a940030350f0781a107590b20302d007079540000d05110f03500305078107030148010f1a4840204030910000c4010461600400710325403628002c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 711998003 1250 711996753 711996757
    0x1031205070f030c032708120a0e150f19110a02030d03020f16080702010809011811030f0d081b0304021c020a08060a2007030e09071b080a03110a05 65
    0x401010004101c15860425000b0030072038144800007420444c0001e502121010220080e2090815510030342401030b87c40e0f9134800490b0030303142c540c0e079541c0319200068007440f0b03040d448116110030001c001c01005044110b03042c00f41500903e51b0000d0000e003c14030000600083b0f0304d10000c66a40c10040c4004016900000d0401d5010307242c0c00c001d42c0703500030f4000c64012406904013550700095141c0000c8100300c5404020305085200744c03118503254a92445003801c903040031108c0c4044807004000d000c0411404014071030300b41c3c0010f0031510042a0055514142011560110f003c030701140e0a1200307403480644440708402c94820032501f1840d00d50000303070110000c803450380c17a0b1054490480e002c1d910340c000e003a4060700e4407000703c4e005401c0102c2c003e4014412a600c50716190640d02d00030f06101140421540b00640644e141c01c2d4222403a02003010300d80e406440e880c140108a1501c1e950070f2494598610280d014039011034889406150140aa4402590004401c042080f041313840b00c1e08002 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 711999253 1250 711998003 711998033
    0x3010512010213031104110c0f0d0816050d021b070501030606030c0e060310030f030e03060112032f0106061101050f0f0c0703050d050f04020406050f13320103120507 73
    0x39811041c0b45c080000c00c001784242220b4100a032000038650300c0040000404044411004003110a07407078080004541116040c4c2d48500007000d005604100c076803044002c0d040c46a809030b001403802800410801d030810905162402c19080071100300529170301340c89010000e2805090502c206407050748000e011010b01005248100e1020011814161040f18000007075079106614401c046840c0c2005091038030f800740c00074031034803032680003065582000308610215941500c81118003d10701981c690980300c1c569210351010b03009070419244110174058140208403c0d10707504081c0842001c2c090070b4a80c01002c0340782c1410490103205140070599400b5034460782a11403130b5182d24803443c0840c1e03284980205103a500b030501050101811000d2000b900075442202c041018590721001d2068007400c442945600009190240c454515075401200c441d140c400c00f006611050180c80c501c9245001d41403940d060b01d9603005104022101203100030780c0341c89083c060b00309222a0b4440151854a40c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 712000503 1250 711999253 711999263
    0x607230a05030907090606020610050a05010c080307030f0c210c0206010b0a05070c06050414010207081b150d05040b1305030403080d330e060f0f1c06020301051201021303 75
    0x142e00c1840900a45003d41681078041c4151660ba50000756199400c6c0e81c605e092005481d000030f0bc034a004285003040710f40684132000c104034140c6400a075500028080000d0640301c8050001451180c030070580200029229211100000304003140341d210f40641e030174840307894218003840360f035000100ca50460b02041640f603070302c80c00c104041b00c86008070000141006414607020541340d82002c05081600c500c0d0381f107032070303956205401240e0328102031180206541014400c1004661001d00140500ea0042e284904580c0a11a0160703694040c0d00100c03646a5038406020400004035843c40e044201c114800180c3d03643c50300d51548901c110305c8014071031500010003031014031140c0c0109a04407420818800005142d00d503806002805480004105044007004030302d0505801c071150141c0c1c0b02a0400c07a2082da0802407040c1c043c0c81c403880c1030703102840c00164600801c200c40343c2502c1d20300c10b08000d41c60354580b1061120610701035558400070713401884800862290b000300d00d801c490b084 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 712001753 1250 712000503 712000507
    0xc06180e0f07091d010303030c020a0308010501080606091f02060f0c0d1505061801020606010309030c080d0e0607020109020f011b0b180708061e010e04080f09090106020607230a05 79
    0x800540303003103a056002c40c0c1c4003011404c00300440510440d649040341c0c000d031000d00a20500d01402c0382c807981100300040205080c000140030380d501c2181c41f12761092010b44414135215440c000100d664124000307542c001a020086c64420990520015030000c0990a90300c099051100d900440c0380075031010015500d41e6460406c001641c40030380200208000340040356160b21040384c05041e665000c4845025214070030114005512a2203040070154140c6c0d05e03c03c00384006d603101c500b150300c54800c44030300540710951003403c0f04061148034042c9000c3d40001a0188131403060010380d5403480e003c0350504c5426030380290120303031420124141c958007508042d505d075204c09000611400c642c280700f4103403040100100321110001001030080d0b401070040c40003500c140c040445e800401b40516805100920003140003c5c9040d00a0203100803040c52a0727041010b900081911884c0990041d001130780104240881903400c0300c689402d61000086c120035050b4038894400b000d105400c0440104080 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 712003003 1250 712001753 712001761
    0x32010b04030f051518010606080118020c01090503210c0313030f090b0301170f031e03070212070807060e1204060f05090901080f250902070609020406030c06180e0f 72
    0x2040c4020780c54820114411280340c1000f01d000b545c05010580030055030740c0b80c44000f1584a0280b00100c0c100d440b034001503c0049940f156400103500501c44440340341d07492f032202400003401030018000e0b0b0912000a1005442d0394913458110081c054002224030508000740003100096103800d031074464150a08840b00005110100c4600d01503030702c40f4010100c08000400d0031100c0c0d02c0c500c9407020300c2200711020090f08854607610380c400c2000ba8034141d408611078005d4801c1c1e85c4c3c05554012190b006131200848070082c9c0070059805407400b10781d5400c00151100401903648201d00c13421690000400101101e110008801e02c04c601840e018060340c403100c440c029100710100c0d020540d000e00743d0000e9503940c10005a658107000303072601e001d000306444842c00c2d03041c00c10f04801c280700300254061818604000c4e517000790300145013520070548455030f40000da00e8500a0700003c40c414180d0f00051882c004006000640309100340004207071079034040010752900c41046400c22001d01c5042c1c40c6403a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 712004253 1250 712003003 712003013
    0x1020d240f050d2411090a060311030708091c020a0b0f130b06060408100b010e01110d050f0403020409030804030305150303090f0d020315010515030c1902010f32010b04030f 76
    0x4104d65013140700781d003842c0040312982561809440004410786031120183c1e1202d4064058521041c1010001c010a20006214911601c86030350130a074003009882140120880c01c404803150700c0400d20150b0b200d020400100a03a20000a901000180000c102030410000104005413032490281c0000510b40c0480d5250f901c03541150010315400301250341305900c0046040250612082481c040f81340074444540ca540201d02c0b003801c460348007000c2d10004003008001c2c2d5080c0c204c80b6500c50302520a00c008001a211803065115542c000e032240400c619241c0f17401000c0d070310020074900c81031104030900c80e01da032400415610310740703011180381c2d20002c04d020115449042241c1c010350315119003480c3c5000d1100410020b070603100190384515403603e804081a1492009507030900c4552000c0202004841880c80603a48070601c0d031001140e04c811521000040c1d510b070360f20310b640c8902040407150808000d42c02600258102414140144d032615202182a000d50310015080034800541001001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 712005503 1250 712004253 712004303
    0x118150c05010216060f0b0306010302060d020c07030f081209010c0507143d11070605040f1221060303080619031a150117160201020d240f050d 63
    0x1807090340141c0c1c54259139080a00c09010170503041c400651600300c01460700d00307001c030b65035060741d030003504462038000240e0390880258025140c10b130081c000c00d0008000158405500100c140c02030826940f01c140b83c80c1d40c1c0e00c2e41280034014051503894203841c200c81680000680e41e401e5041032911300300c4804c401400c0d007044d4540b07840742500c034041803144000360001c02c903102900340518a40c2303c2c0c919440880c0001c0300c4801c580d143e801ca00510100b80003d030140c11950340203224051400b50007034a551484865007500301802c0202e043e40d4660286140110700c2a5500084100d00703102c4149980c030301234070084002e07090034080c81343c0049010a4110100c00000116404040f540404044516002e44180b00b501c82011002150048040c00e6103d106e240002e14214010441c0725141d82c0c01613449405014500c60170365400340071800b50a030f0076202e032420300d4100c618103034401c03800130424a00b01c1e03d0b40d0f0000300032041c5a86081c0000d1712000302000c3c05a03030049030759490401944100c03ca107 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 712006753 1250 712005503 712005517
    0xa061e14040602010e0601091a0405190c0503150d0f060c0c120c060b04021c0f0b0910031e0c050105070309050306160912050309090c160804050118150c050102 70
    0x40c100080c0001d425a055205044044031002900c5180c3d0b204c2c075165041c1e400c2350b0030703d0f401004030b1a12044580303019404182c102465074114062486031061070300c2a100744110841c041b4602000b04142d18001501e00300c1c000000f280c0020090f4243da81d4400b0103c280c4c0c00c090710a554031910320006501484c0b0b42d1104a030481420038801d0030440d802072034a00e004408071015030500c1c401100e6418580250b0f0100049261490105000c81e00f042c00184403e190303806205407117403202c40040e141e8a01c494000c80950a03034030449030541c10322440310341052014501e149640b403108408a4080440c4d9400d841e0246031040d81c8511a0600319489030351904803a82c140030385001e1100c2d5408011802c00b20414030317222806400e683c0c5290f8503503011402c01c0904150010011880d03a450100344055000c40718000390707820a07a1051001300300102c007007000c032114180001c0030f001e150703008a0511402286101c0d00c0e01110300b04000d48614886000c0a0402e021008404404200003901611343e0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 712008003 1250 712006753 712006787
    0x160f0506042904020102030a08090106090f060e090f070608070903120201050a0b060a050d090f060606110c0406050a2c07051c051b070c0801060e04110a061e 69
    0x11420242421109075070101d02100118118003650841c410350159418825501600514181445008249c0700c5110040052419550b5001c01148842e12031091200c092106100080d21509220a21500c10703005045540180d1141050105040d4001440400c1d2007032860400850307121020305803980001500010661410034600342100c5505500c00b901c40c0607070b442e06001c50200c85040c00040d00c108000c040000c0c1e130800c40101502c0365504000f109510410300c030703c000f8426482e164126505a04920001005042018208203041103110100c403c211800c100303141c074010000d03d08028600c074803c404650382c02c0311448080003050f01c085103510040c8041c80c40c0340c41346c00108141c3c401c1007900c0d00241c8407030000129000a02c42c0900c02c42544190300c54000f0041c105100c25048550111043c3c05043c0012414540c20700611006203070000801025007407506e4030402a000800342c041c014005d40c0000c1141d590705c20b03440e803a1101900007135848044084022a401390159031003440c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 712009253 1250 712008003 712008013
    0x1502070503120a020d0806030d2307061e0b060a0815030d021e15180f0d0504090b030f07031e1b05030601080714220515030601051203160f05 62
    0xb080760900105019005035003619900d4041160554909a0a848550309503100a44102d492402038440807404003409160103211040c0046207907840c0e000c5e8804451030b0b61200c509201940121800c18100c080c640c80620801d4880c8010036031034041c151105040012050100d10b550403181030800142c4005000e5851414203d00041d5964100c0f000c10008290f08520300600300300b0106503007074070440c080c0992465450709101d13405443d224048500c41d5006e81a40c207a04079104001c01030030100b5545416454921b040440303000c80c0c4250b00100c1c040c0d0880703440c05c00f405e280400c0f1241075030b503c41110707955040440a03a446031111480c0c010840422006a4445200c80c0544241250411812201180e88414036507890f950b5900c940041e04030094510780062800724004681c100c0080e0710300c8034040080004030196042601c200a01401c98000ca18041c00c4c1400b00c0c5e4003405007a508104410810300f20a9a40c0c41aa203660b0710f000414940b600410040c41550503259402c2403c4131 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 712010503 1250 712009253 712009273
    0x170d121103151201090312090c0503030c0706030501090204210312020a020a0605090c10050307050d0606121d0d0503060604030506011e1d06100e090c0a170c041502070503 75
    0x341908039008005218810b4603c400039a50380500584100c90761540c2c0703003c2da103200207128001520b000c142c11580c1c5100d4900100392500d081001c1c05003a2070260040121a107040c40c09003c540041c0c110144d0310340100030500c0b040110607041d5004000300281c540e42d0aa690a084500d01e00542024440364000a91482042e50000f009d14425010341030400043d11440c4d119036071010070318891034004542c0c0511150b020b004802440c0c0c403404a083c0303280b80c800c1c0412840c040700e041d41c100101280c03002c241c206014405102d411403007124046840d8040c510b004034160b1b910090904a42040700000000c0d21645900090700d0007503900c542203402c1075856480c0c0902418800d140b00440100000002a45004c0e94008000c09400014880d6a40c3c07218024019880c01100941d000c0c0400c0c2c1c61445495140c100c2c0c40303071240c1070504c1010744850304244001c00442101110480d59040f10f01070100c2030200320125000c0785c13217007400100300508214060303040c46d0462b0f10041c0e05001c0c80c5042 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 712011753 1250 712010503 712010521
    0x41506020703021816120b130501081c02030d0c03090503032806050f010c0320030a170f06041e06060903060e01090302100e010e070f0609170d121103 66
    0x41c140c91089424181502080da5100e2034003008544101e0100e20500d0048203813401918500031800c0c2030303840490b426410b6400704041c9034011141183d0656036000420880c0028881d200b0b071203049610038a600c1c2c800340c00007980ca00a031044c540845640b119100f00c140e019900c20600d455220040d07035202d141030f81d40e0071300d020790315400d444000c104103a0b1140c5210061040c00c080d0b86005141d04080c19080004450521202200710103009040ca5030100a0b1680401e2141c502c50040056581e007900b200000d01440b44145901c00e044202000e000082c86841c013080c0e031121003130303d0001c2c4400842d030141c1c518170344450304100201c2c80c011010619175807003120701c010340380074680a000f44c1c4013502d603203070880d0480c18016005070040481102038180e82d401c21002150300c01e0000c6040300e2010075490800016901c03007071140c011414100241600801070b400200081b216030103071240c00405440e2290002104141085250300b143d00000029034000c50748000900300242c1c4900c1c000a803 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 712013003 1250 712011753 712011763
    0x90b01050415120c050910060f0806040f020315040c0207030c0b280503040302191104050a06090e01020306030d021c03111902010902043204050a1b031205090105120604150602 77
    0x105c40c0200400b40008181e1002c44e0308036012507641d50369200c062240c11004681003200a804158001c0d03c079070081c41c1c0c091070780c0040e41c040e810469542c3c0411f04000108000c4591580b068006e41d0480c2000300080784c6c0d140e0554048410502138180c0e901003580c2403c2c4192440b80105084624030080c413442140e000010310700c1346109400f16808401c0d141c800c1d0b42a00318154006102408000140e00c10b42426004a9000182c5200200f6440d44894503a01a80c12020403282c180c0e50110401000d460208080035203024140081c000c140e0403049500144000c82d150700c030a25440b840b2030003401c01e9101c01c9582c10003c00b10003241000039118000e02800c0e4400c8141c0c4100c0c101035031800d00501050203200f8001e21081c10101110403581c02d4080058002c105903902d001d842903000c04030704141c003280300020540e00081e205509502d045a62405845424002c10402f4880d080450742c2120032030320540ca000c031602da041da030340358001005403e4201c030a004007051400000b4440d0740000d1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 712014253 1250 712013003 712013009
    0xe030c030c1b03060415021c020c0c1c0201090312051201060c1b050618010903080f04050a0f030503030a091412130506031b0906041e030c0801090b01050415120c 71
    0x907414010314110030140e130380900352409802101d50f041c411206c0d85d500d6006100d02522108031050301401c60020f403080381c00402028203030f60001400a401d42c9042c0f0003c1d00c050400c4030009282c0c4900750002000308600317000043c40d01d8148016210040c0c099029504884000e25001c0c10b107603140d01c0014850519400116411031070381c2841322040e2a2584100183d41c0049c22440c145100190307114030100081803118140000b0200200204401ca001002c07550b10703031811207985510701028003006e11840e60122081030a006010f100050010003100e07009101d05001003994407060801e82c05031401d503141d0240d2489516034461410407102d000d4039802c00c81d403246101a42c0c0d5213007840071a2104492034022510f200d915007030182c0c14480a80b40d5020007070003460500b5124214000041141e6402c2501822903030810000c00a1100145e8060100b00c0e00074080303641e890303903400340c407400600980b4825070f00e4890070030200149a81d041c2c0240080c0204c1e4155020b58242580d4082d1140 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 712015503 1250 712014253 712014283
    0xc07090b0a090c1e022a04060e090610060f17060a181407181205011113080105011a03040212010b1005030907050d050a060b0d063b100e030c030c 64
    0x2208407803e54000301362910344007078202480c04104282d484080704031501000c56980123035501d01c0826034000c4420030030301c0707401c915000302818141000b040342c0c412030a52000040204050f8080d40c4913500c40055081101c001d510b00081d07445410015034095200c0e00008084042400d04003541c6d0056082a4031310405680091116103400d20308861010b0070061044090365030800c01c00941c0f072016a0161894000c000005101e04000d41d500c0c440d41c0b14148240380544910024400311400303119041c010301001c04e0912104292043c840d5103804000e0000e4494101312038221031100082d04406031a110003045120b41a170a114080c003030760001e58205d60203200e010380114290519081c9690050341100060061701025510b40002c1c14820324060780226480c115403002031070b90b001d071110312014644411580f610150000007c402603080c10ba074450820440300c1003a03900810200c14a200140d404140406144080d51030751144034810b038050f100010b03802c80c04810220b44211151494 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 712016753 1250 712015503 712015547
    0x2280905030c010c2a0608040501110315061c02041814060117040f0b0408030109050f010f180204050a0b0c0616050a030b0f03070303030e120c07090b0a090c 69
    0x10350905555881001c0d070280410780a0301071002140d0307a5450300000030005250802540303840740c0c0100c0c450307a20346c2c80300c000b0030054003d001c1080003e026000b8014042000d076802c1d454a00801200310148545150056400091158000c040c0d6002401450a80c1c402555940e03685c02d40c40426805428000140d1482d2887c10a07820000000031800b90340141c0d50b020000450540c00444403d01030021070703180d001c2d0984d40c2d00140798445418803075400f41641c41d44075071400803101c05990380180500b40081030307040140440941c1003c59025589410360404d4030b0702c02d9090001c0244a107810441d0722410395140007505002c960020a80e02000342e042c4d1b00640c07142c607e1084050a800702c41d0f0081a003c2c000003000c18802d038081100303210000c04280c0752800c0e94001c80d003031001c0b98100303800298403024a0720b01100d080210103140d901079104940b420b0300d484c804903140c440c140550407466407503189151003580c50354900720240085160422507540c4000d0007030107200c681d40040180c4900 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 712018003 1250 712016753 712016759
    0x190b090c0d0216140c0901060e0d030f030f0203040804241b0309050418112d150a030207021003020405060306040e0f0a030c020307080d090e0406022809 67
    0x104440900684032030019504014821600601a411242402c0d02c4000b41da5882c40110b00704940501e5801c183c840609071041c290014002c200e0b00c160440024007041c4075400066440c0c000c0700c1d2102c9901441d000e0b500e0815603608801402004107040192800401030006000058008000f1109070746040b07029841e0005001300c405218081400204e002d41d0443d030440c072080c107526900c8030310070f250403070004c1d45880c000f0701161440188240c1c1440d110310214100b158441010900d442c0407540c2c104000c80c4030040c181880801400090324450300d0310b09010f280ca07036031940a16100300132603454079010040001402074010000c2a40324110304211000301c2d6000b4400c46d001c0c0c40d4054142840c65a510082c800541500b00030b00310144141c40c06400490024025540a54030a584211100d0704500405103851a281c01102442e0000601142410740143c00c400403106000c000e80360b15520344c10194024028130f1390152101298401000310a03a480c003001e65040107540340c1d0309805803 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 712019253 1250 712018003 712018009
    0x9150e0c030a03030905010f05041a0a06230a0b03130312090c050909120f0c10020a020c09090f0709050a05160906051315020a0312020309062706190b 66
    0x80100e03011034054006007600340c0481d11030340040c40c0050107540080f9480507503040003000c5800440c0d0a03501c0011001c9030b0f151405a00c1e001c01d4004814100600140d4104801c2098104401a000000960740b05448580b82c859603445002050041c0b145e03501c900d401421405503840b0054100c0c001880d468584080e80464403440840319001025544014208018419503103405001203102e807044042d1100151100b100502c0d00e0085158050b40303800d55007100601d09a120185020140e0041c4a03a00c44c45a001542007900e01080f5072000a503200e10156500f0101e82800e5100c0c2802030440100300e0101c039400141c041c148003002003000e9542c460390001c118203d221a00c0016484400c10010f46210b18040c04449101280e540d04a966403442e500655031010401005600143d10003400d154006c00d041102040c0030301c00354175511b0004001e03520b6000050200f02400003d001081000d11407a9160121500c82c400321a1301d4185041d070185146449038520031014100412070f4be10381 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 712020503 1250 712019253 712019263
    0xd090c08070303020f10140f15131b080f06060906120c071103030a0c0305090102031b070e0c0c0c0402030c0705010c020f060901020f030a110f0a35070309140109150e 73
    0xc0e07d03d90710103943d114080d51801004015044000b411801048100a45c0d50b2260854120690742d0002500740c020820481010074100860418800b040303003001b610030380030f115181e400344048884a40d280c140e54005010b5001c1e00d4a0300000310b42e0700e07040101d1020030f030000b000803501407119048484078070740405a59200705001100099075212207040002e000ba000307813900d0181401900d09060880f000c51201400000c20965180d0120504100c844004240503410664048806c0c1c038000070301c106960381d13060281401c2d0003071b540000050b20201d0250300b40d429055110300288450b00103801700a55520601e038140c12103000303001c0841d030f407008140700302c440c914a070318201e60540d9500c0002900138000c20001840601d020008000c1194560006100c82a0700c1e850701c203c0317074000594001e1088803600d8408200740308915000743c2076000c4100c1030381c40400741c41d01043e540d450345850380149502d0a20b010b02903080980c07440c03c004078209281129030024000300501421580b00130361718 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 712021753 1250 712020503 712020521
    0x50601291804050604060b071b050103020f0f03041b03120914010c0b090f01050c03010e06030114040f0f170d0e010501030c061b081603030e0a080d090c08070303020f10 74
    0x4101c062410900905168010360781c00040217000003003641d9220310f0701c078003036210041c00c5480e0203964440207400311000c11200702034002884c0031410308a07400c40d004007510821041c801501d201200003010003407042100405c04c200300041c010081d56901c0e207400e001070048582008910402008074000c0c184070782d8011030001c141d54803070080303981c1e40320700c540074802800c0c1c80701d41d010300e442d90003015809004441c050b0211303041c5e66682c0c0d85400d4601562030300107080c02d4460f0b410118030700b400440d4295140d40160b00442d01d0401e5018614108046d20b8010b0402004001c0392140c5400070307403c507405400b243c500c5400510403c003144d00b0880c00c0355424000245112542e1000340100c610580220306944005c0d0440038040340a512401003540001d0b0102d000144020018400c02d84e16004111042c1500c40c02421545020350360b441c414002d0150a0300015618a01c08061040254442006228040a66103503c5e03c906000351100394003110820948181c3d010030f00081c03e0342c0b00d1a811 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 712023003 1250 712021753 712021777
    0x31808030a02090310090c06021e0615061e0301080d03141b070b010e010303090e0415052802040905010b0403110f060d0e0c0907050a0c1b0305060129 66
    0x80e50380d0310140c65000350400c003215038041c45182c2c805030900d03030240700300d148241c0142d441925407850310000034a03240c00f182c2d044036441d80c0035038000404003000078490740140c1506c1481d03d1010150700401d08a02500340303034081400102d9004180d032100700d40198142c900d4002518500e41e031281041d03054030901503544242c1c40c080b100013190440682004020700c260300e845946400101e80740c80200000a0308450490010300c8010002c041d0000801e0000b071904c408038840c90b01c0d10340c80700c12038074418220100c102610389002a00c2000d54603400c00750303050b0808200c2c00500500c00400000e41060203200c11140c034010021582c0e0641e00141e90441c1e920040c500340400b005814040d200c91030240b02900082e061022118801c46401009541c45103200180344920340700c2c0c10405000b0000c5c00b204144a0300f002412a40c55120150844894002251101c01100512080c400044641c006050740c05960004103455005500c002c288001101050084008160300d61245108461084035 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 712024253 1250 712023003 712023007
    0x5010905030a0f020a0b21010617130309080a0c08010c140403080a0509060a0806030606061306050f041d090106080c1e0f06040801331e0510030903031808 68
    0x700143c2012601545548060143c1c1d411980d5800c52001c0d603000700701084c40d6046054603105054000200d02e074018586450003c01924a110035585010400340c10910040d00b1103a0200615004d121010700420086045450340d080354207000681c40c8960068004c1542480d2502d000300e4420550304045404007020249082e1860b078a050710340d40400d1181c41440400e1040c440c1c1a0b5540c000b41000c0c024a80b94400a4606a820541403400041400703124640900c442400e40a04a01c290192225410003940d600150002c043c0305002e10391054420240003c100800c0b111401c40e580d002e140c409000788101c5032528001501c0303810045200d0f801c60240c604030451f055142090209460780501820007081c04100451f0030b90788250040d031403070781d103410f4030b40c60fa120a00149040e10420014141d2041c42c0f8408042000c9102d108140300244041a642d80101c02c203980c1100514004116806191000398041d0160007001d00603808280760401c04504c80e101200031807207039a400101d441c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 712025503 1250 712024253 712024273
    0x1e020a1d030312090106052d04090c090207240b180903120a09021e010e0a05030a030c0327030624051c05060a050a0b011b02040507030908120108070501090503 70
    0x85900c070f0014200d6800303641300c010014007030f142d02c5242011121172030305a60b81d00d5900c10201c42c143c0000c0d60071900680c600051840450748a80260307080c8c034100a002350351001d550034080c100c4103011214400841d0b4031000084005105d502510b804241690507101c0188003c0c0300d0003180303000b1225401e464104104500084405000340b560000621400050140741794012450002038402445542907a101140c81550b0300406400e000c030108580c0d00d40042e0511020984a1010107001000e103e40b080001c801c26000d0600741c001c0c1182403507581018070401007804400310080c8030540c0d24618003030b01403ca4141e4165501d122800500030744503079a103400180280c0201d140a83e582d441c10700e0464000050090000307d020b00a010f00105180c20840140400c0b41c0044251a051000c400100c5215041c00700d1002c0c14690101d80004403961000003c0d0081c001c00350307000b00030480010b00403d43e0b400c010b0b08141030380c81402c03c550059458200540d1444064003a071649584425650 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 712026753 1250 712025503 712025527
    0xe030909090a0b15060706090308150303270d0b0a090b0705121503100e0703020f0f0d030e061908040309060f1215050907020307060f06050607060209041e020a1d0303 73
    0x1c0311380703807009042c151030801a922035804031030011404400141c0320300300788848090000e40d01c10041004070040c2d1700d00502402840d0145031090920303a00302c0c2c44c50841c2007090792440308081c0c0b0560031580301101841e080750400000c0c41900001c90b612034441e808130740c07100c2c400d609841460300c604818076140d48525094082c0128100c601d650303d8420f070079101041c80740d9806051900e1035003031b0003485581e00b51701c10450b2181949221a008409145580c0c0740f60f524000c1e8500340d25058100b003141e4444101c003044007441600b103101040400305078110b00569001152510a80c0030381d85188000b510307000100c81b0390101030f40c041d0001f040e540c1c030b0542050705036011031309035019602548039440d41d410100d10120400c444910158102090003404c0c08078030300907500700340039181081100030304190014000c1d0042850182209501103903195081e240ca9104055183d0115407001c440300d00d04007500081c0d0321515100c400980911921155110b11071403465055500401542c1408c10342022 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 712028003 1250 712026753 712026781
    0x20f0d03090b0f06041b030b03060603061501080a0207060c0c020909060106080a0e0c03060103140601140109091a03060a15060e030a03050306150705010510150c03030e100e030909090a0b 82
    0x21075445556003001c2480300701155201407031b0300816100420103400e110105410890000e000740d020b5000b100400c400b10300101060b0803441800d003400003182c4c4600c0a81c200238060309000130300c02d80c9044050000c540d004240c40c00141d100311209211540d03508011600d911013807041c100402c5000001c104500c501c0d07004151307a52185012140d14580d1000080d00e403243c283e206840841c04410030480414041c0046405401c040b59500d5401e124000001e0185146100b00300000313546000310028120003c03415000ca050090031203141e8280026183c00078410384100e1610b40d0301e40e0500041c814010007040305440001000b42180820b2501e040c0e411758001400705074040c400f07240c100024145000644150707030040c40001103a150034040c94500c64010703007161399014850301021341000e9100d080c2d020b103907a0610f00465280c2241e400c0b03528001d6006660b00a0303a0900018810201001003d4078214008a0b11210b140c0c179412101900c9200c0001d001d03003041c100c800042c3d002c12120728 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 712029253 1250 712028003 712028011
    0x1050901090b1b0601091b180b0304060f020c010e07090905060105300c040f06240306170a05190812062413080d210209040606020f0d03090b0f 63
    0x10a18104000c10907404c202003600300a54a9a50f00d461080c51552420305002c0c00c525030030011008403603203c1c10520011144111260030f440080000c042003003c0d04800c0c2940c46140095486450b0b449509019001003013844030315100306000024049010b008141d24150000c2c0070300026401d2500f8800d0320800d2510b094000c0030000100b441002448000f080c0c1c15030b6500190420b8480c58040009440341c2d19400c80c44d841c1007010038802448241010070911580010080758100140001d8019000f0b42e401f0700f280881021200000c03200c0402c210b07000c0b5100c0c1041c0c1f00c000e02c050350030001c402c000d4400500010b505200700907181d00682000d942000000300704e840d844103c0001e07100c1481a140000c0c04a540101c0c49850010b0441b600b0400350100d070300940855600420010046610440c0c8000711112452000300302840c191304507890403101910500c071254444101a640743e1045084600c01d2041203900071425109220710171030681d1004501860b03071107100c051001980d010b4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 712030503 1250 712029253 712029277
    0x17060d0506040b1005041b050912011b031d0a1202030412210e0105090402070c0b030708070810060e0127030c08190c050909030c070803090f01050901090b 68
    0x5000a800314004024652041d8400c0f21004500e2922148404a02403036074000340c0a02d04040b0b842001028540400010f1451481c107503880300a01000600800001a4a20019440c196107001208540c5080c0320038000c0540b0103211001c950710241020f05601d00e00c0709003641014180b070300003540b204182d800c0c4104a2040ba81015101c1c0b68412003e500c0032421502000d41500044401030078510154102e0402e09012050b5481c00001074003d01c2000000f500c1203a0004102003007042000c2c0c2d900140080451407622894142400b4100e00d000380d034244040303a8980b0002d4619a003000c014002c4d075030035075509950300d54500300540d0300c440c4040b1101030240504d40348864002c1d0341441c1c03800542c01000c811512500c0d03c080241401c0c80401c070306620348200700c1903001140c54101030104035041560318006507603903005000d09600403001821080e01403503100081e113040010280c540c9a00486070089100002c0380195203d2064405190110f22815010000480260083e04150f5020 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 712031753 1250 712030503 712030519
    0xb1803032718010f140f090402010e0307080a060f06050909070506030a02040503010213090f110301140301061701090b0f040222020c010c0c060b0d021509040b040c020d020d050a1706 80
    0x1440440c2c240076040107100b142403690070450004070345a440d0010400341d80740c5412545440120301c042e5801030002e0f05004444245441e00c0d1803c11550340104a070800340c4020b0401c0d443c1080150070065200440701d4240500802d840c5001840700d0f02404481c401840024906014014590402441500c040f0b07428000054191800c0c0010708250b030142c520317103028074200040d00084425003c40d440140c0c0c034102081c50011810ba0449044d10040f03d8109004a0b10100190141149401403ca8170415000d800c0d03004205401c8581482c1c4110040386403a502d03881903820660040f0340103175108003c10384c00c04940080b044202041d1010b49800f600d00300c2030300714250954440706004000102c098208405002c0580301c0d03946002e50460360380d0a14407203500007440742440340c0c0e070801c0402c1002901400b2580ca560000e00b07040b9000c2c2081c4010150f8046c069100c0241000a40241c084c44a040804034420701c1210007468068642000c400d42c0141d00509900f4010500c2d03402c0401 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 712033003 1250 712031753 712031779
    0x803013b041b03050a170306030709090f0c0b120a020708070305030403020a02060a1d0301110f0a170114010f17130c030b090c030f01020703020c0d0317010b18030327 73
    0x48042d600051070107000201601c0d070351440c15400d150405400540c500d042030040c00990742d004200c440440303541c2480441c003110141080044007112203001001000e5040300043d6000c900380140480e0600c4009062440d91410440c5c0241d1040000040c0109020440c110000f4010800795070030501900c120380140700c0a80c0403a4190b0300025031100032402082088810840d64229000c80f01400d500038000b010200d4203800312406004000c0781d00708801702e8100c04091140c0203a6201c40c1c00b4080348203055950305960401e03101401c6c04180042c132085980c490341c601503e0024040840000d0036145640c4e046480d00c40e045290f40103e6080c4402c240c0000810003003a502400f03175aa040c060040743e10264201031500390141e403a054640d006001e004046900801c03030081c803440c10340302c240113010b09203011520380001d51090320f001d206c410000f25140f403004018000400240003000d00201046040659034001c20750307050112107040c4503003032450440e401c9903030040f440a407a00200c811 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 712034253 1250 712033003 712033043
    0x303101d10270509010209032b03110c030a030b0f09060d06110405122803050708130801090b0406180213091a0f070f030c0e04110c03070803013b04 65
    0x43d0907141c0c0d4419a402241c06105864240051107881009000414090744850802c16211800c10414000d141c0e40d20a131584111b071b05012104e0f0020070806881d80c4000c1444080d00500000c1807190050900d11000d542c0e03414002d500f64041d500c003d202d0300d40d02c40b0540ea0a00600b024844442040c41c05010004040e00d42006040b041e2440201038201c140c0d8000d101d400003130604a446280034040c4001002003600312084611603a000846a82c1e40c4000103111000552242c0c40b80ba55586410124000d001e4803d503018040d5100318018041140b100d03940700000425104040c1d480070782c0c2484031404155540c005203c01c1e00c50040c8a0204820503e4990b9802e402c4844040c0c24540700c013040b001d5a030040c82c2c03101100781400c0401503161444401015101901401401a80da4040c91400540c0303003402e507520002030a0407250303075000740c1c541020310f5042071190803c062069190981d034107c405030224050440208a030704110354900740ea802451000c1d00030344040f5006082070801345 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 712035503 1250 712034253 712034261
    0x15020408070e040605130308070c05010b0a08010c0906030213090b0307030f1506061d0d0302070b03010b041701021e070303110a0815040b030c120f0303101d1027 71
    0x2100400340303146414281321064910043c0b07030381246074034517981c20300003604507685c80d41000880c90701000209152508074010300845040c19880510b944000441d150b05410403182c40c606a40c4044c2d1050752800103902307a020b180d0f464100c14518000038410300700c40c1d1340400341307990000b4110b83c456075407034a4120000c0300300780e0195808074845c02d03500d04400281c001c8400409042c0350103004041400303840140c008010341c07480e1083c0200321004003414420000c440140c440d01101c0ca5880d65070300040c4040b5030051160b491000f0011030041034110041c42542ca401c01e48903112620f00c0f01081c04c031103c56101d40c200b1000d041c2d503244030b8606825074a0140c906810309459904207410043c1c40da14044504e041410301c91350030142c41c40300689020030340d0010410140c6040e0f002c1078000e545a410704002801a0030144004010000c503103104107a05030031240d500005c0c0780e01124850000400c9503003140d003100300c0c1c00d409404110f00c441da07110b00015440012070b02910090107000c03c60581d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 712036753 1250 712035503 712035509
    0xf120216050a0318030305070227090606030d11030d0e0a051002031009091a0a14040b0619080c0d0f0f05072301020c0405070203040e0708070f09060203071502040807 73
    0x1c0d0b4840602141010342200b43e4a074940c40c60002c903503d080c613690f030060007480380110090103055017038446000a10010015244064001c9000e18079140206405503500390498080d0f00c81c0c0704032081020030350701800c2d5002c0740481400c05907252016451059010b04072038242d501e441d2043d00c3d08540484d0060000302c000c00c4821901581c1d9044c40300000446a2594000f100c910f85441c0c6120006042c444403000f000c07a084601c03602075540c0030580c0c00140300e182614040c5420f00400c00c0304005813030343c501c0c0c80390780d04443c0c0644007121000500c10584842c045c40c0310030b900c0400c2c4c60402d403504081c200740040c403607101c3d43c20314480d43c0e40385203082c0000b0030b08071080c5d802140141f003031200803213a400b1401003075020307420307003645c0580002c2d62924006101c1c2d014030780c1c41c0040341c2079910900881d0042c1c070741c240615819082101004081140442e072040000341402904000e0721312802c003401c01c4840341e50085042c40c0c466126111003003405622139445a60805c0f0014269100b03026000007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 712038003 1250 712036753 712036763
    0x20109050307030b0f01090c050a0c02130f2921120d020d0b15040504021b1504051006060f0833011202070506041704030206070f11040603030f120216 66
    0x913505010848119149042c2c0150010340c0c2094007a00d401c0364810b0581d5035103016868990382c06001400414220302502ea130030340074141088020708650003160001540100c1b10191540c6070383c0c10081c0800d40d07124a1a18690044080d000010020030380c01081c03491212841c10b56140b904d1980b10100316a000c010080142a0081104010391a5074802e0b08260300003a604042e00c000140140c24051040c2e00a46102c0d65001c03513802c845007201d021401601103210308454000070f59411182e00d200040300c044816104035000a01c000009016040854140d611042480e41c031154080c0c0d00c0038001442102c0c0e541c16600c110b1101c2200c0b080c10110103007014286504801860001450107040e0301e0f4400d032040c01080a500040d100040280e030258210311b0440c0300c202040703880c40344d91103a680080e60200000c2402400d000d044a0b00d138101d0f80c0b061000c02200203480f4140010f40e4200d10003e004100d85104a000190123104110040311144800500c1c25100d50b0740e50b070780740690072130030b0310 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 712039253 1250 712038003 712038023
    0x5030c060f0f040b0720030c10050a2604020a1205060106050a181e06090b030610050d0e1b18040201030e030c01061401020717070b250b0a1107050a080702010905030703 74
    0x501c983d0b040f903528034003613010740161050980ca00080b83c00540c9c0e010340e100400400040c0f020a041c41030001900200c0021301d02c4011061881d1581d00c00300d03095a05038070aa42c40d9a00040d0800d103018008070301523000c0050040d980c43c1041c2a0b8554000805d07103810b10007401c1900b00700401402d0705101500d564640f9400e4164a41d880d8850468150031840a020340d007601400303901a40c0c0196640710300100d031048055032807013904662030302482004428050803d41007500b007003c04a407991007031030300100e4070039159204410407024a05070000310320382801c8000440c0155111385c0101c031f04001c2c064100d1f4a0280b441000c0c50849030203500c01280442d000200c00034642c0e051110000400c100d0700030f00f422045a981d0242c41da82c440c450301801507000a40e02d00e0220300501c6207a0980034060300a01034046500b05251212001c854215219103401041d41081c1110f10039242c0164000e0001c0150049642d81d01c61164003403601a81448100000060560750422000b0040c600ca00700442c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 712040503 1250 712039253 712039283
    0x100303020c010c0602452404031b140f06030f0a18050c040f060f060c02030703060e0606100201180b180f0d0f0807121e0f1505030c060f0f040b07 64
    0x410307410040340c1e10141c6107140079100b980d0f01e00c00800804044403210030f103421261f9020410350701c030b00e40c80141064035140e00700d1826900031f1400302c221820030300c030f0089004142c8d00304242c1c40303180c40c5420f510400910104030344020b103200700c56028501c0c1c200020b0f031618172190741503003001040003100d199100703a40329221411301c6d018900e40c80f004420244901400c160545072420050f0240700c0410809a004400350341d001c02a201c002d40d0004800c1014a44011045448680450b07082c3d0045003000081401c0605c14890720400403481c03047d0030302d14600307aa1403240b00100980320382041800f25080d0000f074001480101c80002c1c00800810740c020b43d455018020001000000381403001240802c408550003800701d400540c043c40c000101c5c00302c15070038042c4c81607040310041c840a241000c400c0288110b5840200040060b940344030b441030344c0301d00f0103950f070184142407030b040403003888400c540c81d002c04017070325140a480c50080c2c1402c0d151a034004850f0884581074600b600750900759 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 712041753 1250 712040503 712040587
    0xa0e07090f060914040b13020a0914070228050309090c071e1502031905040b091005060a050103180807081b0a12081305060c03010608100303020c010c0602 68
    0x182c0100703603050040c4507015001242008084000307201400c3d51780800c000850201500c0a0f05059550007807800300c080b900c42d00054001c0c400092000048040e01020a103002e0001803c4644084001011804c840700c0c24240c1e015000400c41c05c441500c014045284139641e00c0c21528030452074070109070f03102d002c24108000f40a1f24007442e0504492100301d07003c0403507174480768000d03900404040540d907522459a20b100d240540088282a249008144420041180f0006000e03030810021150a2607030ba5181c882140e90560301c00344d00503445402004075501a0700301d02d0b50000c0c50329401000041c035440e0365955901c0620100c414400010303440c02041050f80c0980c0700036152100902404107959204103040382090740d00030601c1803240c001542d000100880080301c40d030140070780c4c02074103240c02c40a2041d042030003048081500d4500040f491007825400004494150b40100b40c030f40c10041c010340d52765030000010b0f10350640800c2000c0c0e4098034a10600d903030180c40180c00200720a0542a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 712043003 1250 712041753 712041761
    0x10020901031b020303060d1401050f04030e1e0f01050408070f0f0f03020d021207090f09110405041e03170c090411130915170f06071b06050a0e07090f 66
    0x2a0041c0d541c0d900c1c0c0d460041580013003030301d80c0301c0026102a10103149904040d4000b62141400c510340350300300000c10008141907108240524131a4481c0d5500c8882c050802800611a00401000340000e11791201d03a880c0412101ea10711030181401d51900e51038503d40c508008035900714400380c2070422410000305008030070035402019444001c07940309040d540040c004c075060580113440742014002c0150942c50a008203030090840c40c1e01004442e005620311005048280800d96441c00414088011420a40a094450740d0300015506844a030003040e84040314028009408010046d458810345070381803074034a8041c415560744561155001d400b0081500d07101004060380761020700000c5180713007682103000c00f030311501e801c041412904450b0080c40342005501c4640d5001040003a4440010041440703991f0300c0c10001502c0e40d5598101081e16003c0e51054004001c0c180c03c907203032010800321b0344900e420007095003010440162900c0319500d070040c01d8000c00400c1381d03107a003095034a0360b080c0f113 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 712044253 1250 712043003 712043021
    0x4200f0d1b08061005090103150e0112030801150801032d080309210904020d0902101e0503010b0a0f030b0d030206090f06090a1e0611030613020309060123031002090103 74
    0x508414813091900700205107000d000f00072418141c56608404150380c0c4240407401402c5442e40f9100d0669407641b01c10070030310300c0200035000302e003003100041030203c8030418071440701e2aa80c541e2a00d0784d02e1a0750b03c02c2e00b054050b0b40200020707401c628a03480ac1070841c20440c4210300402c011034883c140004658202452408160819080914009840050359090314401402110016211203182c40d28001404d00c1c000029880503101c2442c100c61034100414446030603008003c41c252240c0580e05481d24031003030180b1032100070b0034401040050b1003032484c0343c9004490714022882c403107030743c01082c1400c3c020042100942c010f0300030003070382c1a03040100741c5840c4424001042d01d0308224034810345035598180050000c601c983d0342628101d6842d50400344c00303580110108031201e001982010950400c1d117115108098160b1410321007480c47c02501d0140c2001c00240275680d1804e101c1180e4614805004802000300d1190450030b681c09000304120400360040141c0e940c00030f00001000c84c1d0f8225 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 712045503 1250 712044253 712044259
    0x31206060a09060509030a050f060a0b1819060b070308040b090c0109051302040816030209011d0a0e120a080103021c0c030b1308071203060504200f0d1b0806 69
    0x4041d0304059a03100900208454003424a199902c010f040428184920000064254801e0000000c03503000006092440f803c0350b01d0081048640343c80c20400640c0b04140c440c0d0b40da603900c7d004540542070b0744400ad1400490b05034001103075960381d19142d4150300400c0c810713070100e0040000c01c8107004240440701d92000b242806030503269103110020b1b20b120407030b0084034040e00c0c01c280425038460b119411030780509030f10b604a504000001ca24005005e01502041b8011502d0500014406200a280001c2042160941070b041d43d40e90384507000911800c040c078611440388002c01e550341030b02d0742c008010f044d400e44c1e2111119070440c0148224285081c4070710142c566940140c402081101e09844180c0380c0c000d01c0051642c031504001f02882078844000792612100003000c02c1040851004d030000801940c4003413207075595403030400c400c0315146e909101c00c00c040b440050788292a400c0c01001a103040702456810101d050034143c00700d4801e030045651002d01c1d1804140d41c40e80000c0c40c130303901040071 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 712046753 1250 712045503 712045507
    0x50a0e0f03100b04060915091a0906450906040302280219170604021c050313080105010f151d0111060406050709120f170d0203010803120606 62
    0x300d01080d0350340b40d81640922100d54030b4007012410754907904598018030100d0803d00006060070601c0c1c04070b880d03900c59014a5450206140b09000c4918212055548018014a0995100c400340802c548800e00d080092038161070205d4450b000f060400015003181143c400351481c079000b5500308110025204c000c1c15400b5400300000294000b0380d0f017000c903035000b5402c20784401300070400c0380142464500a611051016a52601e180074501c0c2008449901a006440c0c426000015480e48416540a5007141048044508034034203800c1c000d4038184214210f03440c0080e07580c0e0914009501d6040070070f459441d80f0040000107440d070100760280c1020550000d110084060182c042100d141c41ca0001d0040900150304a078007880100e2441540c9809440c014038103031a1800043c50126007000200d2480840850b601000341101184140d1001d02c0464580840c4c03201c01140b9a03425400084180801c4800e00b00201400a1402052610015601e501c005002c00300b20751001002e0318020f03002 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 712048003 1250 712046753 712046779
    0xc0307080a08160629091902030c040f12122c04020705012c07030812060307030f0819080903030a0903030e0f061b031b1315050a0e 58
    0x404a0031a01c400d50281100380d0303410100c8000403189440c000c0240c001132078501d01050024000c91000c0e41041041d100705e907a942d001c8200125441c041c0c94003c428079028089400315007503940290340002c0c0c480319050520b41d541d10340c0390301010160040b264514050b200d00003007100f200c48403100407055060001d09101c49481d1032031180141d082c01c107211b1206aa200305561900d50494500720780201c001e20500010070501081d409400d14440c5c41c0c50300c04001000c05d1400410180141c0f9880f101c021305d0000b459689045035100a019180d050290120000000d0034080c02440d52610a001007603d90420100680f44030040500110a00095900f041404038010007203a0f400781c1291000107140001341000c030020280d5026014651040c0001c8000c01d560000b29176100f8182c2c40006216254000a100d42d41e000c02c1d01d03056482c0d40d07079a0070004950034120140060901c0280401c0549035502c4001e0140450001502d0102d2400101135100580c41098440090b5041d6110f14040403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 712049253 1250 712048003 712048019
    0x2301060e0607030c030905041a19060f050711031c0e01020118020405041106130f0b130303081e01030804080d0c0209190905070e01170601150f03020d060609080c0307 73
    0x802c03100b0042c20080744801c401c04140c0691805406031038003500412282030403040d0411701c02401002c003841089401c4007040400315503c5440d00f0b0ba5020b41c0c4e044c489810115041d02c0320717005848119408810504034180d5603d08018140e81511958204114a00050000703041c8440b01c583c00e0b0704590400055013045c03603001d038107d0206030f03041d04c00042c03070750340c5080c5156081194001140d2080001401d45035035450403003003c0907518000c0403c0000c0e955528904041d104149450080780c1e0403190400109020b568002e030b200c240b205410680c0260200d500c07900300d200760411143c000c2d0201e414403901d8010051100b02440300d04003500d032103080d40c00003502441c008108481d14540b4400054441400b904102c040380da00c0001c45d026640c94a4132031003105000d000d5902125084c0c04100f40011000034201e04036583e078510750441041880088851342c0c1c1c001485007d058080040728010442841144014441552520603003401c0585882c2805400c40132380d0700c2603201003000d012140d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 712050359 1106 712049253 712049257
    0x601060807030f09030518060702130c0c0b0408130e0621012004051c080d0b0d0f051c050f0d0b010c0b01080109061b08060909010204092301060e06 65
    0x1103e8000c1c44241d00624201a520072801c10f0020000c42f025440038803518003c0c6012100c0036a103888440c00d10406840840701400001203001c14041c44503184000b41c00e03115141c25040c01c01000041440c1c1c41601c6514491f842850f240e1440d160950049400c0316441c45601c3c0010b400f0101e0950b50b820500c18503001d40300c90380b102d200f03800c04004580c8242c1c3e40038040c1820442050303144801403e0030700310300b6000600e010944021910245002011380d01c01c10081c401940d10100d10000703150304d200b65009010052103c80780119004040d10100711024000083e00c80000e8012034404251000c007804d4851140004511110190000c40e00540a80b409000709846c84100c0c4151111069004000880c58804241903140421001d0f8000031a0000981042d4585030190101c0d9240c03c9000f1000c0641d070316801e9042c0601c12214010192418401000c448660200d4072038 = true := by decide +kernel

theorem cover : BRFrame.Cov 711870503 712050359 := by
  have h0 := BRFrame.cov_init 711870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 711870503 ≤ n) (h2 : n < 712050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
