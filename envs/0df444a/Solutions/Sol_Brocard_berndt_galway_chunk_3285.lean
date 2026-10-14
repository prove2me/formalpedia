-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3285
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:12:51.298827+00:00
-- url     : https://prove2.me/submissions/a8582d52-43a1-4641-b59b-89e2f1d0ca91

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 590647482 ≤ n < 590827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 590648732 1250 590647482 590647501
    0x506010609090b090402030d030e070e0702030a0f090b0a0f0c0c0e07030c0c1e030207151e020a0c030b060a05180727030206090a08031303050d050c060a0506030106050603090105 78
    0x403040f41c9101d51120024000140e40014203011030300024203000c00c0004041020328241211588403c4c40c0c00c444a0030400e0107680030005042d10b0042d40c8840e000c1c3c001f03c880407202c5055034010b40c111034004026511915018174841050781c20540b401070300c4401e00e82d480d503034083ea003603000c0d01d8503984030b0b428010b040d5010b000b4580240a1840d0207040d81041ea1100c0600c0001e84000d10070601401c40c0e480c003418420700c112005011015610031502ca43c2c480018400300c5008100c1008130108540000c5991010440c0016280c00c200182811421038030382a403001c9000c2c20644d0310030014000084e4640b10504003a4450042c03010302c0f44035144c450000380c0007010965001c00000d848162501d020004803200800f901c0d010744039035446030f40200118001d100395801c56005e912001c070b00c0195245400e00d201c0b0a403481401a14260034041c40c0c20b85030b40c050480c890000b071700078000240c000d8103190312182e40b054004001107020f559400208035998001e46218a080c0d4407002000081c08 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 590649982 1250 590648732 590648741
    0x10e07050405280e0304030206030f010807050a03050d08061903051f060e0109050604021c0510151709011103010303180e040804060c05011b0f0908030c1f09050601060909 75
    0x444600001002c928030b10f50010480700f00002400000d5403002c1c080a84002002070714080c6902508685d900e0402001c0100000f80901c2000e803d4401d409001c502c074100f0507212030440e58842d0003001800b1b000c20080d074010000510558009130060141d40c0c03c403904a80d1070300118000c002500c43d0b4105c01548408070303a81e04d0070701c00903181405800c2020303c81d541038550441316003c800081d151280c60008029200e15a40d6100b881102c4a40360480c41c2550320080c080e0704544213205009645010210403420b0800072040440d04180160030800e50203035060354090190400010001411a0b01c03006503002a042640083c0b40c3e1440c540300c7c600c0780e4079100003808032030985002500e05030755a40030a116600440c4100621015078804114094001c45c01c1c1c3d005c4010300464040c41030000401c8582c900c04001c0c0098112000040d80300070100c200d8400d00f8218015209403038100849024100041c01c09d9441103541b0101340c0041481802101d02030852540ca81ca031242c83c0070244410b80703 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 590651232 1250 590649982 590649991
    0xb060d020408150c040605030a02070f0c091406030717070315020910020f0a020f0621070e010e1f1101021603030e061302040b0301150308030a0c02160e0c0903010e07050405 76
    0x3e050030740c24842c04d89009810355003111181d10b0040c0c1c0c1d17542c0740d072000f4020f4011100d0040000300c90703030980302c10840401000030a850b0341000c100700020500e5400c06042500b43c801c50781507080707214103100128010707489440c0790004008a5817403955070b940d26003a104120132100740341903020444c91894038000c070002007168100d10007000704c280c480074440d440e03c400d000c000f40700700a200040f080c940c480d082612100a260305106611880c409644941c461044032028005030405e0310411043d80694007288000700094450a9120748400c840715101c10300801c21418841d1541e49030707074030b0a82400100414000b0149101c10030216107000340c19505020b0322004e20b90001400c0012030fa0480040030003040c2c0464000c5030003c092404a40100000081074840c0010083e001c400e00c03c20000031760213042c0c4543c00300001456810120b8a401d41100040d00c120681030f4204036841c124912641c2040e20148070518004213074000900319142051901c01d40e400c440d6080016140c58070889030320 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 590652482 1250 590651232 590651263
    0x605030a05060f060a03020d0c03031209080444160b120c0d020d0b0f041506050a0302390c031009060605030a2a12080d0b060d020408 59
    0x8503442903071215241e200c0200480908112400003030a195210f40400c0000e540103040303401600114105011404800e020a90104207444107810040c40030744038030002e1a41201c1000d0403e03042003007201082ca080607000c001e01d122064003114401c1c08040d4035441c03850120201c80e02451180c25282800341040280305003481d402c81c1002542101012100b515034650051030442c1d0300c01d500320089019052101160610119980d07400031025400125860380c22901d2a11144404040106464602010030a04c0d64a01c00030411036004202500048415007400750902c0e0340c0329103510762703114290307000c0e07102d51032420002d00f400724440d440d0301020071a031300501145140f68020907501e43c09032115409040c0d84818210500000340d0000b40034007002415685444010300300301180c90805414603442c0c0102c0402e40d0f12800701100d04500303c0382c5040c2d11507280000ca40b00c0440b1a04403600040301942c90308402d407820ba032607a000f0048400c0b114801610b83d810320720002d10f03010030401900d10 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 590653732 1250 590652482 590652493
    0xf1b07031b091b0f18091b080a02040308070231022a0618010e03030c09030706080601080402010c050c030d0305150406031e0c15090504050705090a0e0901110d0902010201060503 78
    0x3821684074518002d60300c83d0b81410b06901040740c03a85c030000452941701c011202e203411b050075600c4007042d0303071400d0003074441d5507041154843c968003004a10441c84010310400c0200300071070050410589421003495507505519000801400d02880d02000410545070b056000410082050400400e4060650400781c86005d0440c0e480c1843da548501070002c00c0030340e103002c2d40e500244900350000c1c03402d29011410b0b02d0b01c81c10f00807030280e500d0308855a0180b00703000b08500814050f11400d00702c2e01c106c1c0140d5441c039142c1c64580064401000301e13081130303600b800b0306540030030103031410044c4c5124000c507698000b0b00d5180156000020f150150021446682084001c0004c00c06005a101c0e40000c04a0800caa441241c0361443d02440c1c9070b80b0032003084100000e01ca0100d90000e9100c4100d4030705903000e000c541d0b02c800302182e0b00d02c20038943c03e5004007001002d000341400c40e0b0081e584407000f04000604c002c0c801c0161420b07a00110000006152103500020855a0a0003002c00904080e4010031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 590654982 1250 590653732 590653781
    0xe010516080a031d0a0b0a090c081507110d08060604150f120212241804061a01020a0f030212040f030c080d0816030b0a060309050f030f1b07031b09 65
    0x20b40340c20103640080c6c4240c2001c004500303064850b51010f1080340c1e0041081c940a0b039500711490f1103200781c03904e0001162481c00014417480c01004a4400146078a000d09074078403c06c030041d0b40202d400341c40c040e04610144001720704205400450347d940d03005601c0e800d4980c540b00000915a00b6980c045541c46801440706025622401110b642c2000d4002d4040581c40c49040100041e02e41195250b503010511001c1129003040c01545140180e00500050124000304a010070074900c10350762a600690288203c04041513040007100d108500c0303407042e1118140c0010004245810507040118030031040c0804100b000901c4a000c8001d01200c00a804401c00d0400c0107007014000806244080007010382d0b80c40700034032036400054a040000c00025803662a510001c1c01880819800c88003407007080c040c1d0681c4500003090f10a00c03140502d0305441c10080c050f00340103010700346441010610440360040000b5140000c1071208044840c09429018500b100721400d460805820400d411000300828 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 590656232 1250 590654982 590655041
    0x801051006050a17150405040818100915090306050a0b031014130507031e1103120d020708040905040602090a0b031b0a021c03020a090501110703030e010516080a03 72
    0x400140c0032051300c0d01d01c580e5205c60000910b010407000ea54005d29141c2007100f0840707941d000e803c180807502c1e00040c4510f806014004888220b204030700200b12020310811440d0030040d4450107089503494100c0761140c2e65036034503083d038000fa507000690a8070f800305038180b800c0400c400c1c0d50112041c4400e01110b011050f03c5081c48101810000c18008056106001c0c003900300018002541d012480940709803c0c19000501c42c0380368a4215040c6101e804413425510340006c0249000c802401000c0c075204580c42814000c0d4012902200c0032001440300040e204940d00c11244601d00070440941d490306c4850800282c0320494010700450b007000d2090194045d0501c006d1501004c902114035034036040c038081a45044103000c0503140701007200c1003c00c0c4403903245c1c0141000310f813543c0340e11598684500064459001d00d003007040c10307603005400800201e40300390502520401c0c10304240e80381c00b00c102010350400c0b0400d001a102e007080003030a502c1e19070b8103204032540c840ba111079042d400c10a44412 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 590657482 1250 590656232 590656247
    0x90b180a080c06010509060d050c0418140f01110301210f06092307081002031f0b031504060302030c100207051e0301061a160302160801051006050a 65
    0x2052291424414250408000c00035148001c0e04404030944078506103440c40c0e5940c500f4000d49000e13140c084089501400c1030702424600540c4400035001071004078040c000208202011146060018668440824420585d00300494590700c09004294150200c4c1420740300c124140c0101701c1000c01c010001001f06110f14050780c1d01004107907020b181241440743c8072000549018107820310b0031040804002001110350380100220a0040314141c003144442e031139143c01d11861103c1d400c004c009044842059000313550001142c0380445146052481d0246104041c0d000350510704400000d0190040c03040c40d400341c040400b184c06000f41411a40466151250201a1070091801c102c41ca58264003d00c03516010b0a0050141d210911400790800700c2d8402d6540894041d501c2c10030041030304001c0712144d6411a0601c41c0191504c01c1508852503e0120340500b98214010640d604e0110303400500500000e0003c1400807410b4180200902c070550840e40c00b0b030007030100410080048540046c0f6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 590658732 1250 590657482 590657491
    0x5060d02100e03010f0f0b040f06151103040812070b01090b0d06022802070302010905040b0d0b130203010f020307080906010810020a050d1d0d050903071502010b1f12090b 75
    0x140412540b0100700403038007412455618031030b03050502c40c070040f03044565030002c0c240c160216000e0052202c500710103001c1341c003a8019210100d56029094502c2809151441e03052051803045074070b065a034401340c5040851102d000000c210b400501d200c14480565011405080c070100f0400145a80e500010b1034581c28540c01001e80360046442c036624110048444020b100e1104020400c5020310002511000540402c85c04240810400701e030a042900c208030b43c0090140c0428041c1143d034484400500f40200860f11042a6100120040e1002c3c062524440c84540c0050703141e0420807005451810024210416036220000411400d4400128000803d0911500690302e950401044400f071241c600360422141c200000d107004128801c400c9000010b001c2d0540e8502050b0501c21034503807094404441e032603800840140a1070101c1044039285456600002a00071001c102140410300310340c800a1460703003102117034664160040391a0351103900b010301c10424120f1325500d050b103400c0041c0c03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 590659982 1250 590658732 590658737
    0x140619030902030a0b06040e01050115050c1c08040c05030c2808070315110418020d090f0f060c0f0c0b100e0c0904060603060b09150d0f0f05060d0210 66
    0x942544540340aa4080d1840c0c64024042d5560030b4201e0034002c1482070191011400340e07242200039072a1b11410700c40d040c1a500c59201c11007400444601c21101c50b00030f0001202c043c054803a00d000b100795058008a024411f40d01e440ca45031800e070402d1045516598090b50003508001030020041e69203da001210605640000c10540b44002915a41c0303802c5070071008a0784107114020042c000c0c0c4000100c1d503580003407010301902200014099882c0900c0c0f042024000d007180c001006901740f84c0140c500b01041c0300d000240c81c40d664980341d200c5070355020284c3d213100d00d0b640d100041c03203128007c190202007982404c488040b11500e000701407125100001e08003441d48400b09885018003040440140680d076000e41d05814003505548195202c0c05045100d82c2c40c0000000d511406400381600302e400c1e00b00722500700082c21090100d0610000b800c0403420030704000d01030001ca218810070071544045040002c01314060200c41045440c05014144507904048040e401691079400035510380b811031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 590661232 1250 590659982 590660017
    0x5011e030905030d020a0c02090907061b03020c0a180605011817070305060c03091902060307120f0204090204060824011101150905040b0f041e0201140c161406 70
    0xc2c20414203500500d01c004541c03a00000355840b0060380012a00d02c4103008840900560b00d42c0c0d00b86542e2060507102d130f80003007058042c401415a000c41e24000c0000d020380103030f620620f03030080080d0b403002490304520202091400d95643c00781d044d2059801034142806c0025021071450000840307031909200d2074000c00c01412a0b045411002e000041c011035118044801505250803000340c40d4004440c190410310a001d40c0c000a0f01020602a00d1103401800c200d01d1901c0320b24044600d000341e0101c0b140181d0302c456034040c410b9107902c000e1004151200c0c0060b203c50801e24020040d0300b010789400c5500b0020400c00742943c4460994200b600024244044001c2c0d5600540e030150540c0c81400c0c0c03146808610004000540740c000e54400c070310404120a8a6940170000d543c40360090303034042d0a040f4604000c1c2c5020140c0e0154600090050500303100c030307090100d0102d0044d4481c4e0440c006a030040c86402800c0080000c020018006402a110216186070b021860741c0c00307844904000b40c880d8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 590662482 1250 590661232 590661251
    0x1317120a0c050f0c03040807060c1703010b0a11012c0c0f0a0608041a2d09100509030c06090106140d08031302040b030a03080f15011d0109080318030705011e03 70
    0xc004882c0213060400c16134102c00e65480f009032458131400c2c000e8480b015000e00c032034bc03480c64000440c0d05881b030841d4100d05142020350111880c0c031401c020106103640c0e40c1008055261008812a01c1050b8803c4420b031480016100c24204040e88a40500410136025410401e90b00c1140d420265589842c00f04d203983d4403030414484030340008005102e140f020300d05011147c0d0034460200c0360320b40c440f031500076161000d84d1481241402101e203050280c10000c4010400c00e0290007c90304120a10f0480c0e0401201107203103070074407500761243d00c25a0742d01c810400440c80d0f03c1100d14601c11044414165080050320f940c50300c0e2000804a0001a102c562110304541d51a40203090040c40a01107503075800d41e0303140280c0b210310151100600740b102d500005a008450340310b15403102006a4803d40c2003c00c0d00760038400b130001c102030141408280000490483d030208050240189523240300f885032900002410709080c8950031030760412903105c850005452104003d1407109240b89000a0305484 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 590663732 1250 590662482 590662507
    0x2040e03120106020708070e2404110a0305011a0408071809081b010b04051009021c02030424060b03011503090c14040b12060403081317120a0c050f 65
    0x66070381c0003040800d0304400801d405500260100640389000e088620040e02e0342c4603001106421107078048001c801c000380c0d0300707008146d414081e5110ba0203000461003485c030b020818040e0b0403010f02c900000e0345e6800104851403031000c02c0b420703030900280c6061401f81000c015640f01d10751070156206030400141c20604481d1158400a01150405035542e290040c034031405103032050707048a2242c15030a060b0091113034506031044034020b070040c1903c4001d2a144c00c9450b0080d40001c3c808e10024145c400c4042c2c0e00307142900045100304c0c1f18000d02c1988032808030b0441d0303220354580e80c4022158a0001c061003101150000c0ba81507550120509030880ea980f00c1c1207000c3e08400c030300204840c002500004491075241d28000b4001001c440a01c0f800059000780940980c0092802401d503110340c0100c0d022034011449a42c1003220f002c0c3c140c1c0042d880d078481c0c424042e5200b001d2036464a0008041c905900c0b1020519000b014a14041c03000c1501d102005003540501d0741c484244040c00900414401c2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 590664982 1250 590663732 590663737
    0x10e01120b07170a1a1e0438130b0604050103051f0608060109062607051603020a150e1b0a17010501150c03230c06270a0f02040e03 58
    0x80f9000b82201c2c03407802409110140908600c416109040f50390300030414507085091440501c0d11a03c2e01184250003410403010301850f20310307554a8486804008070220303001804a000d501000f900e034515040c070700207110521000c0550010404d1a24504040f181da6481c2150704036030007443c0c0452503488400c040c01c0403610b0700c0425028045e5481c0d0001e415078001d0842031044d20241c8a2080d40769440d40140c032501004460b00025483e81c14540c01000d034030103032403904505071b032404608004815030b00140c0f100744a10b0a0f00941e0018442404201881c6032a55001480300010300c5402c00d1610b550303646450301c005004005891901c03801c1c5940f260b14102d00101021904030099120f040c1845000f0002030044030782e0a422410317400e10540c0075405d034840d080c0e850380c0c444018281a051a01284400d01128480d003081000403001d0305e9410841c00e0300404040e2140d82148040e010114a00c60403000c400c8200e40211118501080008100300c48041d01941c0110b1000000b1000a0035807 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 590666232 1250 590664982 590665007
    0x30308060f010e060c011b020309060304060c1809060920092b0b040506010b0c0d1803020a03060c0809010b06040303030b0a260708060f04061503050102041409010e01120b07 76
    0x18001c05c0d180036240054000740710501100d9401c1c212040040c2003217860f03108180985810903010000710b00000c4403a8490304404006103005034a04010f85c40c900c3c02c04c007071075000444440d11b900041c0156003041c401d411031807541c0052080d0001608200000a01460f0a15072003152001d02d241950070007000700d08080c48030344e1001806a1401d1400519000f41600d0036100391003030100105500c042c200489410707a60701c01c000c10380000c580204a0302c0b18690701600090300f280d40c03000001600c0304800d00002d9403040d00f01060144445900500d4040700400e032900d5070b8101f0009030b4282c0c075444c1c100c80c142ea406280104280e40c5500c0401d508507101c0d80640b000385060000a081010702d00174a401800700351341615109513803000c0701603a40340240c529840191b20348000c50300145150b0f201c0d401840101c110a44820b6030b0b6210790b0308a80081e0b01070b006800100c41191007a00d000d45200f405000800c0392100f072035040406403091160302140041c00d9154810102e84c40a01446407490038 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 590667482 1250 590666232 590666239
    0xf0a05040b0d1401060807050f0319030c02092e030209070f0507050312011503050601080c070213110c010e01090b040b060d06060303031a090402100503150904050714030304030308060f010e 83
    0x100d0030380f042c500038081c0e8841c41c440e41c01030400201c2c8a01c1d1401c0b10320303250701000b8010900c60b0521216441c000480050890900185584110041e00c8405d0b0f2a4480c0c044c0104841d894214100301d000b0351103910020342644401074000f44016a1500c8071a504908185082c00c141101d44030140c80d244034582002d04944000f003008081e05c00e0110300d50f416a03903800010000614640401d41c191082500c01c0b5003c1232483d00010314090511020b8208240010103a803100706524030710004a0305510541c0c00140c00005d00805214400d0141d07030310b0384004400030009018140c50f001c00c00180980010400e4010307801080d81c5a07a2071100721403007500104100141e555a140103001059201a460842c0310310446c05410707803074800c40351031245801405403c2c14030b000520490705c40d4030040c00c04000c183d4182d209400c079141c0c111900d02c95807141004200803800d103041d8402d05140d00410501c60341c420002440001d52000041340c01c2482501e5144926145100580e45480c0c9100348a80 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 590668732 1250 590667482 590667503
    0xb090402090727030c0f0b0403080711010323010501080106020714090903070b0c2107050a080c04080d050d05010e09030d0209010203270910080d0c050705100f030b0f0a05040b0d 78
    0x303010320810500e048a46d00380600c12102d540741c400b0080e030f0081c0c1c40302403c031801c00d01c040000702c0c070100203440d54840145400240e000040c0280c0e03680d24080102c002803001c800e8014000707075800c408400d0140c04103000500000b4500425440852490340e1558060030482010401043c410000e94403401e91250350a18a850002d00026094002c0b151422a0150b003a0280c00d240d088010300900a003510f6450a16190110740b080d184140c01400001000e1800c210000e0203c45c14042c03061454569a01c1031743d61810324281006030360043c4c01850b60201c81d507007440490100003044401848180b100540ca41452000507801d60007481088200754500200a204104602860140043c82200d5030b90007030312540109020840c5601580000b40e202038981a00d0900407a400d1210034400c0e01101c061035254804a0303400c04c60107100d1300205407800040580c06405005040c150f81c801d403038442d02c5164500000c2d00401d13491188501444d42e0700e0100c1d0040e02d070f01070001001908a41c0002 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 590669982 1250 590668732 590668739
    0x1407050d05031609060804020103020304020a1e0e0603010c1e021501170f010603020f010309050309150316030504020a05040e030c0106081f1e0e19150b090402090727 73
    0x2480340e0b1044401d0145400c0f4180400d00c400c1c0600b00d04403da449656428080756074aa00540007035101800683c0c1c0022030000010319000c1090a28040385c0b40301c100e0054180c90300c103c0f5100e400c406400c0714030030b9050a0081c0912913018440e815810340051555410a044260030390500c040840d4684d0212010300000c01c0f202d00b0400d6540900c08040700311079000c80580d00311403c981036400006d40c4094042e020f10645d40c440d1701308941041c02481038070700d4240e640c1e0000e484c4040c140c400248200340881007104c50104003da640e91106c03d410140082e03c7c040d400240040000d0041c18402d582da116204042d40041090310340f00311481008004554035540415031b0b50b1a00f41044074060b5040400c1281c2c2e200501400d81a00545004006030703200c00904000a4403407149051028800d62348450420541c01c0000300040b070142020180d030403540341101e4140c52810759107a020b1100c000501c00107840d4401099480317140c42c5448254090f0340d818891016516402517411021030381c0001c13 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 590671232 1250 590669982 590669987
    0xf05040b2d1f2d080129040807030c150207120807060c090e07050a2c1005040503070b091807090b0d14060301060b0715140412030b1905011407050d 65
    0x1102074103c506007414202c51448241c01090140a5072100000c9500004004038502249288000c41141614181c1c0301603000f46815150015485a81c065000740300c20018065a48818005091800d0780503000c3c580040c006991141c45100d44c018080400c406403042c442c0351401c0c4d4444592100d824020300245120003072400e511801080d441ca0622000700e61286d000f4422600712581d079403240c5451409044400004002100300c00c9503074021210b85000c1da9482a0400700c5480d00b5448140c0c48a040c502498070b0074034141c10100c40c000f020441d2480e40d607500310410000c520341021150042d511184202c481001a50003041d1520b80403c001d00f0107115a041100250303480c0d0254038543d0f0b00d0600b014281c40c3e1501c500038889504000b000c010039080130702d0b814095126100490028407171850720880003011601034500340620b80685040b680d150080c0221444200c5855580203101000c48030302c1e140c940705407814800498a400c11a40307000c8242d641140e00801920b40809445101 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 590672482 1250 590671232 590671247
    0x13080312070507081b060f06091e0c040b0a0f0f08040804031104060801181421250f1412030a0906060504020d0e06090d02070303030209011101060f05040b2d1f 70
    0x7c0c100c05400c010014009041c03801501d441030002d000d41c2540e0040b2040403988420010b010901e100c00100700c003188180b088001012050450360750b00e005480102c000402c0030207030702e04c2e0000b00315070101407202042c0a981500c0c1503a400070601c840045501d40011300804031603000220302d50a00c0d025441c812050346d607203103002c0d00a100c2e50440901d0680d1035a2035001c20340c0812004181c1440340310f025040c0c10050402200c8051013541075210010619000600c00c4808641ca26404406030003001082d840c078a80300140a002454580080c4c100c1005602000713003000206682c80f0100800e2188070381100b0300811010f041150741d0300c50110120090504406640c9040c4180030105501d008002602c0100e1100759000d4000315086540860195101c801500e0402040c422001e101176000e101e0540141142900034440b28603150601043c0c80712401d10780c1c800c908025015450500c0140c2404000c5c001c000700c0c404040c01c2c0000500201d00300040036845984500c420010140c000740c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 590673732 1250 590672482 590672491
    0x60d141501031d100c020f0a080912060714130306060902071a09100b0a0b0310030302060c040b0d09020418080301141f03270813080312070507081b06 66
    0xc0c244a00c4484845420f84410035942241c4203600029400400340c034590720240c0c00e1640c2d4030540718840f201811103844c000840000740c0f031645000401c0500b501c1c025504052400d100300142001c0d1814103800b92055200030700e0304088820003e104100041450160005164019000c0001640303131a8800000c0d000a00121f4040c8c0d40a03002108440c031042c0d0070380c13084c0381000003000b60140314140000a000e082814641140716410080303907102c0300c140514891007038800561006459801e000f80b0701080034110140b42074081100744510750a441c1144e0491211000128401c001480402d0040940c02e55800c04003046101a200700302c1188011412a0304242c149068030400404110703041e0342000c0c401503520328100c182003020340aa00b0810303a0303242e0f43c00007040700c4810b20101c6000b0910520116107071080055980592200040210090241c140040d070074a06890402c0304003c03c0504082e040c8000405e10000300100b00b811950070f8003110801001c00b8520620f0b040c1c0e10b60007581c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 590674982 1250 590673732 590673737
    0xe01031403030c0313020f100f03060501090617180303180f150a0b0a0e1302190803041712040902120f0408030606160f050a0311061005060d141501 65
    0x1042002141000000c2c1d82c010f00e08541610310303644824642c50701a607901da4080380c0151507000b025505664801d220140070116440300343c0701c1c4d8101c1c00002c00712501504400d0502c5410300052008542c004030808128696004840091701d8007952100c50304a1410142c03000d10001040040f42088140c0214030305040c14210f507181885611415140d00d0340750341000700c80a02d4800508405070b51b070032448014501030b103909081c03038440816040c0c54034112442010016010018801c41c101139070703241e944d1002c2c0703100d10b5000ba041010b03071038880c0322794410324041e080e001e00c107007400701428044102c614500543d410b9440e5902c80400010350007000014050b48031240000310140402d1100ea0710903588844110310355580c08003006466040030202c898654002021a0001381892140d0401c01c0e000e10002c2a00040c40c1c9001455231210306041411078101c4414801205111b65a5200340d030400c44a007500d800c0705198600003403030b002240c20b907030072900801c0c4003c080c0440640e070b014010a9 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 590676232 1250 590674982 590675003
    0x302070806070807080403050a0314040b180c10030209120304030f110906030a15020904050c04030b091903030c11010c03050603070b040b0d15050607060516170708070210060e0103 79
    0x1540680f050b000440350100801d040000040000e440388004004580b050309000132610a0b007444c1094080046400700c555906030070600c4030300700c038000110502108a8008003c4903c022020078448682c0800410a01d50046080c442d540e0301c1c0800701b101d00039203404807601c5980e43d00701100d0100708000240d900f41d0540c604040c143c2000301400f4420311b005401071040c4030842d6a4000c100440755146078540f42d0a00481c0141d51352802441c0c000e90031210210b40f6641541003240d09000051700000b200e030300c40801c8035070304410a0505111103415040010702111026000d03140290340c0f200d5420b240d40b810303820750f021540550102c1d000d82c206408036000f26446001a10f164071540c060074804020500c071242c20403900d80c000f91100140462000388040c0e4920100e800c0790801c1d401207071991349407820000703000c1c4070100700c040d0b6041c00e140410583c1c54000e0b0300c40d00d02c1d9010b400790382008a00c1d4006061180200420683c500810307208001117951030060008029080c0000c903001c0c02003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 590677482 1250 590676232 590676241
    0x2033c060f072d050c0d030204050f0d0c090e01060b19080906091b040b06070c1806030b010b0c0a0c061107051527030d09090b220b01020c09040302070806 68
    0x1508021072280c0c800c10590f50203100b01c944042c100f400303c10303205007000010040d401c6203200600c8014684692901d01588460800c000c00404200640720f8070302542c40317030031a800811300c40600b03081103606a400001e45c0c0312002c901d280c0901100d030090f03048260300245141140d1818410b10003142030075070314098961201d00d00c5c1c0b51514000d4400f10340701d07808070038503484c0130203c2008905225402000002c4000e409004110300d600320910685d00004009420815042d00c0030070100903010400c1d042001504603641d403200b10354180541c0081003804541461803280c10403516242940000b490043d09580388401403030901c041c50350a00300d014403c00050303242030001c030b8641c1410001084504054041446865458854200c041d21800685c1c07205025103051010001c3e4003060341c1d854501c181010307441c02c291110046001e010301c0003c00041400c0f10152541e010b052481c9101142c00240c01c00100d2602c0048428541c0c440170443c140020560002801011252188199103e0340d48 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 590678732 1250 590677482 590677487
    0x60c1204240305070e190e0a05071404050102070e04110a08070602120f0d0b13090605071d0901090203060a08010203010f090c0f020a021507051c0311040302033c060f07 74
    0xb1341d010000310710464807220007032418504601041c20f41a101c0440f050b610250b946110405541036461660f40703000740b204286d8052852401c8080603042c41c1d1030685440c0c0000d41e41c0349207105e51401180b019012030100441d840c000362000500818031035030240c80f20045e40d100c40c03461061801503ca40612005004070190a6a4084007844030300f070300f8000301101a001512198407010307405500d01080e480110302a11400c003426014017070003c3c251901c04405880c400400410b19000503001c02c111000f0307614038030802e06581c5400360240e00c940b920700220702120b9054102200650000c400443c0d000350410030007045800b011024080c0307291a8900fa21030340340d640007900060704140080400342c1024410640141703100c402d140e02d03243e0541c69039410100048200140c0c2c240c802c0d01c071841240d05004000c0c0d0b104244843c0d43c90503144d40d00080d514005100f003091740e08001c0c00c03c01d4111501150703d02050384020b0700402c81900381141c080c0c82f00001c5910429219480020542091 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 590679982 1250 590678732 590678741
    0x90b0711040b01020c06250b160201050c09060a0f09051201051611032b020d051b0c1009050c03030a0c0b13020d03121506020f01060801020a0c02060c12042403 70
    0x1001074042c40c031f040450101141c1080301d40401803000344030038440c10700141e10585468402c4245289440c008900100000d0030b403100036243e5500c0f0310041c00201c84c1c55640000f00c983c40715280c207005804072045041900d01c41559071007030303a01c0424000d4007002158103411091003444107214061100021140507910303410300b8949407031664414450806003501c0304103068195440400500c1222090900c2c050036644000c41400d4400d880320207124804420014079100c040d4007894180c207140c040c1c03005681d1076083c205c81e044610303160300030700b42031101c1440490040080901660b50b108151000600802203656048401d0360440d8000781c03190107804654200700d94010681c490003c190344003100c02c044080304031080903a540416512156003182104000d00894002e070480340c00f00345c0340508403201d550007207500703034010400120800d070310145800e6604c0d412038206403100300704811035140162110134500001e07800540400c2d4001da4000410000040868130030b4003108000040301502c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 590681232 1250 590679982 590680003
    0xf030e0d0215090a170c070f09090203010b040e1b011101050c0421380f07030e0c0f060a110105010b0304121d011d0a091d07030b04020d03090b0711040b0102 69
    0x217041001d802c024980410010b19004002c941100d40c01034440201e41e808141903404040c00696402e4240110f090a00a00c803881d0422103042000e12485841151a4014902c8224240301c00c3c1d03103c20581c0c0e009000e150101c2058200801c1079180611900c0c580342e001c3d020b007030702c9000072412940c0070203024072a40c840154001c003d0b0708a0150014000d005081c0d20802004094508000c4c100780307807288824601c503407045020841142040c0da005011140c5004100c0c00d5500b0003c0b60001f01d4451042d200c0000e40265245540c5207400c25003121809003d400c13624542d42043d0002401d01900d0019500580c010561124003035200c507400e072074200c4840510044090825a008180d43c014500b840c200003400908080304070800000030509203e42d00008105640e500c12110340d1130a1042190048032003800514066095480d07040c4100e40c02400288035407229607503142018401c51b010320007491400034154440c081c40c600b5541d00403400d0200c0340a07900d845400d004545c4005640b0304c04 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 590682482 1250 590681232 590681243
    0x141303020f0307200a0308070b06040f180206210702070302010e1206061302040b160b100b030c0307050706050c07410102130303111501150f030e0d0215090a 69
    0x22000304440603101c80c0f04c002c403499100e046101c000000c00c44200040c030340c882c40340000f140340785015401c00c0212102103a108070020302d0107400c0c01b59042584121500b20750100c035404c2e00d503540340032280d480c820b400d8500d0541c0814141440200317500010f006082d24401d8a510314160a40c00500140030f61004d1010015800740010138110305159000b00d1038035030882009840d02c0d40701c00407400d40350302c40e030183c8034032a140c43c40000c00d12042e160003540040d8107a110034101e601d4806540c03aa400b0103013660a03110000008107290a00542c212000158021402c0c0540e203441e015058540d08040415241b850b1f81e0441584241e00305405000f0401d0515804c103115180b640c02c601c1c0d000584200c4103c2c0e590308000285143c00c8601c0060001c6120b42d0302c51221078425180750b41008601c000c1441c43c0300284006100400202800c841200010b2034083c0314038010000817006400703a10311028072400307480110382502d5808100300440d030f44c444140f200541c46240c450b42e03440480c10000f0b4103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 590683732 1250 590682482 590682503
    0x12020d050a030b0f150a0201062102091509071e020d0f0f110f011b0e030601090905031603050c0c0d0f0803091c030b09090a02010c020402030703141303020f0307 71
    0x15064083d5110b4007041501901e01e0074071001840110b581c108490b40300700c2c03004401240c1c1c07009241e07090003204041d009040c440301c07103024a192103004407101380000a205181c0303900081d030919000349240c6000c0400912110301da0400200c0a4040e0004072414810710601c82d00031200140001081c2c60f04a60a6482e09800720340d0340030032521603010302c500301c0401104050310500c1c0003040054425002001e4000500b101d50788200c15020307066500b46001317008072a070448074148d90215407a411909103110205007150725280c01070640c8102207142e4002c4c02041c0c0b0980034554882d0242c12a200d0a804440e03030080c2d00010820003802e5220014030450043c0c40c4403000070104409183c100c01c036841286c45032841305c41d5904150255880d640e0029a55030216078440c0340803910b2076041142000500030303921013900002e08081503810003074010b1342c000012500185c407990004090a0604c4c01c24466414812030080380788c0b000050550061080d1104030401c0f01c408401c89611039405500c841 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 590684982 1250 590683732 590683747
    0x6090510050f010e12010b0109060f08190605060706050f010803041229010b0c15060609100e1809060c0c1f180501020310060801050307060e03010b04021612020d05 72
    0x1140001d6a8802d41002003013a20091940c48541000e001d1000d14800030480c0e01c0d000b000100456a15071210341000a60b40e072403005143c000301550381140300503240560380200180a000a001e065000030b820040010350001405100e40c0004d0182da0402103101440c1da1703a0884d20f980740545d0142441e80c10a000b04080001c001d2860449240c1840d0044a942c0c6000f8400070001ca1091f481907880940010381720194140c2840148211603420300c2c01c0002e82010320102d003050151100540c0680070102c0701f9155580510195040040c004010000356002d50414403000c1505481d03140040c80740201040f40302c03c081c004d82d021000c042c0c00502031451440c000d4443e81d1164200c01600c90741e6a00c03100d1108401c242c002d454140110000341e0380c0d0070844114101d400e480c2d8003840c20082d02e0340052140b99004681081100d07410b1074100695036627680064014000c9114050b07019100040c540a650302d54507048420720300501c41001c0112481d0b105a85425045004200180080000c1d1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 590686232 1250 590684982 590684989
    0x4090e071e0605070614160e0d03081302130f0e0106090c080615040513092a050d0c0905072a170c242202030717120a03020d0609051005 60
    0x20408640600c0000c19212008000300c01d00c21400c2e070300907a03a00040b0728200811030300b001c448c035200501901c82d036181e00c1303140d14001e0400c40040d20502881c42503070100300079580e4681000c071115036800c0040000d448075041400042040c0c8035019041d509040e000680e14040384a281480f4069403100e800c20f90b00c0350204108000c1c0306042c2008140e040c040420903465104104144000c1002c001610300d000e82090348102098003505030404d03406d07621a44100c0082c208050443d0700c00d540071100000146021210802c25802444402e4602000c001240c0c5d40007061f5190a508120f10814260340400e100303240305c0550340040c1070240402000410380070000c00800403002038809481146420f00d407940c2504902c0e010100c00100201c041c080d444001c0340c410140100c5a05501c6006115a40860307203a4000b4030070031a2070054031508400791b02d4248145d0350f5608100b078426176561584c0e900030740250800c00c0c500f44418980800400c81d481c2900c01c0c1c9000e84001950081002c0c03529041 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 590687482 1250 590686232 590686237
    0x6070c1202120327030d020d110109050a0c09061d010302220510081006120b040609150c1202092103040f0b0c0c030c0a060e1504090e071e0605 63
    0x226041015620300040b10b00080c4003820981640e600074482a0740d5a400c2d20140303048490f2a68842e0700000200038840e40c0015140d0400011810070440d14140c1c880c4141c010300e100c400182c5039018200101c000c0000740d0f882d8505640b900381080000948800e200d101401148408a100c84407440042c0050f00d8451111140d50605a01801c8244240b03200340e4144c1c1c3c425610090140b100e214107100304d150502c0b50446041c9582c008010261410402e07803502c50500002806101001c8045070500015400c48480203030040611080c5e80f1940b1400340c01403003009507810000781109000c02c42c03809076008a8a90b01300040c00715045400e6106450110840c0004804031743c84100000101112000d070841d009081d05105541c80c1c5608490107800e000700416628820b402c0030b21000c18a90303e9005e00000e8882c5441c2c401c0740d007080e00300804c1e6101030354408012900340c040384c0055001d400c1c0e000842100c2c0f0810582d182240d603104000302405024184201e0301c00c0c5d01b6414008584224003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 590688732 1250 590687482 590687519
    0x31602161a07080a08152704060b04050c0d060905010e071d12031c05010308250b04150b0307060207152006070215040f0201030513020901091a06070c 66
    0x800e880c2c424196240c64403948180840c5011408600070001c00e00092220003038200c0040d142c0300c52143c1652010303d510310954403484910141c160100c1c0030f020955000c2a40d150018008020a0130550030444640d007140d800001c5260400c140882c1403a901e001d074504894104203025080d4a0342001514544290f4091f80206190b486008071980c1d40c00701ca0825100145c0d0186903103513103190442807a1030041c0e1182d0440c030300342801000040d05110440d0482c0c210b84030b40440c6400d0410150b4404880100040d003440520414003082c0503072680d543c1d4180d507407500d00300040a1070300145078a030051441240c1c0940c203c3c4408120b02038054900402e030307990900d018504030200e584451000c0c03520b0110910380364010405c22824540401c03003203500e20105000c41751146442e540c4d0b44007501500600034101038450002c0303032000214904400a2950040c8402660342c4c4a444400091841c9001075950401c036000300412414408107e4101c2d0780c02c6020100140d003010550b0900b1070400c11b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 590689982 1250 590688732 590688779
    0x30f0706020c0106030803070f081b0a020a0b010306060f150f08060a0302120a050606011b060b0f130e060711030915070b041208061002060411040e0d02010203160216 73
    0x3515410080c030035134014621507424551203050024005108074124080d490038411560140310b004003446c2c5107a0b2802c0440c0e2010380e554044450220300b070500801c80100310641400000c804c20040c1d4000009407800720032004134176a507859a10701400076510256012a030b11004c1840c030180b040480d80e80c04078010b001c0d10200d0388d980d80420300b85810300203103030015001703081003c2c1080414000940c01610918000109003254070440401d0001510020155941c0e401001465100c4084501e0080b00c000d0402c0c503044c0c5040d5600d030281844844100307003406100e000600c954050303941b00d1181c010580c021400c1004103800d1144045030a88442c0c002042401880002509032212510440c403a50240034595044c035000f81103a640a403896202d00c500080a0710119400610154040c0e004281521124410804200286800c0740c6424841c092000701105103901500154082e81c0c0002c1c01d100451101c0c2c804036144c0d0140d49a181c0c88100c0420200a90110441c400d106200403c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 590691232 1250 590689982 590689987
    0x6031302040f1d03031f0510030f270c05010206070c02040b0f03010e1b0126060109030501020d090c0f12030807020f1501051804210512040308010e0903090102030f070602 75
    0x80b03d02040c00884034404086541c000403c21070207004464625210707031407102852140b00e00b40f60005400c00120b00d460810103a8515103040d00d801140c04c000c031440c07001000070303840720f0402020203c1e01c20394a5040e82d44400e160000240b075480000c40c207205603003980c1c4005001d8500d508200c007a01c1d150b902d043d0321003140e000703061031940e080c41820280c10409000700304039041001c0ca03a00d100c0100702d605050019400d103a520018a07200c0b03160a2244110250351075603140030050303401da001604042c00329840403a13a88001085580030410183c010b82c110b402059507030f19001742d07008260007180d010100d44202d2200003405800030540111660058640025207030314050702c2c0464910300c0d070064900c1c40740100454109415100c6142207040000306086c907058032803071400c01040c40903e40d4800000015040648100140c88072940c4130b4800c012607061905004001207400c2c02010300c5115031801052440f1300000c03c54403204410b8000c3d50505208004603050358001c508190781d40e076000c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 590692482 1250 590691232 590691251
    0x10806061201140f042f22150807080106051005070f151e05010305030a0503041502030a0b040c0201020703090e0603070306050a0506102a02060403020402070302070819050c12011b0203041406031302040f 89
    0x900a0701d001d1600b61003914146894443c0190ac0e111460b480111182d14000e07040c071068440300e8010000d80ca850911586d101e01502d0103038400c840158001e0a0f4043c00d01074445107a60940088031620240030811080604070400c03a41200c07000c0c070000b0196441040100e00c010f009a02860f4450b01603c0d41054072994141d180341a40e100710340403141c041e030314910340605103440c2c864051368109900c000c50800d1840d40d000391820003140180300c542e40b80344000460a60f41045440c01a41e0301c1107003408030b42050715400e03000c2c0205503100340c0b041d4003218407207280c5481160381324403041481c8210000310102d400c902641031815041642c0050041001101680b40ca0000b09010b41c4640d004040c03807441c016155092042e09400000d0310f000200401010440000da100c840310b50894040700d445805820203801049030700d05054118111440040c56030742c012019004840102c05124500010a402c015061004596002d00b454081c00000003605059018040c00280580000350320b803c0c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 590693732 1250 590692482 590692549
    0x190602040810020717181504050d08070204051e07030507020c0d0b190b0d080309030903010c090305150c0d0c0c14100b0405010806061201140f042f 65
    0x11512128110f800090360010088040000104e00d0384041781c440c2002c1014448003180d401100005104600b0b4446800c181c008404c1158020800189542542c0740b5a180084903500f107518164862031604d40000d48402d520040103280d003080080d0361401e642c3e400c80136801000d001c2e00d44400c622816445801ea9152090542c09050040349003210038900060015080d02c9208401c9807079505204c00740c2d000e6200c04039490011540200e250780c6940d0383c0e10000703145006400e1915410341c00d00c0070041c1d00d56007002c4150306490007002542d0140c03000b81144120b0300010ba54032034044c030040203620354078443ca9114401c3e6010700c0c90715002d82d040541701d4014049801c89061450740000256056000740d91180c040c828500b07450a020543c501500281c6030301e40140f1181c00380443c000340b0b0f90a1002944802080104680c0d40e4281d4100710310301100c06c0d003040f0703801c0351342039101181c130711f09100c14009111100307a4110081e18580304081c1848020340000b80b04413080d081418642032500b0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 590694982 1250 590693732 590693743
    0x20306061003060e0c1215030c0f040b060d140a020705100903170f070207050307030807030c02011110020715050f0114030f011a01020106050105030709030b040804051309031d031906020408 83
    0x5c07045401d81d40c40d14460b0059091102c0d018041020a003d8500c0c6604d06807004940e02103400002c42d1260b44017885031001c5400340610141c810b07407180000900c030219410562000c00c01c020916011403880e0346171030f105412480b8a51018040760301c0711442d4a202d44c8142c22051445100745010511088201000026024151043d0010701d0550041140c0e11b40d040040000508040b0024074140c0c0c61a10350030101d00c00d03240041c0420070b07005010020745e409811803202d29880c060031241d915488048400080d00301c81e5007154807c05540c581c6848442d24001e440c0146024901c2140c1b991070b090b500164582c122a107079405003d101528001e0031000e20840c200340074040a00c1640f0030454000900310348460f00001d0502c94144140a0700e00d41c04280301040e03a500550b00c0e00652901e052455007405a5401203501c2071b556650400c00c0c0c0c5040d00100a03540c0b0a48485045a000f010111f500e40c00d24a00d65030194400035841c110005207a4403500c00a02604005240c252108042c50500 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 590696232 1250 590694982 590694991
    0x204060b03090601030209130b0c031012080919030203030a110c060c060108061e070f0201090605391602211609020310030204200a030f0612020306061003060e 70
    0x20b0304450010000e5051203100503070f200070048c809601c0c804490b95031482800c3c014104540c003200100000b040341313082120078030161071610b501e0144484245040d44403540308064042c026000207030b4039000800400051401d070fa0b402405142421041d0701c044440d000111a02c1000b8407414150f0305c200d40314603008006003080d0700054501981001115403400b080a8222046030600351241d02032100c1006882c1d401c191103103400540a0812401280506103004000e0a290f01c0d180610010b081e00c4c10744d0810600c00700b43c07402c20500c4440044504415004060011580100300c1d900c94580c0f072144810710980300800e0000c203c10011001002106070408154065002048021404040640c040d0041c02408030551452402c040d4440a03144103110090190707454081701e804105420354240c40740a00b03500c010752216826000103001c0d0000c072044a05071490311101141050010020395025a000340c010041903d4000602441d6108164003004050f0746003004a500d41c030584030039004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 590697482 1250 590696232 590696251
    0x20c0a0b011202090c03060f1507050d050c061f091d030409090317061f212306280f031b27050916090609050906011208070204060b03 59
    0x30a0b0301481400984070001c3c00d6948440018001c0090959600040c1030060109a46000300101c80301c80d10b03000c5018650004040780600036034200c400c0c6d4080042d2044031004404c8841640340c140c0c2c50051203052040758003581111900034801003940740c00c551404103000e00308007d010403140005040da0029041220a19210b03074084051690180c00320318070000c020312025031410131030000f48080340410508406060381c90360121440740984140400d1030704680341c0b1508090030050b0f0400170042c00d00800e90064801c3e180c80394440542500d1440755002500b111610f000038205180c09044000d60308110800c3d00034081360194040550300b00661207102030094030901000040b00000554128140c40c42c4062003848403030302c0419184003c1da40307403400000c19032038001040341000202150112041d1256800290308203c690041d401c946a03040100300c42c1c1c860300440764031034400303214080d0465240c147c80c40c040b550090082c0100391004100003281030f51a80c00420941044451b13690 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 590698732 1250 590697482 590697509
    0x8091c0507082b0c1110080702070f060210090f0c08031804090503030420040c09030c06050306010518060405100e120309100e0301060b03090a0606050a18020c0a0b01 73
    0x50301c2040103c1c552804400382d4401d54148001103c0e40c01c5548019404015907541e4900070310103036140c0003646800190914184a82500b0301130001d20045e20040014030805100040302e01765140d6820540b005030b406801440400789141e00905606001034429552048800d800a80282081c00007000703840051500c8440545070203c504464904040c003c5007024800c4000510200480342e0003a03014440f070618214060b030028401e40c030303840020f0300b2502d030040c180c18131a00002200c045030300c68001d0f0041e21380c0b5210201c5043c0001e440440c0071030b10500421213030b000d0350340c00e42ca9202c00141140703003015611000100110300c3c4801c0310700031400001080d003090410503410880d600b500d0009501c0d018400300400c040c0c0010407000300c1007140358480b1680c00c4d607081d044480204045494961641040301040c1d460310003601c0c04880b5a40351200005040c188982c0c1c1804444034200040344030070003007184102952020200b010140180344c1401d00281c04c100c003841c06402000d02010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 590699982 1250 590698732 590698739
    0x130f080d061d060d0f060510050415090e0102090d0201110109080d091b060801170102120106020c190803030a0c1b0c061404030b150a030506070f090501050a0c08091c0507 75
    0xd542e00c005010540500c2001c03810b007010418400b031001c011036110500188541c3c4079102140ca94010fa04100e40c412b0800040d10190f040c01800401510614075080003001404104c0c2d40c03c1748600d0350300236000360700d001c6404003560041d49510f024584c0e80740003050460301692052000d521007908109072958a90740780301404075180310400b1001c005c64002d04030504083d0040d2035103005100c0d88052580c0e60b034110350507041c2034050b05c281500e160905119540c40d000c002c3d488180c00d9682d503002d10346441103424486464400403048840d050301071451034588516110241182076051014003030303128800e40310303540c400c05180c030603500990320804c0e01400d2180007054440c4c241c80c540e05140c414401480468441d4611030303088060704044081010400c0c02040351042c0c81c1d84080c007180903503010480e50541000c403030481c3c804644c0d0b69845950711000192914082c0513102c030002807602c041c40d80080c0c105001441c0380100107004a0440c0b8603c0c404148441994108440b00d400184081 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 590701232 1250 590699982 590700029
    0x1090b132306060309121303051606032301050906010314070905150901140a030b0907080a0510080a03030b150c010e0c0f0d110109051215060108130f080d06 69
    0x150041c000f00c42d03091440c180426031a90b03c01001740d45144011002400c0e5600000c08402c0f00021607100003940c4a408015401800d140800e2140c41c000c01d060500742002502405030f0081c41303920f4008000d030705900b8a0184a507400c802000a4180366650842d004820400c0740320a2158416580d00640c5c00c5c106028171003141e00210003031014450071b2007114210b80c0c111207070040b092802201c141d29070241c0b0f88110058584940c44641040d80302d0309000c001036000c441c8500c50200113000380b0280e1104006514403281e1885800d1903600011005400240711783c00413000340500030300d2a240a060201c6980503030703114105680702690341d144040981141070040b560410b0084410030703045001500450300411741071703000a09200d03100281040603801082104090100942203204038985140c100d075a4081c1c80e0b40b40070540d1726440001b0302941c1700307410a84c800d80060004913140d170340710740d03d1050361143d40c94129282003042c04035500d809024480c40005004070111034071b01122100303c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 590702482 1250 590701232 590701301
    0xa03061b0f0801080a08030c0f030c030a0e03040302062b0e0a0c120206030c0d1503060c0809070f0b070201050d0509070e011a0a0e0607050d03020901020d030603020901090b13 77
    0x401c800d0099440040203080c0011a50040c0c554100e800c10707036a07a5841351108028406c410b9046110b09000c024003005d00c00381400341d0722404160b1400c0111850380040d9a0f40c0780100c1c071000b54841401c200d5806602c464000103012400c0328900399006400340e201c21419507401c8a4002c4440c2d00a0401d0402e0201c45481040201807061001c1072826141d0003140d40c61000038a0f03140300080004440c050104c0b641d00c13143c502c840455a40ea11113440385002c07805848001b0303001d00080c903c03c020039020100480c40381c0c11503020000c49045c161600302c44231a581c000700000c1c0d060110030310010138485001c0c0940c921500307202025003450350800b1183c0b0342004040c0c11140c00980c0e0b030100c0c0641e2078004402c0b10070a45481c1420300c510800140000d0b0103101c1c164000f019030040312a8130280641540151000c1c800903002d5420600101c0800c03821a000c0d448060b6121203890010840004030741e000741800f440140001c05980014808041915900c61404a01180b201d1240c03e00c0d01e42e0018 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 590703732 1250 590702482 590702507
    0x70f0b07180807030201030b0604030b070504031a10051342080a1112100912210b0102011103010b04050f010e030303060405150a170f01090c140a03061b 67
    0x402107060500c200c06940e074032603000003030600d50380c2d400800450b0f8520040ea4011540031511040c18a0080d00c000c203250040c1c4402c44003400c1109200e54110840b005051082d04244c4001c0051441c0508107c0c100324182450014907680d61107401502c2d0507000c044843d0003200d260480050301e50300d0340c9008545070080005446800c11030611400401085442c1c1c0141c00c2400b10110040c0f407000a070441c00309178810701817440703141c4d9810b001e00e945411a11800e8040c0b0481e0441c00e481c0002954030b440704246100d03c0c0010a00440d00b5403000d64014400c1000c180f0000131020301c0341804031a507038002e8200f02600180440c04025620304202c804658000030b183c01c11000c803421010a69900010f44505e20650300c80c80010303c50556582c50004642c0002c1006070016034034043d0754408008003100151300d000310400001e001d0814000c54401c5903000700b40c000c0542c034020118900d014101c003903950040305001c1c00030104155000380c1c015010750a9681c0d81090020501a00a0a0440c03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 590704982 1250 590703732 590703767
    0x9030a0b10260d170a23010303020a02040c08060d032303040c030506060301090b040b280c0e09072106051302090f01090f0b0a0519020703050613110411070f0b07 71
    0x80c02c0f0244c808a00405030f0002c025902c0070910b003035025100d103490010300065107074445041000000b49035000500c0c1400c64000d99040000b1141c290044940c450b08603003203900900521300c81d10000384501e8110600c500b441026501030702c40e02400302a10b620a450070b0704c0c00780a0704400c3c000e1000900c51140c001c2c00803002041049010398034212000e0008002920f02c000c418001043c404003a00e02220842c100f032104444402030b1041c81005000c1542e000000034030322401d004daa42000c5000500078262034031001c0c8600000801c0441c1c00300e4a615686036147c5424001030a902d440d03074140101c081108016803141c00340303810b00c05a14040082c090400405c40002c1004400003090340099503150b503543ea130750b884224015521441101040c1d06c00c0800011680d65080c0d0101d2014203580c03140056a071103840741c40282c16160002d000103400c00d9018542c0e19841e1405501c04844001144046801c0c1441511040d548500400d4241d40064142d020003002940c003007410024105180c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 590706232 1250 590704982 590704997
    0xf07080c01060e071812030c020112060605031006020312040b0403090f2903040c05060c211b0a030e0f0a030f110406060306031502091810030b06040209030a0b10260d 73
    0xc6c00d0b80240520540a41408a108140e006691003103544c0030700e00301403803424081103503510300041040d44212051800f20702c2410020030b10314804000c40b00b0b0024101e204114984403500c95030800c48010340109d050003520f450024512445611420003021405441d00121b840802c40b203480040c0442c21400d420020030800c40020b00310786128007580c000341e48941c0c0320b00d200c0b503070b031403401d854407211030080c82c522203180c2814402c240090009000c01904041c1031a50400380e00c1d500c5020140040205511000c400c009040c901101307000404010701008401c1e03503945803a82c002620318015540310700e503030f440500c10303050a001e07400041040b803404110151a47e192250301080c1081c004003074640000d8001c01d00e94a040c0031508800748898113003460b04004e21074021000c0503101c00c03603140b480700000400d0351400c1d100341c45000304041d001d45a440240d6840f5141c0d032074014031540c50110341d1040420f5805910b00c4c6100901d000080006030a244c020600303290910301e070000000c01060 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 590707482 1250 590706232 590706239
    0x20a180303120e10060b0c3003060a21050d080601020a0602161a0910090b0411010201110d0e071203090b07080706051009200f07080c01060e0718 64
    0x4000e00c81c006034840c1c07000a4200d050302c0f280b4144000b030500d074841c00e0b041c0030002c50b4091000b4024100072042d18119044040014007104040c1d0840002c1d2503010b540c580c2030091145801d00950780044004c00d40140340c2d0711481594100002d040550745003a4120080b041040340070452076245441030700b4405030503e02500005d5591803a1100113100980124080300c0111120b4650030340c007980310b140990391006440c1840c1c0d034044200e07880820f91080d11780060035264140b240d50052a000703003106519590700e0311800510302c14902c20303e04565131002c2c4100003410400c05011804030050b40811050b410b000c1c0c7c24a4101183c10026030742044601a1002a40042141e0100d07201185400e0701e5880c9424110b4903070243c12009801541481d0400c421989201c0100c002c0d075913800750030480b0510303040c0140660004d1102c0360804040810040011a4200011b003d03224402c0d0402454080a511040c8c29141d941c0e2200290301441e00030701815903089036007403210700f0f8011050070f101482e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 590708732 1250 590707482 590707487
    0x306071d010e1c03030b0d060203100905090c010c1109010b0c3304021f080a0c03090b01180b0303070609050c0603040302070501050a120e0601080f150103060b1909020a180303 77
    0x410303d4101c40c40420388200404c16001e50060240074200400b402600031450810401960003112500e032400d60b03180004c15070500030300c6658003900d1120700400c03211680780e00544102c0e080401c00d0760340c002000c00c0841b0700c0d50340540c514040c100459110b62a50041c024051804d40d200302081003008038540c84030300c4440c9a00b000b03141c5c500c003802d0943d940d0b2168004103025407400803102050129030040541c2c0e264105000f113000740212a0100450341e0540002c5003161814600280044240001080004a034004000502005020001d206615603001070300c0d581c003020f011144542c0768040401400014052900a040c06840c0d452561a103176400a4854620b4005c1074107200000c10310340c2c10184a07031840d101c20f002c960300800c43d09108081c0703d940e40f0000d101e5459184242c91b241c8005600c080b60081c1608102248592a45d0135543ca60b0302400352006881d4100020070b150b00e800908030507041004101c011001a50b94502100040c5510680300c0801c449081c485d03801c00020381d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 590709982 1250 590708732 590708749
    0x11070305070807080f031005150702100e01090803120406050a02040f1815030302011505060a050406081902160c05030309010503042004151d070801150c020306071d010e 74
    0x5502c030b00e209983c0c40712071a14003000d01550340030301102c850200030028203040c0604804182d80044940f614170b500384c1803001c0554031913000e000350002540030700405214001c4040e20481981414242c0400b51580f0003070340b464000005450000001d80300741300c28020681704054111030b46101c154079003401c120b0340100e070010501c40c105410360800000b00081c01c82d50301a10204515070080503a180d03503800c0080c0a80408244400400001c540000e4a1b2410384100c44c000c4a036902c032030f41000c2c40c105d000d45d41504002c2030862004210a805101c110b2140b00802c1105440705030304040300d8450800170901d0303813103801c0140a54005c0005000581e000b80540c0e60082c0d01107101e18000c0c45040d0364000c42c1d800d210244c0c1d005420888400c910f00608250300060701d80f10394a0340701944001d000e9141000c01641c199012034180001031007040b51910502e112a440c42c10f0900300084613a0105e880c06104803a0b000004010031803220120b81f0441010b0140502440c040040080c5140001e0085 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 590711232 1250 590709982 590709997
    0x1e03030f0d0b2e030906050f0601021506130b010903062c0a0515060f03120c010b010e0f09041a070806040c020109200d06020403050a031115011512090606080111070305 74
    0x1503056181240c441c0c070a030405c2000c264071440030301c401d09280307001246501c0242c03189400750080040352075034450300d100c44900c1628000c260806469810003c11300820080e04464100a0030800103c0850717001e0084045100c441810141c60060550060400699081e0803d895400443da03903004104001014040102011101c05540c1c440034000f6915620105c44942c050180580d005d200042141c00b90602480b090006e108104035400111170100011a0240e48002c401100440c2410001030703982d8054494114a030100580010340880c49000302c40600004105104003c0d481c10280142c40000c001030000740044500c0c0e559040381c2061105144034440910646142c1d50794a4008803000282c209a04550707860b11b80c2002c9495800d059420303404201405d030601c00b410b0000800903081000c00128180c03590800c14864900c0c0700100d80d4600300308140c0c1c001d80d500452842a110700d00d200c1c400010b0014580340c0d2071400c2d5000075080580404041c060032000c01d0f00001101c80c10b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 590712482 1250 590711232 590711299
    0x41101031d0318130c0906021006030f0b0405010b060705060402010f050f030708070e1e120f070314030712081902090109260a031d030a111e03030f0d0b 67
    0x284480750f80030509140061000404050800700043c4809030041400d0081d142c0507030941d8031038890a210601502c040e40700090410603500b15010100f4848102c5d01e0b005803081001103501c808210005403140c216040544031038111106001c11980c20460002020300360b41491420101041e4456405000041c40d4105101d080740000350f80e03c2c4114060480390200906024521042c0e04c0d100c402d5a0580a00c14001c541c040211b00c20580d0010700b0b03500c01c0c00d1b10001010a0ba055980b81001000384d1450482d1a00c410720040d00010310401d034280355158990303036a0031540380410990000c400c42900d90301c051481040580841c0c0da203c12524203842d40b030414074400c00c0000c0c050070080c1d20311010704182d6003e1915010101039110f5407010002d0f41c4013045035000755841041540301c1c00d491b100141089028030380f202444c20410100b0a0020145503210340301140c1c2c102090841d4004e10701003504900c00620810003424038850100d9030752050b100301c1c000604810701311a401c0c10807809c8118 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 590713732 1250 590712482 590712517
    0xe0a0c050304030c11060c0c03010f0209150d020706050a0b190f0605090d050601120510110409180c0314011a100c051606210513080307020c0306041101031d03 70
    0x20301c8004030408011200c046c0110350790700303400d2860310344030345590b0001486942451441c41d81c0126a00a07160010402042e070b01d903603091181ca00c44158820a1500e2500d50203214403c08501903100f1144070300f8861002103581441c42c001c00840105001d50011128007556061240403000005c0c0d1082c1c501a0501a90340c0078814001400301c142c1c824020644d1292100224000b12040d21441c8040c0c8200102e41080302540c0c04d8070156116000c030444105414441042107240c5904010968904414812600d40d125102c1c07100c007501941003030b0b410031041c50142003080c03070900c0350451140c8007548807a070b181411000159a590304030303580400c10405080c01000d00070203000b400003692000b40f021034000c3e0381c1c400c060030390b0900e6221300c15180c030354030401007545403180609403003000d60035a50340034030800340e0312500303190800303404103003140f041d40400e0030b045e03e0030005e280c020350007495a41441e80001000500f550106100701d0f220540d06600050274001c008142c0d801a81c0d4203031b0110 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 590714982 1250 590713732 590713757
    0x403080f040f12030213080c030d020a11100509030307060501061803021503090102090a03030c0b0106030c050307030e1c030501090e01060b0d0b2209050f030c0c0906041d03040e0a0c05030403 84
    0x5000c1d000d110503a0903000000900003403a400002a42d02c0c220700203400f502c0c039804c212b00040e40c0b985c40202c1c0c00f50105004450b501540d03c1c1c4251400c0200846040460a007151140881d146030002c030402c441c82a6600300501000350404001c003003004881e07d000800a0540d0f020442c200c0c20f411148241c2503001c400b05408260a4044c3e468000e40500040b0702142e0303a0800804401984401383c0e280d844182c00428081c0c424082c0c100c1d025140d8443e18610344403000200c00074031100100c034400f40102d00c0a113c04210030441015448199500400c40f94100003445c41100c01800c8071b8440390b03152801c104400c1846070203491107241010b0703001034074a1030100400c01c8580031820b21250103080c80340410424840e94041e02000303019a0445d00c0500714440d03c04d07540c1c45614000c80e92035000a403d51040d11300401810340c40303107010f400032441043c111800d40c52105c95100b0341c0c6040d00040b4003848500b41e4415055032242d9404002e00c00c0500c408170243c89440040c2014080000183c000d4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 590716232 1250 590714982 590714987
    0x207080d02123708070302130b0901030e01050c18031b0112020d1b0e01081b070503090d0303060e07090b030103060506010e210705030c032518050403080f040f12 71
    0x2001072041074400644051003c01c040411824101e81c4100030600c90804039a002d8481d10a956840003d40000c0d0342c80c80c200710494a9540103c0c011904264603800406a03800342805424051445051401d45401030000404007008461790f005001f548040d81d401907081c0d003011020001072003030a244035000001d00142c0e02a11981c031183c503900381040c0114890900394408030407011440d940c1c2012410841004560704007094a044507846072040c0320038000b0b44008010980da900c1002102d01c1c140c0c440001c034a41345204002031b000300381c0e110300400c284031001c51102d50086281c50540d14080c10f02e040307221030340018080038241a41c2c0360b0024455134000d0355840c00281c00200b45d00715000c00030f00d0654050310055640501c500492200180310304000840c0c041d502001030150110700980d158924080c030001000f4522000130710000074804001c461010003414000301d02040303502d0107040140c0035620160110107040900c408010102d004514800c00d2503500c801e09003c03542039407904 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 590717482 1250 590716232 590716267
    0x5160219080d1701060e0105070b070c351309060b0306090705040f090906060e0411100c0f0f290f011703221d040c05030f34080606010207080d0212 65
    0x180156151412f110005801c50070240c1050b100700802240000601c42c01c10304002c0314010340c0c03101c0d04203420310148441644083c08252110180721000540d44240d80c0e02aa80d0b5540094030944001051208a042801c4201c1e03018085090aa00d8507107000c002e00d07846a040d22502c40096a01e01d28003080048070740040340101200c02d090a464181401c000c4001040c5421b4144202c141c84070682c41a030042d403202c0071050300510202e40c0381080351121456410440c0c011509001c01c501c1041d01d03099000300448a07100380d100a02201e190201000b48071920682224400e09001c4050304940800001100d91080881d003410304009034083c01500e044055401114a108040c9140760080c0101c03520300c4d106d28014491259100c3e40e4006141c0c4440303001c060a441a0406091034400607800600c1800c06002e0810156110503c2526075010110351341241500345c00140c1440745640c0d04221045c0a003a8240c09484007110110019541d0010424031036120742d0003007038454001044604 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 590718732 1250 590717482 590717497
    0x30307061103180c010c03050d0608010203040f0b0f1003030c1505160e090f1b0d0c03020910020609030414060910020a17090d0305160219080d1701060e0105 69
    0x400e02884a080d0401c25080e00200c80001030100c1d40446203003050300000f11402c0319075040c3c45c1c0343c4c00400d40da2000c40707496000c00b47e000d0f40240c46444c002a4008244003d61090340030710041c07004003210385002d40141c00050641c6540241c280c1c14404e100d0010842401200c1d8503003001d6500190324070b40a044000300c94100e1500c0e03494041048062008000b101051004654070901c0b40c40110041090410007940c10400030b030003000000d04045480d400700c229429091f108079003041450604c1d01d05544682022000103034021a08038150304012102841407070302400070f0a040c2c0307422881030781d0707134041ca00c00d003c0c580f60700e401910400c0c0c840d00c4c02c580d4012009021030700c0240c03c107640a5554490080c044500700b191003120714202c2d024006071124014001c140380c1110324a910100c1d0f498006200d000003a0031200000d50040c0e440d040c0f02c41c9800d4248041d842d11a01d0028090b0403c0a440040014803214182c28819444c900300034030f05640b11418900f80c0600200d0040350580200302 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 590719982 1250 590718732 590718743
    0xb040501080f0d02010501080d1b08130306050a021804020a0c0b090706110a03050904090618050607030b03010b03060406090c0e0403050904050a1118040e0a0311150601020601030b0402030307 84
    0x30421000100d040d805209900040f07030480b901e688412400c07250709202d01d9040d50455405003181900c40c07003411400c00580c1a480a9003100350302d41180a501030003084c40c8602520504004000c61402003075405181c00c0400c60510368512401c246608407240e606105541c00500c951396035008900090311541c000d08a5a130510701156956500d105074043d02e800301e4680025407910380c7c800940303100300c40d92681e106402c003e102c0041c0809460100c004640300c642381c605c0d00e4000d151503414400c09a020b50000c0159040000001e0b040303500c0d070340d001400f0343d0404030f15900300d48000030741e160410380c01540010310807000e0602e4174000314290440d1110026141c00c2c030081c564014090300d020102118100000d807a186001d10844804400850503a10140030745114140c095031211280d43c4007800c00f0420f80c0003009054200b90710040100d02041800c42002c1e107201040201d40c01010f0f6010354003196062030340001c5e560300c4051000801001e8524000b4045450a1064620f03c40d4800e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 590721232 1250 590719982 590719991
    0x60d02060f0c1501090b0d031419210b220b0312030a050c03040b01060f020c0303221202090105060a0e0a14030607090303120f18030e011106010b120a0b04 68
    0x15528544400840f50840d1080403d0070000c00e00039102d201e1b012600c1c0b8001e03c4014a585990703019607858078585001c1002120600c85000e9141d42e50f010314900041c0c5940c0d02c6a114020050411080c0f0301040012480c1c1c03401c010709180b9101d020200004050083d040c070006d5284001510140001d050710b690580116108020444040800765000f20f01c0b905040c00700d41d903000900d41c900e0000722405885820014010403005004048078201c03070400748196007961030600e0210b460b40d400210004000303232001c0ea0f031090b10804030101001424a200004240319519000030b0744403078040c05803e1040b0b200080d403200050141c003160740c1120b406070034144901d41d281d01e2945901c0690014900070b014040002d94414030404126080e00ea042c0c80c0e100800d201010008000d014013104860807996501c14481c1a132094850b40b04103a2007a81c0340c0001d41140c00c001012614068014881ca50003100103000c008090026900d5014007010086d00301d94407409094041c0c180c2664041e000382c5030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 590722482 1250 590721232 590721247
    0x2072115061703070201021e0c090115020f01020906040302040e16080d0806010e01090e130204020403120216030803060411070629011d1009080d080603100c08060d02060f 75
    0x41c0c0c00001c12a40441c91002285103009605526845600b01c02070050300301e051700c2c050001030107603184070951400048400d03243c0311401046640d002030b00711100d80d000311070004885950400007680060006030007503081ca01c40ca000b0465500407030200a110300d4454014020b60704c1c0421501403100500f01c0301205040da03070a009500c4a000d01f09500018601c0e0300041c0055005400c11200020181e54202e0303130380cac5011a1107030a03000291220302c60080c20b010070005659180007030000703103010395800404104c00c14400b034500403449030040304002e10203008002085107101940d034400c80948001c100d0302400c46006000d4850014000e0241c1e1401c10780910f100fa0040326680c0a0a25207801c160207401d4a00541b1184030501005800125080c900d81d00c1b07041010925580d08070078100901d119441e6800c0c1c82c205034003407540c80300081450003000b40c1031804100400004102c0f0b4006c221a200c440c40090014034010b104038040d910700503510701151600c50844619440101c05142c480f0701 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 590723732 1250 590722482 590722523
    0x609060d0e030a030c020d0302120619091d0618100c0320030601140301050a12020d050319020c01050a0905040b120f0a030806090903030117072304050901060501020721 74
    0x2990092038014407400101c40343c2c5038009e10841d5921380c8010007810031307135171604100000b44090500402020690360000034404545024a0080c28400e00801d041150348203085440c0c030317000401241499684030314040001901050300d00c0d114124010124054001042c00e5002d04034007500c4c0080e0b6156007504500b0700c80075501860198000740c5c1c890200361110315402029001c01e025a80e8020a069030402a646940c41c1030f0550a1019003040d0000d1415100d250a54000007000c0712611504450301c200158148040348076071000b420018109a80d01800030046a001e002c0c0324084c1d60b403414404c500340d88072119880c2020b801000c58040d941e1102201e41c80d594928401c6003c501c803100441c003180f401d0752646200d4a8220000e500316881d140960040c0c40104a11340268092900007040b119804001c49185d1040c0000e003800101c001d00c00c1c081211401000c1825603403414030709000f03913a170100d03d900442c0d85040901d0113041c21600142c1e138010340c5c5e0030018101c0141c80a292176205 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 590724982 1250 590723732 590723741
    0xc080601090e010c0806030c220212060109080109031709150103060b030706110c0d0f0b0106080411040902030606090901152903091f060308030405010f06090b0609060d0e030a03 78
    0x61001009000203080b81c0301c162016001a06c0e540c1e8503812251801c1842d050840e5046000c0b40c0303840030300c8108281d080da89000c9031700817070b018400700300d8a60030003919503001000d0f00c00420003031000f00070204090300c0062101026440100369100050007103255070b0320030020401b03281058800c13100070b56941c0c50018020b2040d0541a07009004500000461900903400305400c0d000d1800036020007589102040309074580c40b14210b84601e49101510003058410210301d02030600c50712020000c0c10b01d414010480321170540c000d44210300300910040140c0b800f10b0400d400c500107076010842510f404100034090482d40e40030b46e0003001d0200380010240c10000712050103a00c8082c6141007024841451149840102c035240d4055001101c214004011003074106418802c0c4103001405d507407241d4696806500a880944040c1e465003001084e205091080c0030007007040c40020002d40800300c2c0030a101d03000d8810f03030601c505000300d5043d0302114190000b084c900091026640c0e00c44031014050001c5c03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 590726232 1250 590724982 590725001
    0x6460905030c0f062a030703030527030d09061116020a0801020c030f03060613090c0809030a1202030924090f010507050301050607110a0b04051206010605070308040c08060109 77
    0x9108100c0c40b4022800c08220364168044050a51464040c1c0a5207501c500019a0000c1903280d020a541711416407040c0083d001c400e21a80e808074150414441080030800e80d41d6480a1101c0f0310007a201c802d0390700204031110700c0004a4045520344107030400360020032002d0403002c043c1100203a0010008905003039078684030300c2229034600c05034840001508034050303040203800c20f600c10028414040b0101001e10f920031001007000d032a00401d4000800d02d0600759002200d40e40e01e8081c40e800254204601c03542c01101403004500380421304000a058518003100ca145940d8000301003231460380e041c40355420200168044e41c0080586805404012900b01d58040b130b50b00610700d1840c1080c0041c0251406140e1603980d16003107900380810059039500c012011108079041211a40c8a03441f44400600107110a0f00480d840700e00e03100c00e00c560100100601c10306c541280e801400f915800600380da0711039815290071426035a540c0741c610f9071400503070402e441e075102e44000058040607540151000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 590727482 1250 590726232 590726239
    0xf06181406061e040906030308070f021204050d031103071a070f140307020a2a12020a09200c011b030509060f09250509010506460905 59
    0x442060400111a4203400e84250782d00500421030400300c00d80602460807240c1c800c1c000c1d40c0ca4250344940b074104071a03865000300e0101310020f0030849541c3d042a61450049514006080101d041c508110314610032402031760301c07640340300214109162140700003104004800c4210713644c98045061001550441c02d84968004040c4000a80058868061803160700c00310307156054201000c0f071600d9081d0304002c05038402c40c03013801c82040105080307038041807080c41000703440c40d0010400900381e0051080b60700118101c900840c0000016150f1407006012104566000100301c0000a81010700c0c890716040c403840008081001c0300f0080c01940085a00c0f80c8802e83d8088200ca41c0d202641960310849062f15150042c2000921102400340aa40e0000c0c12000f510266200d24100c00c20602070001c2944c080301110a06001505060307103003602500088800601780501460107004078824480000b640004068145410b420800040100b024140e103404801284071071005108003040d100c2c8511 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 590728732 1250 590727482 590727491
    0x9061e120c03242c0403051602100906080c04031703090c132a0c031220040302090703050912070503091c020907090810021608070302100f0b0d030e03010f0618 70
    0x74085028000e244609241c007200713001d940d2141c41c29159900300080c0b0f9064004071702d014900503a609140c2d5400010f00e62202140075050020040560000810b40c01c50040100401e00200300c000c2e84900041c4403668601c1da881d601c2d06422418554480101c1380c01052403c0d502c0e51703030b40068112140e00c0954000f280f1040000f03580140303c1d036401503042c1c0d0110b110400c10002091103440c05010455030081d000c5518448402c1203120081011040d250514000c1414801c501c3d0805080b60001998a014000d42c05c01034846904c03501020824003a5410008100b810058140103842c00c0b0070004181d40d50820b11480c0b06c048010403003904912039490342001900e42c0b400b41c00789a054403140402801001c0340c40c0c901e01e0017540420008502c01040f60b84103c0011a07100003490154400e9014103120f94100003004280c0d02050310b81200302c2d041404001840d00c0d00700c040c08000e6018034101c0341c0400320f203021900401c0510000c406050814a000c00c030140700c00c512080c40341c40001c0402 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 590729982 1250 590728732 590728769
    0x4050615060708031f0b03100501021b01080106081b0310080c03010903140c0139030605060d0203180105010602010b120c0a0504050606160309061e120c0324 69
    0x103a4400c07080d00800e0b4010a00201e10301c03543d401c5090040305e003040c02094449841e070030a45444c1e041103030070540380000054184100d50b0f05209410100c442014042c51150300000041c01400d414003481d81000700c1000040d103058880c51541040040c000081550384c1003540300c08a40c68442d004041343c1f481900401440741c20144104416140c00d681d488101004850084007903038022a82140c556480e0508443c440c400d42e0484680307240343c00c81001030b25030401600c10800140c681c0c64814545080d008025945070f0804607403500e0610b400060741e96844420115213072180900480d803a606c7c0c01c0c000b0409903015070005885010032100600c0383c0c0ca070b4203500c5a9402010858a410056540d810000d504044c2c01098101c50000d142030b08101c0310101241a0101c0b49000f5000200f40107010452560030500c1000740c07140e20400c03075035151100e201c06801035941910b8002d42c0ba950b03c0403080ca5a100c0e41c0200b0825011060108044d280e0a4404464007080d024520071610b01241c0d50 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 590731232 1250 590729982 590729989
    0x10317071509232d010605182208040302090a1d06060415050102070b0a110a0308010e06010503040f02010c0203071208041703090a03201c1104050c09220504050615 72
    0x9076407010004107071141c80441c1c10a04c41c0d1030801003901e00210340d00c404002c201695548046070032861000d65120040c5442c40d41c204403001e10484080c45002c50956000c04184410101d4003502d4040d54040b01075158495140000d00c0e00c007010808c92100d20030a604490310109120707025040440e010b008a0642d062241074490f40741c81000e0250b17114881c00c000c4424190094490010942440602a0260012141003408494040380000c1e2300d5001801344840c800c003d00e820150a00e0002e0440c1740542c0d0b210514805104003a042c80ba100841c20210740c0c0400100c000741107800710604200345c8500d0b11503510b4200b4090442421003100f1072036142900041a640e54460051500c02220300d140c0300c1d040340c8640a05048040d0341690a4220140c490385100d0172144904107185846000d00d050035035490a44480c81e501c2507007410144520413041d8002c0c1e420424040b80c004500c3c00c01c84411510214105489810310350800e000c00080c04000b10300b40b03204003070001040440c0045903080 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 590732482 1250 590731232 590731243
    0xa0b19090c1b053a2102160606061d06031005040c050904051f051210020301170f0703020a0527070c1a0402010801180915060f050901031707150923 65
    0x400d0003110126044040181c460080d17640c3c07034904858010507102895401c0340981c0c2c0f00c010084100d0a502d078030385082224501c00c41c00102813600d861000e450310303940002c401006401c0030500c21880880811000400d0800e60401894001d02c200400d0300440405071550300702c2a1a6072085103000000342400398010101d01c046a401e4036045440f505200c100301001c3c0b601845c1c070003284100014817000e555035100a50181c041d40c002c640c0106400c1c04d0480c0307480d15074004030441d07800403201000143c480c041403006844040310314580c920100c4c0d1030140c1400340c0e0f12021102c10442018840c1458022100f00741c510300582c514440c2c00b01603a00c0c1d01c801c03074040d03034002d000540c03800040115140382e00f5042042a0000e002041900343d0b51200040b404041210315040380d03441402700310150b443e2031141c0081c07400b030350126010f42c5103480d20340442004064650048000090100c01c1044406150030030341412042044102c65500b40501c11103900c10082c082000181295190030000190 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 590733732 1250 590732482 590732563
    0xc050918011d040503030103021c0605040804090614130b04090501090813061b0f030e06070615060f1b110915030d0e0d120203091201050a0b19090c1b05 67
    0x46155034616401c0c070642c11f1041ca45520ad41a2811740c1c200010164001caa0169004101c1d85480d0b0b400c00d4065021501c0303640c8403058510b01c0b0300010300540c940307070b400110080060000144901020020070f01500201100a00c1075203080450820000c0d0440901803800300150300288942c3c45403000d403a400c03041407441c1030362203812181100241000544000c500d109280060509101401150160300708060481da000d07110909100207401c0b02c1841e01c003e01d1149044c0c00300f0421a100602a00528520350000d44103412018050181101900415403000360540c0801c1c50700702e4524200c049501103043c4680a200081031159220ba0140b10894400900031419643e10390340d440c14180b142d0803000154042440407205599802c1c268074011410311001040500e02466924112481140aa031081c0c3c40200b8071001c0701e68095182059500e608400070300340c03040c800c0c10ba89074440b1082e0704d0302061310b804e5860200840440e084a4584206003000084da11000c0b4a410341181d154 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 590734982 1250 590733732 590733743
    0x1b030302120706110f030a0522140705030717010c080615280903030215070801060f020307021c02190315090201030b03030c06071707050d0c050918011d04 68
    0x1c500008810340080000520400340001d425a0303058881c24150040e1594407190302000c003c100726100c55000349a400818002507035101b035060798036007101d0f822800c0040c2c10642540c0c607000250000b040024040c240c018129060f030b03a03681810050b00c04000c000003015500742117a041b0304a004114042c02960024681d42690290f840c106010b5081260f40450780f031510001c29074541a4240090102a2190349d8035001d40d04505001c3c0ca4411040d184481a2828104025a00da8070940c02c60640d812803604844013500d11800f28614003c08801a5210164030001500003100c2481d103a02980709482529056011510341101100c951101030310280c00c0e103081c0350480f100e607803158800030300c14140028940d50880c0071a00c2c40c4c02410829004d41d2242061060441d0810315042d031507143c01f80c0e08041498401c0c1c0c020014042c14504400030303515a15008072080c000d0055401c0d44134007030422800d101602c002500c130640284169a110b03205010426036040300d00326818443c03600417 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 590736232 1250 590734982 590734993
    0x50a0f060e0f01051c020306040b15310e0a06050105070f030f170a0b12060405150408070f030924090e0a020c1009030e0907020d0e03070b0a05071b030302 68
    0x4402d0141d070508041906040000811500b070192014070001d00250841403070044e100d1070540144070071500310f040300714800c0c0c3c2e603418000d00b1f00540f02c00303ca048041c03094040084504100000030086d2045c059420031034007003000030a806000ca0411440342c000000d044c0701c0613959100540e11403140d844042c140c04080d134140b80c0464080c004003030b4400c28078640034450a52641c3c41c100790700001c0c0c030604045a03c0d2a034400c201e107070007400c0300c07011709656000e03110600b07007607803296912101c2c54201c0506202d0200090140400c01e020f8a052940041060b40e47c220f2501c0c00a2000803640603a82c0c03210b0320394205a8164041c200b8811b5902c0c0c0c9501e03000c02031410141344480100c8018072000d0026001c1000780441031051204800b08030640002080300c03038441c0340c09040461000c000a0041641c4010030901540c00a034640c2c281d01942855964510b10001190400300d01e90800100308070001001c182080e88100200030050048210098045400102c4540c0303000c2407101500582c001c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 590737482 1250 590736232 590736257
    0x3030b0103062d090608030c07050a0b03010e0a06030602071101351503010c020d030b0105030621010e0f0a0b010801020307141318090209090109020a060302131d01050a0f06 76
    0x282d1180081e6407040003450a0345541d03135070b09503081e02c04540003001c0700d40010840000800040065a024190407288c000ba42810200c0c0c0f80700794041445004106405a8040340d24084076a1194000e1034000300291745d55145811310900f056401d0381801e001840854641c14154151002004141a8004000e6001101c0c0301054000300b8040c0050459406c00b0042c6540e5580912070f0a0741e105a80c0c0283c407140940c0c40001d01280c1c030081a1380d0500c0b20810412440381da904804000a4600e200090200ca50f02003241e40100603400e62195140b00c3d2008a101000c000210541158800c05035608a42c5e00c0300c524078240e002c1568400c0c0402c60f1038400261032000ea001034111980500221200d4903601d910303e0a0800d80f5015900c06150f40d0400c210542c240f4042d680d0380b2100500081c014815240d0200d50200706600c00c0404142e0b000c140c850303018107048a0b485c000c24880340b0701c1c05114400011b0804101c420700c9614400d45a002000802007004410b920441d0440d84850002822 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 590738732 1250 590737482 590737529
    0x90d0906050f0a1115090715020a0206030a140f270706110a060501060314060303070302061f1706072006010515070803190f0b090408070606050d060903030b010306 72
    0x1280c100340309030b0440c500c09180c81040fa0b1400345c1810607000c3c45509110a5503407c0846642040c0542c0d0006511165010340000b8180c080c907030b05a03012030352a80c0750403603000148010005e01c8900041d03042400f056600041882d40121820f5046d10502d212168940030070100340604c03070750181c105ea0340c02c001c10b40c0600c1d0b480803180005402e0350712180480d0b03540011180241c0002002c40c0d90340f1b41100c8a0307215415001e6106105a00440c40e1060360780740a5508c00004100e064400626000411070b07175080220301000300601e5070b0350103c024001c0c60b000d40b640002c580c102c1c00940895000000c10007080c040551550070f00d0090a09a401c0c8414040800b00c0c070002c044101c0000c1150340001852080258420b600c440024104101560020030598102c00d00d80d481c490309161100009a445091280e0083c3c1d02c0b080c0b5590718541841c00402421440d40b00325400080c4042c03a00900c8020780103044891310036941002903c2c101e900650485080340108140c800340c2c505560030410 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 590739982 1250 590738732 590738737
    0x615140d050c120601090c050403030c0b150301020a030f0b0a03020d0605090c060c150705030c0406030504020d02030f03030114030304210c05120a03031a010507121106040b090d0906050f 82
    0x34040c205841d180c403000b6000c103e8021107090507400513800500104640d417103c0c8101c82a800c2d8030310340b40e840d061960b00e0061460b46a0034010f4140b0320300202060400885030781809515001900a6480303c8075030102800920029402002013420002529040d02d014884141070300d070b0003411001018420f4449000402c00100352504030b209880c1d40102656410024014040c030703140c01010100c500c80d0a0424842001d40b040b01440800e00502140310010000c0c1c1d02503030743c28540000d940d90f4600000e5880151200081c2d09400b0304180c0801c81840400214140c0e2240101105d01c400700301c00341a40d030700c2540301d16200d4201c20848503074100e030804441c1c481103000340400c10899480b500082e002e400c11107041d100d00c1c0d0054074110700b019010302802e02400c02c1c203e40182e8020b410b0001074034900c1043c2c1e008212424030780d65484140d02031044280c10440d14422580d00d40380501c1d04079003101082c1e500240358482c200f4852000340c440d005020a54000f0764640d41044035040c020010364 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 590741232 1250 590739982 590740009
    0x31b030301050d0813030204051612090203060a0b0609102d1704082b0e0106080c01081f06020d09090509100e0309060309011b170606130b03070903061514 68
    0x5021401340003015a07234034051940210b400840e00007403421403d401620041944010403106801d25403003c0c0540e07004130701907501154200010400345044400140c2ea48a29024254450040300c40310462a5100c0c0707000c8600c01101e030320040c0038980e00d0114501c0503006140400015051401ca80c0346008001d95540c00c00e10a048460801c0001800340c2c0501c145c5618030b05500e00c1c08d08401211f15036500a5500b091500c40c000c01070741d4149007845440300383c60140e09040c0300254021070311f4a042c4100a20451f00c506050700030340c43d103c0300001c2d01c0365100051100056441580460204402c0c403480e4000e406110050200300d60070b01c1910080c100c010808006030005100c252402e444d66001148140034182c000589608441c0824806070912840202003100e00c03004050a4400184945d03001307001100c80350f48540d01002d003000c20308025080780c11141c5011040c050520340022003030095a100300c07070030703c6010340c407034a0030380d045e0294841c0ea800350840c0c80d42c84585080640b03d6603a00f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 590742482 1250 590741232 590741257
    0x3080d05070e01180303120e100e0c0103060503030d0506010c05060a09170a02060a090206190503100b0702030a081606061d01171002090604030c030c0305010e0c0603220b09031b030301050d08 84
    0x924103040900d604055005046412722501e0b5102082528030a2041188007642404c00300311036400c10020998a004088440f112140c0e650080b6910f60300640d00c030520307507500404540c82031401c40e14100240c10050f4040302c0b07040c3c400001105440481c816211a21902c0e4010f04031035503421800c0002d00304550090b43c0155042119105010200380c80f0a0038139880d0b11a5a983c0c2040652583c48401551000540f004140541001680d0104000c1040e030b80000842d5152012500704201c0c4c07024100004003058070b0010001000080c40001c81c2d82280340b04041c6080c0d0b03a03034511914608105661800564114454020a0300440c0d03001d441d40700d001901c0541026100e54650031507010715001540d01c040c080c481042082000d0003140a11007000d4003419407212200045109800007501040c12a144030f02a440174002d81d0090741800c5030003990a04860904005444d1242d020825a800000014560148690000049034101d5001a146e211083d010752503d00964021400c404c01 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 590743732 1250 590742482 590742491
    0x20a0e011b0203060a0b090a0207020105090904080903010c171305120705150a0605150a0503010303110a061a03010609090804090504031205151c0218060a03080d05070e0118030312 79
    0xb50703c0801100b0b2140c0e4219000282c044d40c2401000f030034540041202240030300401038940182d90000030741c0c41d1001c0c155244c8003a41c4462070440c0550003401800ba80562030144400400d59101041d0f11034000d410b216010b013a00c800404903882c056078100079145030322140d801880b18201c40002c080e0315000d40190340d44450b0a500340e448815003600c0904900f6101c04040c4141d28107850700040940b403da80c41d41c5022060040074100340014440503003882124500010b00315414401d00c05850b074451410001c01c019004030b14110808014118000c0d8039040000c549200c2901c51803020907040700a103402c007860584140050a00240200d0400000c6200c60300380100c180210790040e6000c0240c90244030010082c0f00d203800b105803240c03a0300320802a40a01580303d1860814011245c00b25060040e96220042101c100703245d0300003849158002a10090014a0361002d030003540c031a0350f180e480c2083d45004481c00a40040200c42d07840b2080c00401c0007038018034003500702c034008400204 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 590744982 1250 590743732 590743787
    0x1e1011030903030433020c041107061517010e19051c0203071a0f04020d06021c020405040e1203071115180c030303010b04030b040f020a031b09020a0e01 67
    0x2425a08a50300c0299004035a83e60a6880401070305900710f98022045c0b103040100240d40000c0d66411b106000354000d503507500000042c5041e401c110340b11550811400e00c8161103a18442040c3e480c00e01c580404045060301503244148103024540031070b03480e10020010302c1801c19000c00b10500c2207404848a11a042c501241040b4000380c803455151180c0103152144420b0400c1e00841d03c22001c40c986401003401081500703900001d60750340050b01964034096290042c0380400c0203201d80c04030b4a8452074484241c418801483d00100256081590f0a202d17180c40b400200b5600e40c0d9403152084403900070300c0082e18543c800c40c14100e07001d4980c0c0449022070310b20705a2120f0103a058480d281c0d9290301a801064046080204409081d000c0c2d00941c510341c504801400e4170700550000800070b80c0c4801c0401c050106a81201034210380040c05030748000d40d01d01e49481c2140c1c81145a07010140c1102c0700083c000c000c7e100f0f0781c21250700ca46031100c0178040c280044821062103c400d001c07807545c80c081e50 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 590746232 1250 590744982 590744989
    0x160209040302030c10022704060918050c0d02030322051e031b1020061005100c1e03110a03081b030c0f0a2303061e10110309 55
    0x8a004a010b90060742d950948014650704281658034184800390042103556482107900c2ea030540200340111030402001e0340e22000401600b940c3c1d01070f2480c10309190f58100300075000c041c465044c5114404554506940009105903400d00200c0658181c01c00d0210040902e140f100545608944510b00068603403990700044886040b0300700c3d10780450a0101d41451800d00700650951440c03800d4000340d8181c480c000280205141507182c20030884001c5138580c010f00d9080c45c2c0e01c9220500350540e9658508100700c246124030b588030f01e0788103054011007400024050a19280455040316172066010b801140e01c114811511200301c041081c0700a044a0011003070014581c510301c01d5030350141d02c1c00e0492240803441d00078142071721640310400500c40c40708401c20440c0c1501c0c074070b00011a120390100ba4140d961110040c0403110100c0c600021a0304104090f008622400d400c50f00310340c107c2c490703040040100c00f40c01d001d00d03040404680b0312801c06000304141d840d081c0c0840226458880580c011 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 590747482 1250 590746232 590746249
    0x1b04080601080a03030e06090706030e15150a0f0602070519150c1b0602062703040b0307021b06091210020403290708070c030c0c14090c041a1602 64
    0x1060b06a0401d080e01c10030540c0c1806413005040c0f401c0b000380200d00744a8011030b01c410107449581c00b4150758403034182c3c0081050000394031900e5400401e046503d060100c0068450785806c0e2244103036848400460b26444054101003540c079a5802000c10740c6c00c10341800080c3da030001d440380310400700b0900011481c80c890b004100e12101d03644c03089003420180c5054000d150000ba00c20405850a41c4103000303580c0d00240030795004d002907480d90946500ba410f6030308001051a0152018040000e01182840100c2d0055000316855401c0394440900340f40000c08001f8000e030001d40c007420400c0b0074017061401c840c400d00484400002e0f61406e00c0d108043c442280c1c8103a004480c07207200742c98421200d40700f01ca41e40f0440019005501800d261109008001c410004d0050f41445408207926062620800e189a04c403984064010311190319003d0031100c21000d1035040340304519a40020300d201410328180e4044600f0b40100d50900c0070360801e0342d9000c2c2c210060b0030002000407a8604056a550181c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 590748732 1250 590747482 590747489
    0x6010c080309010b01030e01020309030d0216020a0b0a0e01090302060307050c0709020316080a0c081305010603241d03032202060a0e0a09060b1b03070501091112151b04080601 77
    0xd041010f13600090305a541c091a40706499105004001c03402d00b000c0101c0d07041500360000140e070b03000c0a0105040c0c00c050030f20041d401c454038410114003400031100502c100340c960348a085181d82e00d4001114002c0003804000d4002d201440401c10244c0900050304008440400703544007039440c0c800260483e0021150b1040b03001e8807072200198250400740090308500851400c4c800e5140b181c030701815020010b04407a0780348180510b0380741400401e601100145602507541202c44008c90a90980702d00c1540300c01c1803440c906001c0440c04400210b2aa0102203400301550959460168001c1d0406c5c05010701e40100d101030780c2ca40016a039610003000c2020164442003025a42032003402030803181500680212882c103002404450700300b5050790094000352031192800e20414200764154002e0ba400200b444d0300b400c0b5514200103004035128080381041d00e002501c51480c0e58016590501111001ca2441c414000304130710017165510201d2441204038003925265a804515103815800d90 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 590749982 1250 590748732 590748751
    0x1021c050a2d14040e0c04050a06020a0f020103020306010917060405070807031502030406020909041518030504030b070e090a20190804110d050f060f0f01030b06010c0803 75
    0x1d209546150000e4021040c18040512825000060b030720702d5824401c4030300041c09001001c01680060380000f41120082e140108500155080000a1140e80d030030601a052254125210211300c6a100041041500750403502c1e001c07205813181c00540c001c2d0b1000c1d00c070700e04001d9805008240804960407031890451100010302d242c0c5080d01f8114208075483d003080038581c220000c10004920401281e02e07005d10140801a600d4031a85040c100074401c258910350009071020800050282c102001e20100c0c6c0c1d2458107100700940042000350541d03091200038042001800140b001c80d0a42e1a1942e006000382401c0f84050307100740c00101401c80854203c0380c0d1503142c590200c1c11a4405150744402202ca0548908020100e44000005217100442c40704010411001805118200b100c060314904050200040c5035442c0c10440d40300d00483d403140d0014440c000c0403801125200799800c0c820220241c5003d4035900b1607070f0ba80740c22900035100a0400504105001c040b445000045021b0b06114 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 590751232 1250 590749982 590749987
    0x1b090d140c04180507150801171c020d0210050c0d0f09080f04090606090303140a02010b0a0605040501090f0e040b04060e010203150f0a03201207060c0209010e0c0d02070201021c05 79
    0x9150851804190307800030020240b0034031b001042d46070000c001d039066521800c8040e85640f1001c11952400903421440e641d00054070541080d102e80208407210520310941c02e0b1140c200d40c0496203016100240c3ea199940d22041080048101480d40724843c0b241541c800440c030450356841d1400b05800069140035041d000290400c154007152080000078409401c04003282491601d000c0c10034120011201c5001c0800035080703030b0140c800e40c40303c4d103480d0340146580720031501c41c40000c005030824010180810400000445c40440c0e540da94070131100201e10840003940d459480d020844005082111081d8581800c681400428009107200312000e8000e0201040303020104150f1072100d0305024014445140140041002c00911250303600d008410782000c0780700c43d40828001d0340164001c82980c012048082003865000995aa04074000c440c540321a0342c0341c0380d209041040566400111100411035600046403d401503c101401401512852074017004400007117078035441d00c000042d000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 590752482 1250 590751232 590751281
    0x30d03020318191e0b01060207080d0e150c030403080c061603140f061903150c02030f0a1d041d0f01020909041401110a081b090d140c04 60
    0x6039540ba090803a4540024a005141030607a0030251502020152800d0f00e5081c81c0342038000483d8036004800d43c81100040380e076a6440000351582914016056103024030103141c50300718882c1c2004c0381004401010364002c4424028000c850341d01c001c4106030f07240018480000401c40c2907002c0c2900c807814a019004500c1e18068460424500090040900d03103024440320200e041811241da0204d540165507450f5101c500009140d0009040c4100401700c41603000b00800600600c0b612901d04005020b0001c103480c0b030301c142c0e00c80c02007000c2041c040500b0300454244500c10441400c00c0d40351195a20500d400c2c1d60301040a96100009413081a002c00300c0c4001d031f4100c00c111940d4111b51000007142085050b43c00520205405040a4a43c0f040d410f4828450a420351000750090045445d20313507a00c90240c0068100f41044600595054895800008903030801086a50440c0f0040a840c21250700380c6c2c2e2103440e203030611105800e074030aa9501014a48031741c031818454000001e041c4000408 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 590753732 1250 590752482 590752501
    0x20f040c031e0b2418011b0503041403030f0a18150c050724050903190308150a06050319060e09010b040b060c071a0d0501060806130e060c0a030b030d030203 69
    0xf00090118a422030043c0341103103c004c94140c0d08036100203100200301010181c0100c40603e92005101d80c0440b4810381c5408110700040108111401d4055a0641002d24810143c40b80078000c10080b010104104c10412648031703045010008074008070650040b81c552408081c0e0b2240302003d8008114600c1404084c4032007041014000e041c441c10401800b4020700240030075080030920f00042c0040810f8605050f581844540d140c5038400c81380391030440450800405c3c1d254181e6140044180c001030841080c2030181100050b01d009032559491612080707003c01d503052240c041e0606096845401007165400388003400c0c043d4003d9000415072080300c4040001b220030021000707203c0c03c000c000c2c0d043c980d10007080010880d440040403000d5100c9c1c0e4421180c043c0f18030010003000e40c1c07070a800800c803650089604d5010f0a030030b407100d008456454800e441104e51614076008c86a01c20800a00c0340a80701c0001c08480f1a2440d0102e2820041c0010900c2d000406000b03901023600070081080359030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 590754982 1250 590753732 590753749
    0xd150e0a150506040b0f010c050312040f0209010608060607140c18010812090a030803220b0a0513051c12110d0e06040f060b060c1005041e020f040c031e0b 68
    0x1089808002c080c01c5c0c2400500030410040c2c500b810701c58810081c1d410b102d014419140c0d90802e0030360905241c5018980000004001c000032841a460b181c004203040344903480a92041c01d020340100e181c8441d948520f00881b4450030b0001c414800c10036603c9003901c5c0c40210660002c0034a10004013541020440c070b08044003000200c680300d00c24840800c482e03840c8213070181166000040d0b240d41c2d482e1950351002e4404201c07442d18045a58090b507108202030502c4c0c4c54803840f5060300c100143e8580705240f0b200c03040b05410160999011080c2003600d041e040e103940050440900304150320700c9103024590261071060034128608000440c01c000034540d0b80c0144080f107003048014181038900383e5a80240c2901519003c0c2c40543d81d0307401068280c88640460300d030550040202c40811010303038484001b40c1800c560072900d001c8840c0031508138020b4441800034450340200724884c401210001d110081c50294018002c168660b4602501fa5420000c000b0072250608008250042c00e141400000d9 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 590756232 1250 590754982 590754991
    0x9040609210305220b09011506020a060609141b16140c03030403081e040308040312030e06070c03080606090d08130806240102010605130e1b0d150e0a1505 68
    0x8948070001a041c4e00782c800503039400680c0c03102c980c403016103441c0c070500d005004442e140d0303400628a25001ca4420b4001600c0304006215000500410382c9400c40b490075104403511903c0781200620114503164090b0801041c0300e030600c15180d01340310040e22050000c200328201a01e218000307000040c0e6948060105010700402035008601d4a0324550f81d010301885400300e10b440c0781442080380d200c0007210104940041d500641c4042d03e50340c50782009441944440e941201080c54030612544902000c1030852041030580c454080714813103030b10b09441240c07004014550000c0100942405a540c145a1a03000b5000e45025034480c0c2880c111119802c106800204c0103a0011003040425504101d440a0740c50303800b003046040750f47c5440141c0c00740c002c03600702c26030040d400070703100ba404072582e030046440120380701c1220800480402082c0c0340410b0318003415040b00c1441450000f03e160b0f04403200154900300300006000c0d1080310110706204107500c003101d0101c854007a0340c540201d42e000e4203401 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 590757482 1250 590756232 590756251
    0x108010b07081b07180c02061b090d0201090810060510020303090c060c16080d0f1404210c060f08070206100e150915040c081509040609210305 63
    0xa0803426141c11030382e03005031410a14550022102c000c0248001c0c8a100000c00f074801c0407002d200005028034019202c1e001070040103104000002e002c08200d1510261503031002c42c10304c0d1900041400740320812011501c2a030512150101c00501340f8010480311050120030100000c40c10704005c01c0218548440101e0011580184280f240c2e0640111304142e958400302c170350035030741c5500c04c02460030036035550040d03402c3d8200e801c0d00180485000c140c0c3e41d90049240c2d21000b200b44140c005030707903104a03000c0350540c1010a20050041401d20000b038090180c0c103030111400c28510381d9941140d0441038002c0400142000c022400850b082020290800b03001d0001c0d001e9481c05141c105c08982907489000c1c5130b00c00300404149180d18003c40300300e20500140c01c07140c40303140800b00c00608a4042c4c41c690b009502d00304811400a00ca003221302c0c000e00141000079070828400c1c00704074680c80c1c0501700b9212246e03508100c0d000203c0306a40004140394000c41e200c1003000c420406411598010610040c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 590758732 1250 590757482 590757487
    0x3112505070b12153f01090c050609040605030703080a031407050a0f20060f1806010308090f1e090906090a020105070c0e09070e010605160237050108010b 68
    0x32420450700c820b5001240112480801060200007046580b14030b038103e105038000c101134645182042008120f01902c050600ea0450803550f03c20f003240c030010005048d0b80c0060000b800246443c400420304050000c10100303909454000007070800001c0e600854620b00c0000789042c1071707601402501401c0780400d07076100651801842c05495407180c40041c0c020000903e101e40f42c035a000d601030103c100c000b0070780f0f951a15440002590750740c206980c000540d82d0400d0004648004919881c80c59210550107030410340d195a8410744140c00c036003919540200020f032045003a449054240c3c2c400320058001c124085085010701c60b5480c005015010b46070010410021008000210750085650a1030800c0d82e0341c80e1403c204000d900705030411003d0200d85018854415000103c82007503070f04500142040d80d90390b650035161031144070400540c0500f20310100000d45070050b200c4400c441882007403100340812824501c0e18246102010002c2180c5010500c960750303000340b07241d004d030504005c120f1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 590759982 1250 590758732 590758747
    0x80403170409051f0e0a2c0f1b060c010f0c080a0b011d06090a09060b0a11070f0504020c0114091c030612060b030a080c0601090c0503040201080703112505070b 70
    0x140034400e1806458007a408017400b1880c00c910603481148405501000c1c16140c4002444080480400d090243d845100700f5410031130b40840896000e00000e40c0407401514100e0301b03800d0100c1d5030004004010513543e82c0c4407042042c60907020340c2c00600d589680e40d41d420325200344440d08950a07001950704005d540b0000c0010038090b0803031180614000c890842d10b50441800042c00c44216400501146007000000620082c10300060900d42c01c2d95210404000b00300c01807541d403080305202d00e0704607405540c4108000d042c90350081c412049641c0001c5651784103113940c20318400041d11100042d41c4a0646206041c0318900d1001c1c00204034a0309104203480e00a84041075542e40e440034103030b180d0b5466070ba28150b50030420704054907071190901e501c80c0f02c6001d0013034884809200343d1400c2424800c5000d4200d100d9811030b031103540d0513110340c40c860301e07684821002018404000d1b50030000802180c182d00c0c540b042e00c800459840c11005485086a260040c1000d2132513000c034810b1542400108c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 590761232 1250 590759982 590760031
    0x1833041211010905100506010806100e0f040603060e0d030510080c1c2415051003240b34081e04080109050f0c01170408040317040905 59
    0xc200d00420351910081c940d205060290051075460002401407080c0d0184154401260300050701c039400c03d07210514240d0315030050100f100c04082c2e2100018440d05640c00c414a410b03d070010b480301c0042d0000480c151244c1c0d0f060102d41011200d0701c900e030f004250004070070341d01d80906603000f030030703040441c81d0360f89008140c46d90380c41070b104881e00c03501c030368504c120400c081c8201065440ba08405100f515015031820460102d049040d2090310606060344806511401d1925004982018002c0852560780401c2107006242110360f5007910304a18030021940301040c44140d0207854a811031a90320071244103615000c40b40c8509821014800107920110f0101c0c00c0d08101c2c401c0c3d08070b0a26507070b800050748040c00c4c5030318040b84a01e410744003180c0400ca900341540400d10707203446003084413280d0a440031243d5840b0790791014580058582c00da81c0340303004803169803a50482d108905542c203140d00c0740d0301d515500c0c6041400c0140760074003080c2000201d155014441d0814500e200703000c0548805480c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 590762482 1250 590761232 590761253
    0x50702070f03030c0627110a0501121e0e010b04050a0506060406050706182405101e0302060a030b150a0507140a060603060b0f01090503070e183304 65
    0xc3c3c00d0081001c1154188900c9030450402079502501d491210f4032000e4a403150101c20207020707140e2561706100480740f420301c05007900030340e8016110310340f24000843c00c070070251050301c2c3d00c85410744c4900c8222510400c58011095440e00b90000400c02c4050007083c8411607000514400543d4109014454180c8880086406031111403420326902c2e01c40c1c2c245030018200320300300c5500401e10300448000f8840816a43d200782c0e007400025100c40580046881e003074403001d54031070302ca03140c11050400c030614144104801c1d0321000150507100c680c2c0ca17000a64150071a0758524080394890b91b50b260a464000030751603400c44a02091030910b1a4076a0050540c050110000e2058034580c200a9a1000070084c1c917440d240c1c000e009116080c0c4900d0503001a110221070240607221505000c0519801044c0010903104084e00a0850502e004003400c140300c00275140034450b4101c0c0c0208980c111082c05482d0aa50150180d109410f0b41d004240c03040c0a04003190046050703460b418000003444a041 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 590763732 1250 590762482 590762489
    0x1e06050a090b0307080a0b19290a030803010b031b070803060d0c0503031b07050418020906040b1201020703090501050c030327070608060a06050703050f070c120602030604050702070f 80
    0x100000c2c0040c1c110302081c6081c6a5030044842445840100000c2007241042c2c01c0c8600c00e41c1c1c010700f54004400746140181e0b07154511001e511629080d8010b0a071034102070180700110001c060500f0309a8030340360161150700a8009154160002081041c04244810900004d008441d8041d103001c401c2c1e1990491404080c20030392195000e0541e400c1071000a105490150000400740c03551411402c100c80340d001d0243e0300440d51409411300024282c505072180b00e428a002100110120b1b0059082002007800201116030081e59546c06107903a0301d43c01c0304004100000707400140e035900d07039041c05491540307190f202c1d5041000411a5140d5184c01109880c0c010a240100d81c09001c542c1c800c200301c2c100746462683d8144100140010200c0c0d1004c5035034000d40f1f064501a0015803210030403100c6119070403024000c10400c000c882445201c8030000e100c001d0194805104060301d8000581407500d03801001d030390140c1c01009003c001d1815114040e00200c0078002414143d2921a00d001500c42611 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 590764982 1250 590763732 590763749
    0x1306091809050309090703020712110a0201141201030507140616020907110f160509010e18030904110c0c01031a040222030f0b07030e031e0705010f1e06050a 69
    0x1018501000010000d0b01e0001300c0082400c6950701d440e040080081d0409502034441c40400358018281c680203504a40c1d00c00e00c0b2601401c907850f2550011b480080c820342e085150844100320814a04100032a50b0f40614822805021705614003000915445100480e591264508200103a080104290014292603040d40c05501c1c55072201c0c001e0b6912201c0c20b00c01c828a0082c00220314401902250b00400640310380082c0e000342d40c03a58284402d52109018048421200700c01042400e16010003940c9500600411240742803581400701d01950704200c81018040303404a210340520400b4402181c20039000c1c601004035420810034203543d1614090f000e802141e0000d928070b42d181006928a1148010088041000340e40b460305000c1c6070314000c0152654810038002ca54180d20a004078190694004021410204107001844208191954040d4808820400080060000c4c0207005001c00401ca000070859240c45140f4103001d0b0b0912180305d010314000044c0040c1e552441140d06480811 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 590766232 1250 590764982 590764991
    0x309090608030a11030702030a1b0e090307060b0a0f0e18030310060e010302041205030d0c0203130e1314100b0a06021b01050912060a230711030d0c030213060918 71
    0x61445d0651048900194144c0201c1c0000c00920a84840c19040e50001c1e242c2c0d0810640c0e00d40c513403000041d055136482400e4104000000c00f08840740c00a04084038014403440010f40d030341c0d00e1400414600c2e4070070090005c003581046480c801047c1303143d0041900c1d002951551501c00c005100c0c01c1840d000704010b014070b804801140764401d6058030040c041c50103001b4034102007403c1090b0b0b80c1d040340d140c41c2c99140c10038990610f40c5201105603184a001520880011130421102d174515a130b0090400c06c8542e401d031080000b00d0f1110f0800c29040c6012170290207160f100803542425190515035a0380160350000d420081142e001917040e0312200078000c01c00e013a182c9800101c400f4400e44200582c00304585861210400002c07a445021710b40760031040205024080d080c21131902440340040d10707540104000384109010b400301c90385041446054034505000080d40e90f0071240380c1d281510010764045000c40245220b101400c014107418201503664610345451420700130006909145d8407a240c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 590767482 1250 590766232 590766257
    0x6010e0112111b01060f050a0501050d09151404050d090b1c18050f1b0a050d030c12020c09010b040305070b1b0114071e02070614070b01120309090608030a 68
    0x3403425030700105500c00d1040e40c400791640e03400f40a018103008851b0341c0012070178001040d1a0140101003140c0040e15400d08201103061070000038030000000360b80c44010701c000c1d4004843d062080441e040d4040660400900702420000e02c1c0020f004510002d20114010901013078081c2d0054448030069480039160002c1c01c055170f100904130130741003070441102d4210b004041200c007142d03003600300c0507140403645d01c024140d05002e4080d504045a64211032014000e0100d800c1074160b40340e4543c0281006110b0001d65603500c40750703203000025140142c0012003043c02500d0031030122401080880d500c00d0903c0d0640d00c8041e01c44100d8817400f01c003803400154084070644104004c0050b1078800008002ca00804c0f2400451a402140c900300098680360030f1001c0300c1ea4520a403c8004060b5000340482814050182d880a940c8540381030407100500164000465800e012800713441c86101c42e240107910b03031802070040805600109007080c2420b400f8059a40000b040c0ca0516005251000c205c514 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 590768732 1250 590767482 590767511
    0x10618270c0c0345030b0a020a0903120203130f050a0608040b062403070315080a03120c030f09080711030307050c0d080705010e060402031b03030d0e01060b070302060a0506010e0112 80
    0x4016130034140341c240c02c0c00c502c65084209103210460b80a1a00c00015944441050040344610340e091008214160f80c00d0001ca10102190b04070b42c0c00a0040b00e03e8106281c2d04080740e5952a800b05c507850000340c4081c810340c100036144900410179801e209019060a07503e8589045004001e940519039000d031101e140001e03403440340b0a68401d0300c4815680d0170080801005854016011000940007aa0015171070000180d00c0402c183c06549811142d100980c2450280130780140401c205512020720dc90f10b00903d101e6140c480c0d2064458544c1c0c0c200b40d140800c1100d5824101e14802e82050120b50041032022401904150007124080d0303d084091803d01c1080c0504a0041c1a9600e010380c00c005c0c1e810001031090145008804444103a8034030391021300074201c58080c0c141c16820a00c0803c08103166500315030701100202001003511500c035240740300250004541a00180d2242050250a003c0c1e4411150084020301c0e080b5030748482d00c1d0000c0c040e400001804041241d58549051142d031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 590769982 1250 590768732 590768807
    0x40e0a021e1602010305010509062d040204091b032901120203092b0e270c120c1206060307180602160f0e010618270c0c03 54
    0x80c401d800300c0780c841d068668000c0b00c240070090704a000c64a00000030800b840c11600c0584504c400405184d15003045643c46064480c80e061211002c03280101449416555400a0009050101800030b0070041c00b90140e0800a034062803041811325000c2d50b040500340343c02680c29103100c004108200b00090f0300040b990070f0609426112201d1012091100822010440c508020f600a41100d00e4001c461221141000c1d144803c1010071001200469141400d955028280c51018043c081c614403120074080041d404452002e07aa040014203c2c4055044092654000c400740341c106003030904c1c2e41d050442e22100540314612a2402000003140c0c07d2081c120000701481c4c154488a200755644006036966030100a61244141c1a580101c0c80403403580c02d42c4120744452205100c42c1c0d1910f6001e80c0c45401c0041a00c540c58950280401e02c42c8901e0b000041c050100203a49261003203070320031401140c240c1444541081214200b5001103980702c51214401e201034480088602c901031540c50401703 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 590771232 1250 590769982 590770027
    0xc031b020a08130f1431180b0703020307020601171b1329040e0c0906030708030a020303061804030207030219050904060504030e0d150231030215040e0a02 68
    0x400480000c150f03541c00071011105400d0a444d814501d86c3c810201140840e0f004102c043d400312908411442c074481074001d030700b07000c001c0710040c2040c14031034559254a101c1198640c0100b9000402c3c401c0030350381001403074010400c0b0400860a182200061034444090300f11007001c42a42c01704500c8942d68046c03c6542074840f240f01000154010495081d0f00b60000905407010312003107c20f5400303810b06005001c07200d444080501203200c0c00404101540300c0c05840682c26219a040204d06410200020011010580c0042d034030b80c90160208440c0503102c80c0242040340090b002d01000a400050000a0300d50440b04031a0b0303500c200c0f00400440c0e20700d81c880ca501000c10750501080c017886511031801140240e8074541060800d030244181e281d4070000092814400b90201c1354603c3c51a40584003024000150421a01c140140350340d042c0303500c4042012444900f1401c01c00c42ca0020911007182d4903629189040a207884220700e0300342030051050b5005500000c4900c0c920000a402c038034207 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 590772482 1250 590771232 590771249
    0x1308030f0f0f091c020103200d09080708030708040c060c1e0201021204230907091404140103050c03010515060702060c0f010606080103060b090f0c07020f090702010c031b020a0813 79
    0x44030b03078541e04c1c1d1403520142401e9000c42e15090550051550365012380b80950941c0350490310300204110180c3c000c052b0b0380c401380c070051030600a4000013000d0100450081010703584550441c1010f00740100448095032045052148042880b4000761001d08907004414440403142420005400182e080c220704039403510b260300c000280424910024101c01d80d41c1d00e6040070781c1c0c80d00c00d20b200c01e01031001c50546004011424001d01080500400b15400781c40b80c6c80540045411001030010248010707003a0001c4a158000c95000407841c2000d00c0380c0e81d0b1101c00707492240f10400403d004502180f0a10f10064000c840c00a01003200700003c00c4000040704e900c000820410342d840c4002032220b40207000c100c45c1c150030800d0502561a090107440c2c0141a01c240800c050784407640d140000b64481c440482c6c020402a802904680c3c070200307054800c07805030b00041441500203100600b03c5180c8420020f0610040b08036105480d80014060510790740180c90325514010b154082948400030340c4014403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 590773732 1250 590772482 590772499
    0xa0c0e0415060b0c160b030609040303060e040807050c030a0308070c0602070c080c10140a051c050f091608060f0415051003060c05070f02040c0c0203121308030f0f0f09 74
    0x5900f075001c80200800c904c1e840a80e800c0518400004a55034201e100b4242c2c088000d101180251406000301c0f03802c41c0c0f0908000807200e503035040f00c3d0b16802c8120382c10382d10362402103a40010b0041c217100d00003c00c07404078064104221603075405041e142c40a06003008001c90b805494041000550456460641202300b14642c1c0b5a14002e242d590510b5805a50140c0c418410f480c01090080341690040183c0c0c82401c1e00300048508102d83c660482c0b002110540c1c95113100c0803180f9034912425004170760310003464036070b85031003480b4a2074021105410100105d460404200702272022940d250410700c0240480b050340c945050054444400540c0d80b8078151415043c42803a0403604008021a40315540600400000c80c00035611fa0140e000003814103000c0201c3c10006241950040b14031140900380348042005680100b41381000f1000b000195010028100b05544c9640190200400900740294600b402c040910002405510000c408503103002c11700c1e01610480310300f92099244086c00c40903 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 590774982 1250 590773732 590773739
    0x6190e030f0f0a1b140609131817070314030604150605091801061b140717061003150510030215030703150f140a0b030f0f090a0c0e041506 61
    0x540342c3c07062000c1101c229619030b04020340c4a0070408103004542c03a66803400035072400701c4e043c829140e100d201c0b0b26502a6104140340280403c601c1810000540e00210001c0420344c0d1030306222060040307000101425003880b903180001da01c540c0b8126505034082c0941c1d22500d13414041740c040e14819810304d54280e584580410b107254024040c060800d01201d41035001010740090124a00003802200300140100c444203441c81210741280792071920601c43d03018601c603000075403418650b0b075030008100900c11003625401550304101c42034008034000b51403030032203203103589241d00da0380700c811600e0b001615407001451107810070140303100854001d402034800d0924050001c15a174811545003004c00d25003070450525800104144040e0798205c002100702600304070001c4401c41890365103951212030001e011400400701ca02a41c011040100d0140041c1010f241c150380d041002000300300640d00034080c12002c958402d00b036804079002c0100b20209520b0b541010704020342401c114005003402c009002 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 590776232 1250 590774982 590775013
    0x21306020a0b06040b1522090c120e03030f0405100c050c19020a0504150b040f05030d17130212060c04060314010b0d24060e04060506190e030f 63
    0x284010b1207521040040d6a80c2400c0204952900d4240c40d040860402501211280407004002030f01640320900030075208100c000d40408056001400790304d403105420b00016803c84070342000c40f618040300380201001404050317034a0000800310301d80f0344581000300b1700380201031201341401c0d489104144114000800c0244c100d034007800780d00c02c0c24402d910042c1c5d0b8583c490954100e60702d60040803070b2142c0d841c0c0401c10015006040080001c6100b9480004150303855178000e00061a60000c03012401d0701e031004060901a02040c08030602c14124960f414040c50b402007140e11040244802c0102248ea00201d498441944810035562080000f480f40b03043c104030141c011a00300b9a8203218001c040c1075000c40d828820301c94903a1901c42030044a90b0070b1102c0c0c0061503241e0b00190380c010a41070317041075002d9141c4560301500204d01c910f0f115428a0031f0601960028003400c2e41c446180c0b407003280d44505024070200b21102007010040c0b01c90140c2d45c06101e8041040001c6084804003414034200 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 590777482 1250 590776232 590776243
    0xc0c030b160e040b030c0906060d0501080d140f04180f0c0c1e020609041a0619030f0b030c0123120a0606080403050d0e0a150c080106050c030403110402130602 70
    0x440340842d441c05100c00c902c0c9050300940905041c0507002e1700302031018000340126080080c10055000300140009451100b00c1c0c0b103098020301c1d089005001c034031074018000c0c200008400041c10005e40070001ba41c180043c10044804070760340e038005480d140c417040340d50300c000b800045444116103050a005806255006581301d000500078855036421a41c034080461880c5c114a80c02900400107000c090f1552400398025801c80003501d4400460740020030008406a01400384405a0398902c1440307031035030344e0510031440a02414041048030416001c0043d40e0b8102181c0300e0781c104801c065090080c46102050320107c004c5040c0116222160441280c406c60800c03901c2d641581c0c41c1c100001445480b070407403580210381540383c0c2c40c54034420318034000150951881c0c0541c0d500c5613030020800940c4030308004400790803802000a8900e128100100072501c10b030b0001040110a0182d004150004030864003140c3d0300c00b024203803001400c400304002c0c1c01504084000c2200701c03640020810b801165 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 590778732 1250 590777482 590777521
    0x60b1602010e1c08090f100807030f0b0108131a01120204050a0b0927030d1d0d0f030e0c031e1005090a021302070507170706021203070c0c030b 63
    0x2911031054480c642802240e00c50886003243c800110310700e040108141c24000c110481010b4010140c00f4403010218510808083c1444000340c01c40080210443e85442100c0105101d28002d01481001c030700024045140035085d41000da07000300120042100b0b041e9100390315070403d1000c0b08070303681d540f4105100700310804059000350b0401e03002030345c4c62030140328600300391000400c160340c0b5803110010039003c41c4c1c190711400c580c02589449806100000c10240c01342528040c4c0104800722405a410310200c490300004503a948040e02440040d600400c144414224070300d0009103036180d0681c140e24000b8ac072084290180602c00d0119102d856140300041e002000d034007120741241083c1000c0d421034000f2943c800c07154114540100c014a0803603486180f00d003007428003608255142d220b05080442a5000000c140902c8072880d203811414804100200303664009024460f111103000c000e107100061a40f0204804108043d04204002200b07501841e0001a144403d141641d0320f030b031701841e011170b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 590779982 1250 590778732 590778737
    0xe1f050d11280203040801050411040605031c03020c12030a05151005120403090b0d0501140d0c031103151501020c0604150c23011a0603010e130204060b160201 70
    0x5415510071800c0308200d9285555101d6a04900e10803814851080030080310b2580450004000c0000c80c241e09001d01ca014134003072000302e800d04000c1c008000880d04c0395405540a40c00a00d0711441d401d114665a0549050908001da43c480d410213945003002c01c0d41e00780c0c1c1081d0201005001c105149503108a214030a1040c402400703244490400c2002a80302c8001000210100a0f03512500213070380401e034100e0710905054018a84070441c820700c80c2c00802c0070003089561f403401000031007000d0b558103264003001e44e8800e0070031645407145c0b0305407211800003420007000740300007400ca5241000808003055140341014001c2c101354040c0c007199406281c80c41d0040c23050352405c00d40c5140050480d02100d145032004034030b040c004a01510f0030041d4035000d8070316103822800c40c00e440d041460400d8660341003000014045180003110040200104092405140140f005005150b2400015900980720360040e185101942c40090080d0555805c420154180481c84080ba0103186403400c50540c400d8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 590781232 1250 590779982 590779991
    0xa0510110115030807290405010221130b0408070f140d090608160c020301180303140f06130b0613050f240d0209041104170105090d0e1f050d 62
    0x504941c844002e54000a0b080940c104801000103440740703090b8018550f5008407511681400e60910001c640480f419140d0343d4000a2100d400044840007503007990300114558841d00309070341c1e40c6d41c00b90a0b040b001024640740308085000c1c00407010a880c2801c5c0e0000c0c0141c2c41c20258680358035000681b804035403035481481100700b0020700034050b01e41070b64429660b800031a55030700e0312050341200940b588024483d010208a0140c0c50a00030702c00300d0490b85566441c0030103907240003011580741c5510141c00380350701d10900483c1c041c07a000349900a00100e070b9845525450050500080c280100c00c16130140b00000c00807004054007101c40203d80c0d040354800e0306203c07041e0a00c0403d40c1c0596103091440101c4a006a1000c3c0d8400542501d141c402e400500b0010804042021030b911840302d030380403000100c0c1c1000701c03000986104490904003002406a8103104c00102da4400a0103c42c034140315500d00305d1441510355051404a640b0402001c000040e40c1d000c001c0d003981d01004c0440b0344039052 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 590782482 1250 590781232 590781251
    0x1091b180b1f1b030503070f03110a05030601051308011a040c0206040624172b120f051e10060e0d0204021e09030d030902060909060a05101101 63
    0x54400c40c56244406840c048414031928060500b450000290009101c154548110200c81440801061500c03948a01d035882c01c000d18041c200307218500c4031000f0581000108103449183e0300230707600300c10060700b007050710ba44030b400044c0c40078000c034403031408007240070a00080c4850054200c5103c0000024403900c0040306041840240c80400407084c000d6442000420000341880e4050b20351038610034101c0148050790640e0260321109940303d0000103003041c40c0070040c00c0e400c0c0300c0c0e085121004030381c0c140d61070f0075590241c04da00401040c00742408184145a00111001d810001c0001d6000c801007000e840c084484155a042c4010344d60b400028135000183c5120000f0f000c5001da5049444070f110b202c120343c0411528246043d800c903082602413000b1828a4011040000401c998100c0c1e9900c6590708401c4c5031034401509020300030035041c014028050f03100c8400301e814540b030176514420340b691f030301c000b00302014521b0740204d03082050120402c85066000d01c80e1080660501e0007130008806 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 590783732 1250 590782482 590782529
    0xa0b01060f0c15060513090210090509041407180207030807083c04050d0f1404172b030609020c0c092203050405010305070807140c01091b 61
    0x1102a41d580070404529101d0041000c60740760010401d191000400c800b500d03240412002002171031200c0a0700c0c0c0703170440c0d441146046100c0c48a1f8641602d00241c20307a2030328001030405a4080c1000e40100c00c500c03180c042d088024040500501624580340320ba003620410300c2c10003540020030a0300040e103200c01248441748101d145030f01036031280302e1a003004c0d2074600180c2c0f0302501901806094212800c114003c1514445603144a10b0244000d80701d0b0b1140300c880982020100a00101040b81c01d19003040d54151010a40e001e5941c0f00c40508550300b40c40240030302e000080500003a00c003240c4a103480c407200842071040c0810f0125501803240350354407000d0406070300030f6115902c1e1542045242c0d22040c1401030300c40c0da10a02d0b00565040c0c1048059100310000c01a03601900007810000301440b00d5601402102c2c0c00071280d2410340b1040c42c024000078500f4040741390340d2180310800112000300070360942041005541006400f8883c0200c0da8030400307080618881c01e04844070419900c800300a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 590784982 1250 590783732 590783747
    0xe06010305160e03030d0509152d07120e030a0905180a0c090f060306051e0906120102070804120c0e010b0307052a0a02190b07140312090a0b0106 64
    0x710300003011501c14000d0282a40e0080d2550f80719509440140942404001c0c41e009250060049401610b014501500441c004041c002c100a29030300b28840f4001c4511240c144003001c04075104264907850303c41c104110b0f000700e02e400e0943c11082c03d02c80c41403141d070004002042548101e45400514554400078000b0355486041c54050602c6140000340070040150402800e12605160070082e40c0d81340c00441e0301a0540b608464002981e508051019041c0707010003002904401309060988040c4d0700028181d11001080c10780901d4005219400814094055503005a405001c103600c482d200c03040b4000c1c0000125041d120141da0540c001201349019056506941c2c10000303103483e40e0b0750307083c09079516400304102410100c0200d048045143d47c0502c41c4d1828641600a44008002e50040141c1ca14040d054201c903118042c10401000c00550300b21125547d00406520021504250050640c083c032104d044ca544011010013003000f07404103801c460144a03031054904da03602c0d035008841c004c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 590786232 1250 590784982 590784991
    0x818070501141b0d02030a020712080a1101110a021b15030a0b0612131b060207060c0c050a08070614180f030a0606091505040b0907120902030d08010e06010305 70
    0x18000315801c2d418800284010900030806043d040300c544910b41400d441c100000d085600140c00108000d80ca0503818032055008284032140c100302515a6200d0324124440d0581e15414002e04542100d2800f030b0079004400b10391034191050751141c07c1250041c1d150710303000c69401056500388010b03a44500c0c01c0309080c410105240380306400c42d03807400c00440c014002800155031118080c0240d03102c0c00d25442810384510b00840c0c1e0205092280d25081c2543e25545080d2a40c000100744288a241d0740006e0302011144945403161080e00c050504032888010b58000c00d0b040b003980c04010030020800202101200c0c41d82c1d403910250f400b9200ca0f01c6090040d245c080d01c1c0f400781505a40440d1505406000c8884801011786a83c40c0496940c941150041e41c80082c2240d115802e848510f40c060081600525081d201408201008030001d9540d4000610140a01854070040341000320564009003105134040e040700d002074010702000d00068024481c51001e5103031720b800903003254400d001d8540103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 590787482 1250 590786232 590786237
    0x801290f040f1a030d0921080d0c030e0703020102061302040b030d0306051e090c07031e03151e0306051008030c151e04080c0f070f050f0108040c0e0408190818070501 73
    0x31b035401d0250384d4070700c2e000c144001c9107085102c1c007041000c076200d240204400c120b403510010704c0740d00c401d00c0502540d80c1500c3c50304042e00418010000360340c000c2215035003c2c900016029103e03000c0c0c800a0000d01c00300c5440c0d50544603800e07c8002d8035400d90f000000740c800840e19070f01682032242c07040c01200301000fa0550400325440100701419003081c080c1590078447c2c100712005104980c0350802e5012021184000691940f90001c0880c0c007003400503010340f030b095268041c40b0099002c007203628100f40c4401410075595100186c01c0003507000c0104060141c24065039501c0842c4c1d80180e5590901100c042c40c1040003070081030400c0071074284440541d100d000c086da01c81c4d80b551100f11017a0021a280c02e00c600615040b900c52140c00d115100281515003918988141004184802e01700c4e01e0a0103070620080300700f408040303501d540307a90b001c0303440c0b030300209681d5500da00e041b0419014800032208001c070611589000c868025000500c00c01c1161500c030071422004100b0380c0c0c0d1345011303c9501d02 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 590788732 1250 590787482 590787497
    0x9050a022a1e0c0f01120906050f060103060b030105060a0e090405060604050c040e13060b030d050c060a0c050d0c050f270306011a1305030601030804030506010801290f040f1a030d 79
    0x141d90600c0c84e411050f584050401c019040a600f404006440e46c8100480c0e02a642d0010001c0d0007800c654107941040b800c1c03908011040c01d000500c00d0300d20060251074071444011400035241c900c55000400c40e108094190800ca061030315010ba0307100c900f600d119219a0510002a42c0b040b0702c401610211004d00640902c1500c0c1c0005403400d80d40241001e5451075102c01114295840402c414a2152420fa54655407101c1d0007200f20309201c400f501c20f5a8550030710420300003d503400380965071510301d010300c0051a050f0410007586c3d03505c00c403000c4405102000c52912003003008a028818585503100a050000a0a5003050380303d2100b40a5007505100308000f280824000801414102042c07000103c48a626000000c0c0b915030b090340102c07441c540000d401c0c0200700081c820540146859002880000d100c1780d642c0000200700044508229003642c1030034001e0b5514103400c09001d030080c20403c00080000c172050050112090590407618000649588078100020b201c0e40d0309000303035110301 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 590789982 1250 590788732 590788753
    0x5060d0c141f0f02010b0f0d0b07030e070f1e030c1403010e030415020706030603051c1701150f0513050d0515070c0c08150109050a022a1e 61
    0x900081c4400d81803a00701c210640450081c102c07032400500500c150b91502240202d25010007425168403000740c03401030245500e10007182d16900b05803030501ea80078640c01e5150390340d500100e00800e0301010404491191450028000700c07401c2c41e40d42940c1c40307550400b1203070300140d910b001741c1d010760303c00144424141c803003c1000084c0f030801c090080c1801000483d0302400c0d0100e80b4656081500200e40032812840d0045075141c040020a004220034102482000e1660300c6454941d800c0015600a001e000b15034249080e1040504152800704144c003a03607507513128000c80625100c20f030002d41c04a541c400c0c06c44200f9001f001511300441e07140300d00840c4a4100018025644110341007140c061250204004001c07141100141c41891656100c0601c001d031420310226282d06580708640039000495072036210525800031605503000c0070400f1800340c0725500404000d12030004a00521010002126902c02c80c86c200c80d001b455051b0308842d009032905541d050600c0c0400711065440d0702c10041c00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 590791232 1250 590789982 590789999
    0x40e071103031e070e0d05060106031b080103290f0a0c1407060c0c08212202090916090f0b030105060d0b0402040908070f05070801020c0717160b04080105060d0c 71
    0x31503002d1441c1c5410a20f0240005c04106460304007001140d107504500014022141e1600c6074002071900c060b070180c04541940d0f8080c2020b0810701014000780301d45072a030f509c040000100104400c1e840c01b0506003d1419500200d0b90b81810740700a00385038241040d24468500ca040c0d502d4124180170265850002183d84100c01844450245c1c000d02201e21042d40201384200054040c0c00518503445500c40d44c0d00314051141280280f0113040700000c01e40c021088207000ba49003141e02d506548804c4151112040b80703244c5403040e040b9080c089030510012410342c800c0d42081c090545181313814809c0d05848801c142c00d80d407084442c1a00403031116581d40c0420764555880350843c1c0050400101c0d0741036034a404140d903000050540303020035104011020040204164001459110000c50802810040c02d6880f03807410303c2400c83c4000e0204c1c002a000340c00303000c80d0156038030036040340c96a56902c400c52440c540151190201c035501c0d1400040700c03403c1904031f810000e039003c66081d00305414503404 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 590792482 1250 590791232 590791291
    0x8060f0f060c2d07080a0c060513080102030a09060501050f090f040614011401080901290f060313050d0503010602070b030a0b0a0f1503020903151b040e07110303 71
    0x700c802d80c494280c044001c1503c0500d000e401e0b141021010502c107400c03400451921019034880410ba038854170361075005c41c0c40e01c0c1c01c54042d07502524120ba074500c0d85400104d0000e04a41200c003442d40700000380a0b08044607031007030900e07a210b20401d200c1a80e941c010030440d04100c440031034000c42a00c0015410800035101580e100e40319031030028040c1190b0a614211001c00d8002c0d000720021005025210340e04443d0090744091090000d00003c00e07a1449090043c04144030140700c0c8410a180c40d040f940e409181407402d1002501240d128030b00314a031014900102c42084c2d51f180503a5258400302441601168141c5a10703070011300380140360a4910121380e2000b41003605d13880c0d17200d14482c4039586404485005285060001c9070719070600081200380c80f070002105040c180704011482c01d035200130a061403410300c00040495a0303511060400400215005803405160700010042440c0300707840300d500d000385038030351314071049501039081d1035560700c001d0342c1d40c0c3c200f400c0c0c2801d0a05501c211515 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 590793732 1250 590792482 590792497
    0xf14030d050a23030601080a020910030b03030906070606053a0f02030a06090501060503071a09030a1406010e0a020a1709030d0c020c03060606190309080f0a0203070308060f0f06 78
    0x805040c0c0300c0543c9a103460028085104029100c0c000080c03080a607804101c00e5000000d100c81103280424840000301d07150740c0c60b031691081c1600d503450f0180c07542d410b0040d40c1d9030b000c0103051155244032078900603000b00000d028003407003010f1a85c42d0209140d13011040c021010701e054000c0c003403480c280d0358080c550b4500304012900302110b000080c0060710b041c0480600d40f4440d507400700380c0c804545080e17400c6d01d84541005020f0340c00500e0802241e4210092000401c400d00441c5658901d0308000c07030705060a82c08060b040400c2c0c01003101c040080003031450704840c0d0b038031326410325916240421401d0b807082c040080d0005880c401e400390302004407640c0c542c1110310401203a19040e900c0d42070900f43c0e44044ca141001d81c10245000003182000c0c04141d81c0b08000f00d61551420081101c80003000141ea5008010503503a105001c1c100700c0395a08441361551502600c0d51a040d1900000b5907032303071115104400040807000410b02c40d0400b600102c40311032008100300da0041d8040c050101e607802118 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 590794982 1250 590793732 590793737
    0x1b03070f0c0c1a0904050105011b0213020d060b071101020a150b130f0c020c0901120b070302070f0b0910050405061311100f090815070309030e12070f14030d050a 71
    0x500d01a045803202202880ea02195102e00440041200b121b078140d1085050000c1c600c41c403c44091a9180350402903412261000008030039040c000c000e0291341e080000140ca090b9020641a184401403c011803260000c4d10b17060390301c032004903112090180700504072144803c0c8050400300a8106045640c000f9117180120740d20b80c1003400540d61409007038001e4994541248666030380c18090f04400b03400541d0041034952405100508441004102908040e44080410466842501110100ca070040300090550000d0b00341a4030400c0b003035031180c405205d9103880400301c20040c02840e00c0b4607000406000c01e9940e845241140492949040303413085848001c3c041d4995840940c0c0c6580c044c1d95a03004568442300d40082c00c04100f94114071480c0d4000032007100300b841c1e0304103490ba10090070b10300460400c0b0140b400391102c0c0e003507840d690343c0300300880414400e000700098820304440c1540490010143d4032940c451940b50400c183c036070503801003620b0030582c03801074006103960351f07103403 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 590796232 1250 590794982 590795003
    0x209030709091b0b220b220b07030302030f0708040309050f04090f0c0f051c02011b060c17070e060f0711030d080a0b061216140f031b03070f0c 63
    0x2c55810101c0c043c2c2d6001003a0410340404d0025001c240401e080040360908108008280c0c01c0000c1070707600f8007a4050880929229004040c02140d2400c0420014610041401d07115030551502030081d400480e00c2c0c04041548034005600c00c0c6c45241e00d140070303a8254903103803144e60400003403018680c203070785010b50080c0e1150b0f41c003070014000c00c480501e01030103120119266800d00e005091740c204290700451060500403640c0d03441009260781c142c9030030340c2400c0030a4041184140d40b260f94640340f0002d0280ca00e00103100d01c0f000e8210540400c42c0d0b042d0000e0000740d070760340ca405503902d4140b02c0010750440da003800203801d24400c082c001d01c1c61034001e50100f001c814010002925011400324504005018102800401007aa010f40b40e0500003c442480c24480d8944070045001c000520100c80303460341d140d16548903401201640100c0d44041c0700e1a5445043d01c0148285a006484200c21400360316001c001007490403003500e000d444203503140f1090240303140c400c0724084402501a10b10700c929 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 590797482 1250 590796232 590796263
    0x31103040506040906050301060b1e0d09061b030c091208030606040b07033507030b0f060313050708070b0901081b0a08060127210b0c04031401020903070909 69
    0xb40c4000d0401060780c1e030340114045040c64289400e403003eaa001d512108030612840303406d9480314030100d8241650080080d191f0750034180b0800a043d110b03402611031031800d240b1403001410001c0340745204c1100c1c0c03070a1001643d4448121405003051080035020340802a00d1000104502c00544e086840203180600b016102e8941c2c202d0341c2d101d58021000300b444031442e0078200744041180700d000040c610b442d0060703003213140e6285008070009000d08109036450514108568030565070420649028180580304c0c40e0021902c0d48144401609440344c4c400c42c0400510380c040010140152803080c04c1482c10075044400545007008094910355107840c41d40b2000800551301e03009422071811aa5400c1c05608103200054035421250b68126071140d041400d0882c114500000358088400c101d001a0300d5140008030903000740d412403401000074a0007002d1000f9a0000c1d4003510607a03001d010f0184581e002c07a11a98202c1c4a0382a0054058004040403c68a9080e5104030721207805601c0c829800c614 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 590798732 1250 590797482 590797489
    0xf010c05120a171027060b031803250c030503030a0b090a0b0d08090d020402040801020c01110304120e18070c110609091b040302030a05100c0306120311030405 70
    0x3070050a1150140d02184820102c0da010600c0001a800d81040c28107034100480c4916001c42d4030300070b01285c61800002c600b101c200e82c802842d803010941108120f400d8641d409a079031640706035843c4806a544540d074141101000c4211030840c600d4402c06d9281401100391603414425400382a690350020000c00800700d03e080c00114400c07a01c51100040002419042111540003d407450305450705e02061010b4a0321003106000c1955004407045480d1180720f0f001511540840900079013050021800060714001500902600c0b500d01000b8068504101070721005400212070107041c020189500001c2d2a001c0d00c03032140081e4014004403610002205148543c46064609000040e24200002c003400040c0c120541d00320000c0b41d45602c0e10f0440c01c0090190040074007100a00c1154100c44489c90743c050044030011a800b4007a80c40c542e038282000398464403140e0062100038106581e00c582e00f4400c2c8a0213003034a40ba2800c030341407444142c900b1980030a00c03000d009600c2c8410030002c1050795 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 590799982 1250 590798732 590798743
    0x1106090904080408120c2a060d150b09030d030c02010207082701030c0f12091209211e060608160801290d060f0c0804120804020f0f010c05 61
    0x24010300c82c0342ea0f510f14190300c0314900508001040004c80c414000410544c401088000840204961000190f920310882041101c8100c9403c0d500080001c0c01810700310a40d001821588404010341c140c0d103545111107602071044103181c2d82e1503008004c80072801402581724150745c00407807000509004491b40c400f40d5540c8240d0308400c4000d1300040c040007240065201501c1035900703103030500c01d80302825009000c0c600d28441d20000d0014100e507241600c005a1320602c0c00a412980c807011851290502600400c070a02403801c00c00c040344200800314208886036640d1662001d52030450840c034181080552100c070b0001c80c0c044e43c03161400540c00d0004c00101f1040381e40c600c0e410741101e01d4142d4540c21240c440300e22511032401e0750b0900c043d0b0150070541400010007070380d29100701087c51418400808400b09010300c140c0ca40b141107400c0c643e200503000d104901c200d400e041512000070041c1d0312090110f6009511502180070034440e41441c24000c5182c2c503060410840c03d0286541742c50401 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 590801232 1250 590799982 590799991
    0x5120a020913060b0427050a05030a0f1e0507060b04090203070312030c0305040f0b1f0b090a060c11131103041a06090f06040504240e0c1c11060909 65
    0x120b10000302c4000c0c0942880ba101350b040044034100010350301d030311405480c11090707852034a180e6001c0d52a01c040c42401c0c010840c0341d540c001c05890b503465032040c0180442e40d4144d069030005403200000170000c80401075620041c0c1150312411309008841d60f5000192004180d0320350841c0d00c0b50010801a101003100da0069403048940d841c0c4004814030080448007003001c0282058240760a00010030f28440d83c2c5c0b80066041103e4515030707070714001021500480c0c101c0c440d8141c0d018070800907400e81044081c01000c01d046500c2020540d40b0102120000c640102c013806207142c000e4100c000749051412010901064440441d04540340c08a0660b25002103801396080e220301c42c81700d668500b91140c003035408207084449184070304109040c101425001002c03d40590303038440101d41841142070b480f050652010304500c1c2c8080e10200703003001400114011003142c0c41035450320040780c50200103015500046000100f0b10300000c0e103560100510f0709038410341100e81002034685503150100f803280304 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 590802482 1250 590801232 590801251
    0x1207030207031b0b12070212130515070f03090602100c0203270303071505090109120e061201140a060212160602041a12070c0308070f03140916080a05030405120a0209 73
    0x191b00c1d10b2038010b030500e080f6100c905d0801c00c0c01c00215041c402d44195150949a06a51040b50000b54203549400c910854102418004883c090401055400000c4006441040d401d460b40e08e01e40207240401d030b440001c01500981c2040c00300b000c5000c1d000c3c00301100b4500001e48000c056200001083c1540e100d40740c1a00ea0120800441c8082034103070013441d4010a5290007044040040d0b220001d41740c42c0c05102e0350420040a078908201d65805058a40302c95840d548410039507034078442490f070244d507503440c0341c043d0419900001d89180049020900d8030510303230007079140c021500c100d802092198070080b10000c0e400e10000c00c4401450ba41d21703e02014800712242e8030483c1e01000c500e1070400400740301c20080c45140b5000042d074040070b410381006450400b07418403450740754150044c122088505443c10890020081114000a025903480e41740e1442c410480d92642160740e25680c1c11b010150495004000c20802f50400100385051104000d06541031440d1070303030004501c5a8140c4010a1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 590803732 1250 590802482 590802517
    0xb190f0e010b03160608070504050a090603020315010e071214070309030212090d0212010f1a0a06030e0303070c0302190507050901050f010801050609010908061006021207030207031b0b 81
    0x410024442d04014110031401414000c0d00010008040c50b0a170151070200040103000c02c3c021806581a100034100c01002d03a845c250311110540d00a0000d0b200907882403142c40d20046142204000c068165603d9000200030380e80c0d80c200030380719810506621000c003961540c9640140d8411198a4010a2070b42e60206614101b420002e140460241c4c4840128400f007008880360f644090f1440795080e4103444103424030b00b0f10010a401804920f083c014802d041c20280010110321005408605600b104d40f201601c6d200e00c022811136120810300341d5554020804561918000c048110410784240b0448405810155981c0b403110000b450480b1640c0c0003840c103100074601001d202e409000c0c1503840015100941c0300080183e60103205150003441d0000b20074140364412403007500071b08991001c4992500300800172a1341c0c041a840303400e00500504803d50508400c0303100301d41d141c98159009141d6141551200d4140000300170300d015101d400c004001a1499180700500a4044110030010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 590804982 1250 590803732 590803751
    0xf0507021e0906150315210c011d010912052a090a0b060d110c030f030103020411030c070b0601021e01020d05090d0c0b040501020d1d0c03030f070b190f 67
    0x24400d0003070640f500c6495050003565a40c2c00d5203003680d900410344207001500d082d801d400b15915120a202440055120440300420351100050303500184030300780c1c1c410700000c2c8a200c081070f0b0036007541221400296298000c0013200865400441514040c1054804051140f100c40040c148100b00b00c03140300024144031a00c40c41d00504460780718080100a0000c0b20004001540b1031068031580007c640d42c800890401c0d464020654001404000803240d4441f0103030003840726904244401c038850303420000703180c000501000550340107078160001e4606121190b510f100321038100904e0541144600d024001d0010301c448100f2440180c04000140d441c0f011076811300654800928110141c1e0120110602069008807250b50050304000303030a51030303111490401c0c068400e01152200c4e1074200510418965040d810281685250500301c030b000b080c440081c1a2203014071005101c410381c0900204c0040307001603e0841d0b00840d10b24034204103021805803801120755001090013019038a001c00b0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 590806232 1250 590804982 590804989
    0xd0e150612100f0e1e0f0304030f0308040f201c020904080f0903030307030c0f020109120f140403030504050a09060b1804090b091605030a020306070e030304081231060f0507021e 78
    0x40c1d0701690b182015608c0d080c1561141c5619444e50382004007040b41c140002820311405407081b181040d8400d880d03228821103100201c85407902140071604c2048003024650800924a90305400150301070078a0107a03545680314045650007c482d0061002820030030900e10756000c2c002940303c2d14803600c0000b01580c032140c0042c100b080b2002120300350381c5401c40385030103d8901d1401020404cec043c5040210701080c4002180c8001d046d00050758800c001143c0441050340120282040c1c1c1d0060f1505102650380e2030466090350b089101386d8500003401c001461500c005d9901d410380403900078001085441580e40d490780510000c5440001c16004210011203801e1807114850080204070000e01c820b0405400080d241d070009005038042c4a882001080300b03031401d00c03d91300107100b49015940916202210b44400b80e01c0498039107100145041600c1d0003140020f081045a40c0401c400d5003960304250b0144e03510100d9104820a00000f07100d0301300140e40d084e03e00c5c001901d201a03410a1503640d074060 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 590807482 1250 590806232 590806243
    0x130e0106140901210609110304050f0316021504270f0614090406060b1207090510050d0b01050d060b190206190c050d0e150612100f0e1e 60
    0x40d8101c81c60700300102c103060303a0302203600c043c101e40d4000f166141c0c00d891602040103001d690b00c0710300c906040503078140d82030b043d020155209038002c20641e452001e504240c10703200d200b0f4840e800c610700c5e00c440703c01e40581085900419122542000782e45000c1d2543c40000c0022040e40c024000032116000c001310003560b90080c81c510900180043c00700030300b27244c5c11017021070407415a2805010b45000103024407000e40c0140004150780218151f8502d8001c1d11412217140448021010810007400014582021741400e1625443d954030039081031024490000135090301c414941c10400d060254204501c07062180e44020800d4480d065034818010119624414041d144c41007590421703010810000704100400e86c00c0d4201080000398080c00c00816038090080707d038424001440d04ea803840880384009003007055005a007921074151b6603030208000c40c0d203054078010801a0040385251039110365940003402107031000ac0c0c012811454401105107045542c01d150004007003002c02c0c00c031040720288074 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 590808732 1250 590807482 590807507
    0x201060807050102100e01090b0405030a0305011406030c0d0608060a0b1e06070f050106030b07030f05060d0210030b040902150301050108100f171c02160501111c05130e0106 76
    0x9040310a00d071600117516000902a0380001580768502d0751050342007940039071b5030380740c2c0050001414203050420943d60b401852200300484c0c0f400c80003207003042c0a81d40345103c000004100c6441d5689002d0b444400c1d03000041c54084081e1108070106440400b031182d5031085d0040b40c0005503000d201e504020344040c5503c01c511840b008a400107031640c80b40000c407014150455401c031003d00151421500603e541e07400036000103481c02c1402901941500400e9140340480c0081c800b54403048100042c00c0f02e4410001e5000b1154070f85100d080e8000d400ca024041001040000c0c0004141c020501c0d0a06c0171108082440000005200315030300414102d40019003c0141c0030307203604000e110483e100c00c0d0300481501d035100b42c6921004040c1001619000640c842c00018440110071000e562218202c00105c180b15403804081040d5120b600700b4003250b940d010040604111f04007030358646408140155082100402103205c1005400c0c807490014a9107070300c0b54039136614100006107441d46500c0c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 590809982 1250 590808732 590808749
    0x307050a150621030302071a010f0f080105060f090a140405060406060b031005060d09020d0507051201020a050d150e1801050109020f03240a0833012108041203020106 73
    0x3c50401816540700b2080c5035154941001640d41d03010303040c2103a40f036031504107a81c1c2c0c0550032000440e440004003009802c685020102491283e04c40d40d5a6003a1141110960b030449680340100d803941c03811558840d042005407200240c0140c69500c44c810703402c001c54094500394804010300003040f0291203048020031140b034135141141002c3c40041c0e03403035425202d040d00c100000304100c040e00e41280c1c000c03081158010301541c82c0c05580e142054a541c128422075100e8480f82c604100500c0060080302c0b1f03404183c4c2e8456242424008110300100044003410142d05884c00000c2698040d1100b0a4050305440803107920f4212119189401c2d00c00c142c001c10102d134014040003006442d0a015a5081620203056840300c4400f5000d05a034104050f40c0150310540ea42c1e000180c8070b03070100d6031245840387c0009010700180007402000d4270000925400080c81c01c45801004007401e01d540c2a200c1000000301c000b6072122613111948160072580010900c0303180703081d017a000c064091003054010b0040c034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 590811232 1250 590809982 590810009
    0x2041e0e10030f03050906270301050601051b0f0d0c0506100b030114190b0a03050a060506030121060f2406080c0903030403050d031d1203070e030307050a1506 70
    0x4810040390302516110041004500f10303079800805004400b0790708240005001542c44900403400c0c101c0403101c68056800790a00394041686900381809130510400060b15041d10f004a4085c1d00c0c3c15010b00e809016203c2e005805142c4401d190070302000030320180c190b581d1070320012103007081d03801c025000c0c24000c454061441c040001850078400d40307045440740c0110705580400c1d070b0b011641c400050303d961840d64065482c042180d00b40c0320050a900480341d6010030042e50b0380d0301c80d00125a018040c0030384c00001480100107040080118401d00140d00800202054590345d0780c0003a240311a5114014540b070f0b1024201c0a41e8050041800c007020f44011311005140c014081c000f8070014000040441000450384103645040040b00c0c01554020111104005101c0e00140144107070128983e40f90780c111800c242d040f10000302280c9094440c0708441c0f464403600001d88200c041c81c03104a815020503c01c075004600c0901011900394040d074400010b4074410000d040131501e05400620480303480 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 590812482 1250 590811232 590811241
    0xc06090c120b070f020a0210030b0307060503091002040302211f0609050906060f01030e1f06090b06040b030115030b0607030e10020a051b030f0712060c080601020c040b0402090402041e0e 82
    0xe4000c40c03564054070b010062230303010b4104901401d002041d8139058400c007040002d480340d2203401984600080003d445049003180b81207003d9109600c8007940c812885080c000440320f00300140241302003030381c4c01c84501c0c0c08200740d640318500c0c0900c0c100800b43d07900ca80c10800e0700d0300c9009041c1d0200324200940098940640041c20003039044c0d2005040590701c107443c000441c410000000310303400e10101001c5901060214001609281c0101d05e04241801e14403841401d081c001d5400b07584101c030189066a0811100100740d5180900c000d08060b11689811307000e4640100905510f03010750f480700102c00c445028800d09a04d466070160456000841c0280418008280020300038045019904005030b0640020314046141d8085410b500451200141062600c00b900c14154800c09052000e00c211000c00d4580d43c40803a81b50b80981c1201b000e04919207030691100d0009074008100501300b11442d00814120b82080d08400d80c945071103200e0418040806504200030080c54400448a140 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 590813732 1250 590812482 590812487
    0x4081c0207092f0903030706020d180f380702120918040204150e04121815030f050106091d0103020f150c060c0a120c020303070c06090c120b070f 64
    0x40000110000b07503e42100250705441204482060100600f01da46641090800d00001d43c41960041040c600d00071000d900581e034880e0b00000ba03500a182c2c0c89400300540c4840704004c0504c4100c9011079078030442a52201d0014800c03100803a9004441d600314606248003030321b81a074048108040e80401c2c06036035040e655095074600b20544a40c4c13183c1040d141c501c0814003800515030407200d0848018000b145400d0819070092150340907076820182c4c4142c9603029542d41010b0803d0400504032400207002114041079244070300c94007440d000440b0908540c0140071100c080e0448400121203180c20010914070181d00c00040c500551303842040c0d4035560025014140751003480e40030f00410a007407004d8640150583e0030004c580000e40b0300c1c519107101da03105560b01088204c40407c60080381c0700d810010b01d209111040185400942c550f1310f0300030054231101e002c0a0220f40300c5441e0710064001030500d59001c4000c0a9240c0007030003c40c0c03c0c0c605007413101402071460f0200403400300c2c00d0840d1075 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 590814982 1250 590813732 590813771
    0x503030f0a121a041a0612071704020306130f060c02060105040b06130324110301170102180f0316091a090403090b031b07030216050406030c091104081c020709 70
    0xf0012540014041c00400201d28016460040c10b51700c880c01141f013074041d009407c0303924030610840e5104802040c48140388410352a05841c060341590011000a0382d4002500b507003600e131070080b542d095802495590b03c80c180c4500300c191b2001030f00907000421032420f05000e006030101c000c031107007418030711034208a888401052002500740704142020341c0c20005010203400903180c0c0b5040520040c0c40c54a10105540d00038811891101062541d040d0084010b10a6421400e61655030900b03080300a000c0081581650400d01e606016911001e410340f40b034016400001c2c0164a00401c2d18404030702c240407142200140e403809141120104000a03074410403010948035924652500d81e141d0040074800d2101e4100f5007500c0520000c1d12006040c0c00044801c09040500552a80940c45000b0b01c0b00f603600d0792000070400c0b900c00d50240650076282c0c11071a50441c0c490380725403d090361580c0e000e00d0701c1d0904081c0006004009800c444041d81405000c2c0a081032200502080500098205116 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 590816232 1250 590814982 590815031
    0x60c030d020307091d0103200303192a0506060a06050a1404051203030a06050411040302010305150a030f03030f051b0c011e0e061501021905070503030f0a12 69
    0x120780c0000041c074554002c04004000d08581c100c4807107900441ea0014030003480a02007685c1e0b444200400c08009070032000028501c0c0340180143d03080009a0110070441422100003805002c2103001803404108880c40c242c0d040880d0104c99030946000c1c0c05d101c0c0c01c0010192920780100c80003242805090781080803507460031680e1500f08640178011800300c4240c000c91700100d41c0120021403c1b008500008055406201c003d04100f200d5542c481c10801124900b481170540510140800c00140d0300980c01598030480e14580124480c075214002003544000f500200d90000351409900d086c9a8540300340611944030382410081c5041440c45501c5218104001d507660b60000036086018000a400018400c0d4480243c290b00140e40131000b0094110418061f00d41d100f41400100016a5041004407542040c0c01034141c0c2164400c40c19891140507900707075001e2080200028041d101040240901c80b0550341c42611030604040080585500c6000c0080c03003428240c400740c41d0360311441560800c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 590817482 1250 590816232 590816257
    0x2040e0c0a30150e07090e070507020a031505040b0a181101050c060901060815010e040809030f060c0702040c020d12051b04080309040b0306070519030902060c07050a05060c03 77
    0xa20200c409400030031a0461100010904103228102c0c03100404610f20180c54001c450030410360341d051000c450405042c41844050f004600200325001d0049005003141c40c00941240c0b2010780b61703169038001c400c644101c0d0f1000c0c0c0e5628104014808a00640368110b64984001d0007080012030341d0a51407040d9050161803c0520000e842d802d038080c03000c40c1d01100564043d03d10620745881c0d40c80c001c0045116002150050060009603100e0118010b07040c2c843d010f408450f0f90300c4503160a0891340140072640d4152140300c4800d1880c4000f00170081c400c1c0e480c5103001d680d034040c0c0d1050209a41c58144003000f9544030301030728a155078100440d0f0042c121000400500340c3e44103070449002151a1f806d02200c0f850004010507002c4e0080001c1000c0c5405403014801001e0b01d000b8942e85160882d1018000741003407044898a108611841c00c0600303041c83d0200b0107502c0398001035090b500020f9030040c0c1c2c1e4040b0404001c20304288041d14001c1c00d08495107800d245006056645030301c240d451310a10b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 590818732 1250 590817482 590817527
    0x12060402040c03090605040c050111032109010e07151b0f02010806010224010503060f070c110a0510050304050f030a0c0828080403020c1c03080a0b04020c0102040e0c0a 74
    0x74070f120790b0140003c50703003100090220303040504015880c5d00700c2e40907050020350b000014800504000080350301c51400000d02501d4031020b103201c0c481801028169441c595291030007a03551150400090000d4200e10003044500c21480c0b1010b070201050340300030121b02c10807903540404a540030340300c082c0ea50340a0030300031b003140c0d990070040703080c10109820042304482c0d40701072040e2a40c00c422102d050b45c00560880e041c9494020280c480c1010032034009000a050450150005140030040401b0a030060000303010b141e20349000401c0b503200c0c8071030f0000141020003080241701d801c10602c6500c04040d0095440c285045400520241e204031000e004020002044001e0720024045412081c04488140e01c2002600f800240076401c140c070290010311070350000401c1450310790700d27600000040d540c03034201c0d00320300d0713941a01c42c510010308000215668407007082c642c1e26140010310800d40d14038001a80e50381050010280079a02920b40142c29000303103c0c215103d500b10840000c02c2c01c05418006 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 590819982 1250 590818732 590818751
    0x907030203100e07090305010e030403051903090306060b0304110d02060a1b05060702061f0806070f050c011d2509090804031e030f021f05070905120d020c1206040204 73
    0xc0b80c2c519180c1c40701211052000801203090350002e4600d003030306e03c1000280311300150942c2017030f500d016078080034100c1c0d0003812411408810181400c46490704c80c0c280a0a07940c0c0e00d41341c0908036065640201d185c55000420481000400481c00904e450102c800780240391080d00810320f507004140404041c40707905240c0365800e0402340c4581410710b41c00301c1200c906203082d5400940707a05042d80c030045c03c4c268040032100385458086c5203074207039074404008156541e200c05c4c08468030010304000c01d0500a080000e1443e09000b8050030520b120342220f290031141480f89051b02c2c0a00001c40e54080403441200cdd9070641e00c4a244103000c8880700302c0003050319803e42c1406031340d510a65000402c100c0c1180e1200c141000034240e025400c0740079031038803507110000401c142d8a64071110303042010105400342407812810a58410368101001c0c0c50030141d69130b113072004a01c200141090703a881d5a400200c09030061a81007081820040c02590301041845180c2540c5540b0040500000d100c0c2da01c404848 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 590821232 1250 590819982 590820001
    0xc040e070317092418060c0d0c1202010c09120203120d0b0f100c030c111002150c1608210408130602010b031506060702091f050406050907030203 64
    0x15000303190012240551040c06880180b007a0380488000c0d4040d03844503065100c0c5080d00d0101060305500d010600d1310f03116902c0b00c4070701102c070140c014590051040c0402e00041c94108101100d1410315210001d034128541040c1d0300c000e41601002c400c5a0610444820040d03000c03203004201c440b299000c00c0b03008183c4c070000c0c0c144040482c94910040012810b003000d00443c3e0800c8130046001d441400c940c1e0b03200414400e508805044083c00300d11443e01c0840000c3c407413001c96103a07a0107030b20944045240300d03000620091890610030010391016241c1e10550032080601034000901801c480d00d0030a88401c0c1450500c0f854502030300b40c103070205045d2106403000302d50b1140c02c9243d250402c414506032421140300d800005040c141e1620800f004246a4014892084008402402000400d0b9960500b40707112a0040c44117800643c248107072001619401052800f0b9444111404c04070314114524585a894550103503110b1303810003100304003944480d5543e035089421441c01590782d07500d28584 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 590822482 1250 590821232 590821243
    0x50601020a23030a0807031802010c14150a0b0301150f1a09040501031a13030e10120507080601171303031d0a031107060804231005090d080a0e0c040e 66
    0x10002c85020003c0c4010b00341d54440b81c4184600b0f11914208200488080b4082c180607080c01c00a01140011031b0700c2020880e100302107a103150284084680a0002c91800310104000340e526281140c1c450302400054a404c1c00b49003035910350b07c0610090149411050b241d00c0307416119030020403c0c03d484404482000c20b0840344003100c080d0090095523503d24110044170008040e03183d01500ba08017041e8601c046050590354660190340701d00794582941c00b08100c1d001040c10f00030900c90742801092032040c0c5400b50500c1941e2540302c102e1607140102c00503010003031001110716414240001c10146081460352002e807160149400102046d15803180341c01c403650800c00c0c049500c079000c9071104140c6d02c04c80001d0444d200ca4103944182c1e90b20350080d203440348142c2c6c00034180007003191494078180c1221030401106961600701d032040301140704404115074003a80e90410a8101c400c4c0744501c00d07041148550481a80481080381c042ca840005490b001d021048503ca65210301d505014800108075 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 590823732 1250 590822482 590822543
    0x61e07020a0317030402121c050a1101090b04140304080d0305060f060c060106180b0f0a2706140c06040b04020112150509060a0b12060a090912030b04050601020a 71
    0x141e0f900410042c01012070f00d80017201c04912501605142d8030503051701088038030814000d5000b240d210010418241c4468102007001000c0000302c40c1c20b012040d000340503100d651030003074003103419504150900303059610070400810300130380c800c020030400c0c0c0d4000070b0070305000030741e5280000e4070383c541000050f80140e0101c0c00590000c0045400c90200b1030104599049035003946a1000341d0140158460607021680b203418030b030040910181100140f408010400350010346401e400900382a1a00d46a510003143d00324810b00c03110805001303164010f09409024200002428208081e408600c0d030b4500740144000c1c813400d6903001040459000788050209504900c809102c3c541c511202e07015218028030a0b42d110b00c1c9440c1c0891402c1c2070074901c0c41c1c141c40b4500c1c3e0315450a02d40d802180040c00d8003070726040d0411909480058000480d1141c0580c5d130340704140081c403103550048000c0c10369410380b809a100314584030503c94960303000201a10001da101001941810303030050207242001d411036 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 590824982 1250 590823732 590823743
    0x90c090c0a020c0a120212030d0c0f02011a091612051501092903070203070c2408161d0301060e01080d08010803030705030a09020d03051305061e07020a03 68
    0x24440c481003050064808005240e00716008640c008082001d000c12522484240700c8075070480c00c001d801e0550f0200390b000c0128048a10300045400d01404940f24598140c000800c450f0b0b1005a296082c0101c600002111989500c6801c8100000d00c0150000d0080c07160404180800000300c0d000e042a1040078000101c01c1140723141400d50103a1007040103a200e8005094040040b841510105000d40340c3d603d09142d101d4032a42c01000d0a00366400500f215007988428030904002440080340c4002030000702c104040449110b040803404103103010211010b1100341000c1210400b214450ba001000c0c003440d155100d1101e0f000c034400100c111741d08140c0c05500f011404905074001820550407240910200c2c0d440b802c4154044800c84003e00481400760010004560200e110781f01039a00030340c1b6600c001428030001c0d03000808582c01ca2a044002c60401325400544d21810060301d0000c00b0b0070b840b0740b4584090040c0d071144031080380502c0703100a0317000f0440a041d520765044400c0a10f0b44803 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 590826232 1250 590824982 590824999
    0x1b03010e120d0f05092d0703050d0e0609030d050f04180902010e0607050a060911060d0b040c05071716020a03080c1209221e0504110621090c 62
    0x1e01149405901c41030000391801c0c00c0c00f212285200440c4104d41c42030075444040d00001491300801185400520018444503000440700c602800d030912000005610501c000d200c0d00d4503a15001e007002507101d0507188120000c0c0103503d0941c402050101d80c011446c58441d03600e000700ba48821841c000c682000140a200c00e0103000300850aa00103400c10f8000d8a8800710700309a01c081050600c07401d81c00038000e40007890802d001445030741103510070a1065002e090240b0301c00000c075000e82c025042e03400c00561284400c1c00d01d030900d440f8072a800005864454038010454954038071281282039806694180000c140e0400038502d8035048200360300400c1c19490660b2422b00c81e05035045810405441e006200800c440780003143c084805240000d8003d00b90440b80c8115464108a01040039028540702c04542d4080c040c0707041140788844641d100040c00e4101424039040441b240c2d0b07032181c042c000400c03030038145c03070191290349400308070300000751f40c1d00c1d642c10710b1107070900c1c113080002e03504000300 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 590827338 1106 590826232 590826253
    0x150f022706091c0309140a061b080f03010603060e0f06090601140c071a03100b0f0408030a0c03080a0b060d0b060c2b030e1b03010e 58
    0x280402c1c149609000420000c00d0100c0c09207160f00d41100f2010201600300104201800c0900351103200310701d900c000700d9450300d000d0060805014036000c02c100800300c81c140d984005076011076078075101c101e035062068081e0020f0054401103401c1c842d010a14150501080748111700442030740c00d040e00c418046c40810030001c0c04990410041b00300081600d01e148000b400d0413040d800040006601d084a503100e03100d0901000300d0500740800a2001008004126a0a555146071420366525680500015522076a8803d5110340004905ca03802c440e0800c0001c100c440c06a10dc0038140d60700d0401c20300c2142c203d817200c0c540c40a8144000608080145d00540801c10050802b614007061100401c1c0f41440d0b184a01c10310000c6582d40038030300c104071222600c400e001030030180f1940955040540e2200d40080103034264072140051404180e80940003186400200400d03103505046 = true := by decide +kernel

theorem cover : BRFrame.Cov 590647482 590827338 := by
  have h0 := BRFrame.cov_init 590647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 590647482 ≤ n) (h2 : n < 590827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
