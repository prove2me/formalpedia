-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3521
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:54:15.945972+00:00
-- url     : https://prove2.me/submissions/460103dd-fdff-487b-b697-dd173d34bcbb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 633093525 ≤ n < 633273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 633094775 1250 633093525 633093611
    0xe03070606031e020102152a0a0e040e03040b07051603050114060102060411090c2b1b0804060902210c01030507030204030c0e0c070b0106020c03010c1d1201 69
    0x3010600d43d122000300e000c00c0c0c9001030782c0014250b00d0350400700610b4101652034810003d62440501d0700415103002560317640d5030b24a611401848100380750744880c3d01c4400d01e1003d0004888102c030f4000e0f0303076500400c000d12100900c1e501500080388910201c46400805a1206d2000c070a1944100c849a4568001c2c01c1d044480705000e40c1d1088082c80100314031700d8a40c8640f160b10100a003403602565140380414047c0ba0a00c007151f40c00030809403404000d90301d4210050004082c0a83e01941900c2d2180314403003c0c1c003040c41e52021401d50b03a02c141c40b40c0c480303854070002070108100c1280e201030248004010144482c00500c1e400c980d0386c0182000c0300540001400fa40c9005103884101441044203100003030401210314107a85078400406030320b03a04c05269100710703c41c59070f01a14014000000045180d40010b91030020303003040e0020322081e558801e081c0c4d040f040c8202e4540d0000100340e084880c50901c41e4800000120740303400402c00c40011a60b00100400f08005c1c0844d5140340340d038080200b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 633096025 1250 633094775 633094793
    0x709090317100b0f04240e13020421050d140d1a150702090c0309190609020a0e091c0801120303091509020f0d0b0106050a02010b03073c1202040e0307060603 69
    0x500d0180e00b2242007044001c100400884040740f416103d064408c1c0340800030160b660660380a08036405c404018100c0000380d0440021000d1400c0f0307001d104580c140000c00d4480c031010150440702851003070030200560100c00142206407121400a07014640880c0640c3d14050650040300d48880700f00da48043c40d00500c0968003000f00301c1303070704a9004c00070b1003c003003030001c1c681045140740c40e01100074012038070702880503041c03010001e5440043e400001c07500200c15803103a402504600101e4400e403a040c03207010b0003208902020400309a0b86c00c01002075450740600e401d0fa0600c286400a5070003029a0f0740e400d0300840c84200580341e6558100c00d411803e00301c43e00112082c2c21280242d407103510b562140d00e004014000c210800102040d130b502c0700b90003504925015000182510b91130b6407640d40013412540701d42a01c2c0000412100800313526401c031814880c050064585800d0a00e00f00f219511a403258000102d80203640d4100324481c502c2d051010f480003034482c240214030fd528506002c084c03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 633097275 1250 633096025 633096059
    0x326070c0b0f010506040501030e0304031407080d02010b0105030703270305091905060304022218120e0f06090112060e010807080f0601140d06050a050402030709090317100b0f04 78
    0x2e046503440c0148816a02c0400340c80458609203008240341ca060350440c0d05501580c2d20003001d610b4034000800f41260046800816201c080049038600c0b5004d0104030309a40103075822501040c001c0010840380761080d04035806200621001c8015811a040120070a004600c016400a10045104980d031301c4c1030314201a18030440300c5071650450410700000c2c0244000b0740000d01c560f81c88921001c140c45100c00e80d01c88110401c10401c4007611220340402855034181d011a58494040d07414849107014a215030843c01002d40000700c00c1c40601c080c000302da801001d101c1c7c14043c80c1d800303041059010380601c501070f245240d11109a949400c611503c0c290745904240d5454120b58545230641200180b0541110f441481030442c4d9800d45000c0340007840054405000b80b0304107404c0051111359a04498010b92090b0211200107071b40c1e4108204031040c0f150d0090001315540c020590008030b490000e0b8102d480810368540c8181d6aa09544031640101c2810341c10100c0842d0400c84d01d0f40e0240c254034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 633098525 1250 633097275 633097291
    0xd06091407030c1d1620010603021005030903070f020118061808071d04081e0a09050907020703030c02180f0415110d1e061403120a0c0326070c0b 64
    0xd240c42114a06001080c000b403946280c5c24540001c41c070f50034031844907000340b00012914604261041100305001e400e081c0402e80c0a0b41c810f0b69010800da104008582c800c1240c40c02550501005a5030750509010703c00e0183c1c1049102000d1102d2407000c40010001001c8544425000000e1810000e0710880325034054009a080075404000d2034518921450030302c3d010096425087d0b40d0703407400120b14003908481030340441424403451140e6074140005c000794030f00d0380c0360540004d58980400c0700b035110445654006030400081000020701402101d031803a480107010550100c00da400460100a00321494a8940f140c00140006d1007005810028a405e031024207000b100044840054544110140381c01c040342e8a003001c1403a2240c40d03541e5907a40700c0c3c0e0b00380bd0004513916130017944402c90000c6007074840e01030392200c02803040e00c0c20111451452541c03075080d075825640e04c0c00c1c0c401c0da041c0c08000d0317144041c01045c4615000d400c0409449012540c850346004561030500984454004003458 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 633099775 1250 633098525 633098549
    0xf1f03050f040209010302090414010903030b460e0903030711031905070302160b09100302040509061210050f04150c09031b0b0705010e0d0503010b0301050d06091407030c 75
    0x8400344c0ca0f455000da066a03015181c00810741c480e840c00c00032640082040c1c000b55481c000840080641c950800f01c0080d008942032142000080840c2e9034018840440310380b0450100186501c84005203940050510541101c2c03030065134400041d0483d00d400c5490002c80d4000104021440e500880c9141c4074010710350080d070078507d100724a000040540c01c4207506106000c20040100b40c03003081040d00001c8441800c115155441e0800c010781c0d089160960b1142880d03540103c0307558402c0c0f090701c0c2290030040016095468980900c13003404032500380e07024117005031034100c49201080e000d010b00500e140782c0591040c0c44c2a00300040d95041068151071070301c1c1810420103100d0340c03000000064a0b008480101c2c80b0040c0303108074203100020380c007101c41e05402158010512070198080c40e041d150030340c00d0707807940080318104444500c0240a0700c0b610190170b0006200900305200b240141034405c11000501c1c0025071a0702081d032984003812441342e4802e6101340708015001800e031004001000c560 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 633101025 1250 633099775 633099781
    0x40801060504200f1c090b091e0709240605040f120201050910020141100303050903010609020301030b06030d0f020316020f06040605210106050a05090f1f03050f 71
    0x10610700c01d1003008502d88001090511418140e414000358105c8100e2007000049003610700507070041d03802c491a45403402420f14150604100c29103408121720100050300016040403040b4004044c4180d081141d0b0251320880310008100f009810003400031504c0c1d440e195850f103d0000c03158003040e04101050710001c00c480c001030341c11000783d80c0001d07400c541d613030414170148600301c0c01041007035540b05d81c40004160390b84c1101340001154a006050b0710108400c03001003945110f00400c1526401e4244800400400100c0d00c80c001408111074014002300d81c080c1e650001e00c007030360230070780050382d540001006002c0f403031030308000643c0141351600b048000841d0010001c1c1d01ca000d5294441048035103c45040c04540d1002094014650024240c0341c0b541d444800c01400750300702d004c2c400c1620103032210040310f00601400c607034100c4007255030380b0745008607070f68045820340c001e00142c41e040102010070b845a0f030b80c0c56100e03810150708800400c00c0040403010040c1607500260080394800121418 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 633102275 1250 633101025 633101081
    0x703180b28030204030b04030302070609020402040609050118060234060f0e011707260a0b0315040203100e190620091f2003070309081c0e01030f02040801060504 71
    0x91071f03801a01400c00607200c0c1c0c228202031001d401c0202c0025481440000c02094150308000b580c0182c4e8070070390312820b002200c0d003940e0085c1c03200d0b1302441c3d02503440924004030b5101d100e000320312210741003e2130601490384a072502460a446412038400b04040700c0180350110b60060311000c0380e82092030100d003440500404400e80d07403009041c031810090400304c10300d8040c80c4a00c41c0112070324070620740f082038070f080c114000081544116852185c020300103040c0740d80d410301013001e000d1a0000d014150003409800c2201c020050508698031602400c2c072491070720030007036901504070780c003908010a42d0441e401034000d82124807c6c021294a509108040c40c0b520703610700d4082c900000704101294994030040581d0402038600c070000301007a0740704204840c42d078040301a003070302442a224045e038030761202c152a44503500707150015590881c5205440312140301d49180211544107040028010071220400340c2a41d10542143c50300e43c1d140c00040050f41000c0c410460710100810344401c800403204a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 633103525 1250 633102275 633102293
    0x7050d0203040308012c061009030206070503120903270d06180c060207260a120504031505010305060a050a0b060409230108031e0d050910060b09060703180b2803020403 74
    0x406203001d503620001942580b405440174034003139a0000c1403781c803600b144c60000d42d40da120665900401c030a044c0030809004000081d24031215030046030360740180c01a1300b0182d903035040d0a40c142e070140f5500a5100400c2c0c151151103c220041040080b007004036041070a00141381d980007000310f500c19102001880150521501000c4d016510b0201e050020001c251500c0c0e000580603002c0d0030429120b00c030303070f0744c2090081045030710400340f0a0285000b820580e0031a0800d200161294000c140010921f01d200d5200c5070b40a1131a040c00103642101402140207500213030000c8149660300e291420070071085a0800041d83c40340e48401107650b0400d0000c5440e030041c2c110304001480784400c202c8202c80310340143d860072410540304004920b4043d620301d555084040c1d120b43c4c81d0f4507003080403e900a481048850b0050068402403415103241d908564441d4440c4c00c0c881018a05a404120b1070104030062400341448421501d4040351501d059500320505840901450706c104000c10000301c03000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 633104775 1250 633103525 633103531
    0xf011b0c03140f0a020f01140408091c050d021b090402010903031101140a02120601022a011b06090209180714060c0a0c1505090306040b07050d0203040308012c 70
    0x450010948584455041d005008001582c0c6070f1100100d10040ca00c0d80c0040c1c1c4040e00d1000c41c00070700c00e41e60440b0002425001c00d070307400b81045000b0001800c1ea030070403a80d40c844081492020603100320182d22818202100582510016040712041001d00340c150304c14488040c13011101800c0c18142a80003070704125031403000405018100700140383c3d503c820340c0300303109500810f454ad20399490190f1070314000390302401d00f0b2403820700e188020400c5540700241e403007030000718141c100042d202c04e59003540c201c40c001d00490381003090380c1c00801501c060746410f122140744520b001007940da00620400c0204038004082c03a034002c900007040140b40340001400d80490310740d141100350f040440404142288625010b0038040c0c800c0200c008c1c1007001c40900d0343e04480e1821072661240f42d01000458061280c140600e52660080c4080790208410202a03600480c444c28038074500310300c02809000f40c0e0411501a030201d00e201c401000b104850071011154210b002d4101000c4494010188450f00c80203 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 633106025 1250 633104775 633104777
    0x1703070311030d090c03060f051b1624050708090a06020a030603050d020f060c070c0e070e15190f20120f0408070f050102060c07020d140f011b0c03 65
    0x9003041064000500485000741d00f1050140035502807801e26011440030f601c001c403a428540101400702e01c105100b003902504800102400880904030009000d4021002025807002d2881c0c00c040001c0d4480901170440c4076020341c540b008550306003410129500140003905000ea00310402c100d0f19030214a04c5031480e40901c0058031080401c41c205d0007040c0b142c100402d14420001030310480d5070001800340c0c061248104070342c2195110340c3e059000d4003a101009110f80301c201030900490f000c40040b0303035010400b4940881106501000118240b89039000d101070b0b02c1001403207100760070391102020380305980d500f0800f032941203002e001883c66aa00700081113104504001300c0741d015003441022000c010b8504056114122240800b14a80c01407080880c1407240c003d00140c41070641e8214001c50714141c01400103650b403007440001e1640524412a800ba00250b80a0006441030305055002e006580040c105e0030f100321546821594000a00400200000111200d490380990381c180d1707190349 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 633107275 1250 633106025 633106037
    0xe040510151809021509040e0c0d23070b070c050303030c030c1303230f0a0320010f020a0509011803080a030c14030f10090912031d06010e010f17030703 67
    0x1c502c0300c00000305441d03c0000d5204d060907040c40c0384484044c0180209810454041020381d07080419170baaa222200d1b64103400c20010716002002c9001c448451a802c01c800051030050140c0d1203031581011045d800c00d013a100f0010810310306001035412103101400c810780007186076040104e00380c803540c00024000100c180001030249241348030501030000075544860b614429011900c001c108a0111184c1011184210840c03010900d00c0050182c1101d80c25403a10b1000d04c04101e1240d0115544200c466402c0d03495048201481c101880282138000b0140d070b07001e842d0b0400c10001824200b1881e45080c44118403502440400c04020440300c0003851401c0000f059001007406503401c1400b50000b0716a50b03400b0040110601741041014804d11106055070350700b82e00c032070800b0100c481c10040640140ca000f9080d10006010b035001002c0311a5200e4010b8076107881000e9945400403d070010801c403003024004001101d0205207410141c501c1041803204140b25502e6140d40b8020a0809020000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 633108525 1250 633107275 633107309
    0xf0206190902030a0303020306040f0902090c070314041d0c03070210020307090e0901020a02010b061201030615180c021009021f0908030706020a081320060409060e04051015 76
    0x1036101c20541a406819070f80344030740d02d05018000350811240280940e083c41d000154100742482849051a4000d10304c1e52507480320940d002c0183c110700b000700c1c18440d5954007000c40700c0544029100234101c1441040c1807015080c0c410300488406420f5810191081c1b080c40701180d000b20320100092295540141c0340c1d82c0d48142150100c2c0e55903c0f22040c0c440c48420311080300019001022414150b800034829201c0342c0302031045d984036040c1c500403100284001072000a031290001ca800c01070800303070422040d4440703164000869496134004510340ea00d00c02071810039014040c101c4400904a8100320b060000e0f004504488210442c201c649184c030340f69460164011349500010340820802c89480300e40610340300c7c2c0294441d81d40c98020030704400003d03031000c0030241c3c10140c095200c4085606030440382d980385103051860840592002c0240000f08010b2124402c0740e0040010142c164500c8c2014107205081c40000c001c240c483c00d04010b5401e1032180d40e0300510084610300c0900e010025 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 633109775 1250 633108525 633108571
    0x70206060d06110406020102071103030a09090e010212070f0e0102070f030b0a1805030408070f050a0308030601020109140106050f0301050c0301121104090c031e02030d180f03050f0d0f0206 83
    0x3c08041241e2460000126011840d50350560160080700d124451845802458404055407030007050342243c00610519000d0100d9a0183c2080191070765240000d420300c124050400300d9080d00310f50102c0080c0e0f0215032101172641c02001d01201c40000c1c005890030301e007421244c0c110f0403c0c5000241200d00c0601c041000464070364403e85100076080d034420801c0c616450503d0700c0c0c0d0f120780f00d8668144201e100c041600b248001941c6d00301d441c004c02402880b80b5654421515410040a690540d56a03058003004a025628821918a00400002404c41c101020480700c0c49641d12114026071420041242800c880012207055440c1801420b039054940c0c540742e1120651080510381140c08c02d8594000c0140842141c1c0aa0344146107040a016035003444500d034200300c8002a44c0f41d44402c00054810307000d081c0d0142c64000c00c100c40c1d09040e450300d5141c02a100198000c0700e0941c0075019004e024401408030318000d024030b2034404229590be1000035036500018080f90150704030171800b500b8107 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 633111025 1250 633109775 633109781
    0x1a010e0c130e250305010807060c0f02120c0307060503090d20070b1305060c060c0f07081903150f06180e071806020a080d0504020f091501030c08070206060d06 70
    0x10401c0c0d40e400c42c081e140441d4140d80d0000155001c00d200031038030200700c1c8003900901519060705c2e0303148018102103184c004126103a066089042c3c030034104400d5680301680360044d60040b4158084010f00e00d58241e28180740c03914102d6449441008414801d0010003000800c071b081c00c16000e46020840e07480c035000c2001c0c1400103115010318900c504080000d51104107000b40400101a8101d4045140c1c7d0300d0501505100310138112a0303e07000f480004903030b9000d44c005016100803103c4554204006d0741c0d17604026030f108601d04071008010b070703401e494110307418002c0450614550a031080582e1406c40c1c800079000b40380c000d43c0c0c20b02c00c1c0c401c40c000c2c0003440740c1c40c3d4000604240d03450468238205880040c0200211510b80011100038010104016000003650070705c3c954080c089501c1c1203201d00c4080000e080c050300881e4469640d45060102d03948902100740205018070055901000550000d81169241090407092000c0b03403081010660b00440c0d25540b00000740c0b04810030742214070b404401 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 633112275 1250 633111025 633111029
    0x40204060b03070c060606090806040b0c0c16032a09020a0315150206061012020711030106030506010603051e010308160605180129060a1b06091a010e0c13 68
    0x71200200c20800825403000c0407410590054500700314294640c1401c94480481e8020a40542e00201c0801c0018400ca50800d074040040810a0b061000800c125401c0c40b000d1024100740c07915042061043c4080744115005c1008601c164400702050041280488001885003108240c2d0115100c048140030390480c12038182614205040d1031f450350721854403035000c1404000107216883c001050f42c10b0480400d0b084000d25140c25116504401008000e075010540c12034903448042000281510240104009180b044010780255818944018100c6200410700c8c15102e0340400d036102c0340215441010b0559400c00300f01a507500d040c0880705264020f45600800c114504020003600c0c03c16040078400340c066440c000e12070040704c5840d441000103030364003048040c4101214180030b440c0070700082c0304450396810071a12091040007085014400c4000544846840d4848c2d2010000c02c0c0744800e49810002132441c049504103820040d80313000040c11703407541240000c0c0f201c0d4003e0f140c03c80800 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 633113525 1250 633112275 633112289
    0x240909101401061b0206090d15021b060c0a0c150209090a0b040e07051f020f0d030902010e01030c3608150108060403021207060f1d07061b0b04020406 66
    0x100500d41c96140c103005070000d02c83c500000e5400000582c40c400d980400486503038000300200d0404110704104410103240780001c0f40c0c0c84500101440d0802c82d140086c11645071040200100043c0c010b001c941000001850f0064100c2e007040700814103a042310703000d07120356045150402c8202405901c440203200d00400ca9500c440b03d40c080081400040c1c1110040030341c1541d00340324041c400340301c450f41c4030207502480354446102040d45541d0f404031075203030600c401e151040345d001c0807040900b00d0404001c105032800298075940044155600310303400b00c00c03086082c40c082000409848000300124018240142085001242d030505016800c0b10490342d628a610045511a130b00c00c5140c1c6d45071500c41c51030450210010000908000102d00144503e8240e00079042241c0d45202c0d40305030307900c40c2c10304640050ba0b500740810408410320941e540f40b5a1071913142404080342c0340407450a641c0794800340820a0120061603001041d116034181e070740c0e1181c895a0700c3e403210b100150103001d4541140c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 633114775 1250 633113525 633113531
    0x10c0b0a050a020c0a2103090809281221080f1b0a020709052a03060109031a0a0615020c27040c030c050d110d050c060307120524090910 60
    0x18003400302c1078442c0751004100100e2481d07102d02d8130100341c054686410000d00900e09c103000342d1146051814200380ca481074550031f02002100c0f1b10250306e001d019500113806000b40744084904000c501441844229030001030301e0050001e400c8018040840140741c19034210f9074101044105220003210f032a1045550a2903448890200c0025980c45031344c8545280c10f420310b00491150416a900204410035180c020744c00c076449031040910f6a84085e081504004000d000000842d0f0180101040d420850400100f241001c09910041d150301e60084002840c6422050155940015051060b100191011800c01c9468029412075071541804919080e15080c00c01c03080110a0400406803840745c1640383c2000c0d200e4040c40b0302c100c1c0c0e082700205031030260884002686003280b0081e46c1184581e048030300000944020400c213400a0383c0c100f001c640c45140c40460003020b802041d03400782d0301b24071110340342d10700524660040f2400c16042c1d0103040d400c00407a030800014403224400d54002c003014 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 633116025 1250 633114775 633114793
    0xc050c090a0b090c131e09020d02030a0e150615070c08030702120c01050703050913060e090d140307050f0c0f0c0907020c090a1104090e1b010c0b0a050a020c 69
    0x3028002d400009442900d600303002071105500102902c05540d040e502c41400c0d5424040310100c050a0f010b500c4520700580c8034005038100d02c41c0000e00303104805480c01351322403c6c800c40b4142551203103800426207811486241d0080010300c0985503028401303c8143c10103038403644421620707129500c005040e0030114500070a0300b40c4000000c284180c802d07526202e0807000c40e10f800f526484000c0130785001500c20004900840d11840240114800081180c910140c02100b040f080318401d40c807500300e10568600b0420000814041082040f5641c1461000114012129107071f82c03000030140801c1c094081140c0d0001c11011051300d0580040100300c514110140e405240e6416107060040d1041c1b40e010300050307034a8408944090007110107030803401c150315040300e901e002d0040401040385081b000d1100003141001406076071001c0d050320780502807c901c11400381c03054440304882a410300040041420000b1045c0c66455400003203d03c000071a40c4440d5a0b6101030301c038505180655200f00100c0c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 633117275 1250 633116025 633116041
    0x3151503011b090501050301080d030c1704050c011d1507030306030212030c0d050408030d09260403050d050702060d1505060f0a03150501020703060905010b0a03120201060b0310060c050c09 83
    0x102c41c882d00a51034000c2071035a203c00441e0b10340320034084c0112075001030341c0c40803c1ca0302a422601d41c60312181080340b48071000c500c4080301d04004850641e000d50004101c5141540c002e5500136440ca0842888580301754131801090318080c0a0103e02c0b070060002030440c0c107043c131980c040b030701556000740010240340c000b0071015925007018890404a004091288100c107000700c08135070858201501031400c00104507480c10003080c0790303101551020701030003403444140c541005180310030b080160900d4072107007541007603440d01c2a01e03030111040c0001003100740090b9949105540301d4240c10400808c000b072540580d440c07504603a9200940050000c911b10080304452740c00382c1140c0129640400411158801012400240d84a15809a08039110920201d1481c0d0000c5031a64018800415a40c00080100c0e4002c860f5502c180e410614841101c0d1842d9070a000e4100141150707140c2c41d085041002c820100d411a074030940003441010000e403020000d042c40f12480c4008020001d0480d8900180 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 633118525 1250 633117275 633117311
    0x30c050a0512061c08070b06041a01050307020106030c0f03031803020d0b090a06051302030d03051603020705190c0612020403030512062103090a0519141201090302010b01030b0603060315150301 85
    0x80122100c0107d407001a06500b401e115a44c00500c4c0c4182031181c2105600040d03c1550019140108654031001301101203210460b0020003001e001c1c0c0b001110920354103005122400c084800c0081c274905032408c001503552a14010b070400d4006102c603d6a40315440c0251508034031420081041d03061508021080c2070307002171400300314000d90541761404090f8104404a4404441201c0c0c0c101101004100f010311a5002d094414420412180b0800580d2005000700785003210031210071080d04418400700b544005c08510220b8080019400c6c80d00310354014055004450b124a60301c4403000002c1c0c0f81e0f0b650394003101e00c1c211b40d1401c1d90350103403002c0100b08c0e1030707038003100d08503008880d00c0000040c60b083c0058a140d881c0b920a90262106c4d0902143d500d042c0c120030f000c1940304c81c60406008995000f84a8000300758800c0c0c000254025035800090107503001d0540e4580701ea0018010002d150b280460728036080e1841411000503943c1d06a0001d01c8040e101000907099880e00c0c1e45c4651652002c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 633119775 1250 633118525 633118537
    0x1e0c0f0706020d120509071a0904151706010f060c020112150305060c04061e11070b03041110120f110d02040f05060c0d0804150c020d030c050a0512061c08 68
    0x1a4401840c00d842100380e02c159030701521b08814690000200b0801030251420102158203000d501e07500e0000d03401c00040903038134000d140c030941070888482088103008200c034003000c001450002d00b00642c580580032440d05441d00c075a40901410020503011a03104004003103d02250280400401078003000010750342405001c101c034644500d002160341d9102900a0364212001d40d9281c004070807201032144c01414030080d10b44207002c21030700a50f000840901141c0b016101980500c2e450780360600f007606125400e202018020156010a40d03040380d40300750591801300700200d003c10440c140101c4030004005240110740d1101000c14907040300d0203160002c00c00c40780804d1000440030707242c0e41081514892106011903981c0595000301d15107000d2518281d20500680b0082d00380609139503c6425680d1000e021340040e0014102c40c40c1c210f404d842080801c2a413858258244020f0000c0070300240300390f60fa2a15186046c10016040b5513074101c269101d02e81d41c14101e280169186004d1046802003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 633121025 1250 633119775 633119777
    0x4240510090209102f0a03091a0702040c2a0309050907082202032b0e0901060315120f0308010b030405120a1806020c1201021e0c0f0706020d 62
    0x14403002544003502d00903100c40d604020040303038880c0c200880030340c1c14480000e04411928001c48590b44195805002c0760150990302002e024030742c1d9540b800800d04c00340c0d901302405050550200c0c208024170700054485441e41900e0000306c0d4800d1a1007559008014080c211045116025050900c0d10070281040c41b00d05c662906c0a01c1d81e01c030400c002100404a458070002035440001405551881011400100c0803040341c03030598000740c0201342006910482c07000710104030410380e5600312003803403100000b0b0841c0c42c00c45540d02180001540c044018403030b0300209034862140216480d04020340c1e100820300b000104407004500c4c50720601019186405402048004000098078900c41007146d201d0350f40310001d03000c00c1c01c000230410495008511000b0411451003003500103160b83c62051009058240c000b008030503181002c00c6002c007103014045015074010f2080d0382c001100e03403041031682c1c61000207180c1c403102c00150b085d18021000c261100c0c01e1144200025800e44c012a481d4a11522 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 633122275 1250 633121025 633121051
    0x501030e060f060609060415090e13150b01021e010e1507050f0a140c0601050301180c0509070c050703030e010201050a091a0a0b12100c02190b042405 66
    0x100356882038071844101da00c494045501000074443e45400c400905c041e480007170505082030707154140091602412603026020400324401813050a101c1101d0641c0901214651800d42c4225500c01da0385820700602c1d40070854442c80c00050784d0f0f0007813205001e00717100000b011480410b11201d00c0c2c041c0080c1180300d0030f64083d20411140c00709400c8000c5103d80c210b51950b601c1e00c02d031128105400c4d03201d100c8a004000303000040c800994090002080000b0845004000315410300007010b00711520170900048400003989200002040800301c141218011104490240d8501c1d5041d20211605c81c0001d140d40110040441003540002008490b02c1003a4020002071b40c800200c1c400f22480c4140203052140980440c0038811250703071003d80c0c0500e400001160342c0c2d0b0480049081220f4458224089803c030707087c1221036800a1103404003084151001307000404460703554801e04003c0d80790140000441c540000d080c001c950400c800080c09a1000c40003440405940c0d40083c5401d90b10010b40d060 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 633123525 1250 633122275 633122291
    0xa0201020d0c0f0206041502090607060b010908010209012f0d081b041d060118062303010e0624030a0605030606040903050405010c260307110a050d08070e19050103 72
    0x1118000340d503415009134009024507203480e162009014000b240d590800c54080140c6011625038001908245100e00c40105808500314005010b0560b1500503900e26031040c010420b40d60f9028120714030781c4480308146220040e441d6212054582d08005c02d40b40c0d0303c07850b4203d6401942c000001c40c450b00141d101041d00c0d2800c18103107a0701d0320a9108060354078840300581402c80d140f202c022a00802d050400b002e07082c04002d00d285001025500140109401c000144c04902800c410528440201c0300d00d24a190b0510324010010070f00908100e015542155401d07050303401d0f16001c3d020707010005103c20744070310b450800c10028001c14000d40d030190180c000858454242401032200b91a4140c9a050a250508004480302040f40105032078003940703a5031314000c1d00d03a4001100e5242c807000d400d5940d00d1610102c0a480714a95000d2030b0030341c2d440101380750045030011844824101c07191400f101107803503a5a007101c1841d200e400c102c1d4441e0300c8000d805008079901003a401118000c4e00d05000c0a4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 633124775 1250 633123525 633123527
    0x1090206070b0f0f072f0a082a12070c0b13060f02010504150519110a0809030403080a0c111906180e010315022101140402090d0f060f020a0201020d0c 66
    0xc1c2c2d1301801150800c0c5100c0c11b0f043c1032403070540551103607000c201e49400202d20b0b168540343c40d04000790350a04001401042842c203232140210024500c200c0d49412500c0516002d0b5030b52844480e001d0a10b0010031b07564100a001c00300040246404940a0340f101ca5450601c0300700c7d070191140702c004c503814000b540744850060281c6031041d070f0080f4003a5290071680c5440703000f07060018074203070008004244040c0344488a11403101040d1034031000310307224dc1009501420040000d041c5c0c00c141da0050100700005044601100d10200452a1414910a00d403901c24031109003840015480300e61440c11080c4285410504070440e6001e07034505003c0403803c0300403400c1c542240204001c46400030014004521522121013014030041d42c010b1505016903a00044040d4003609292102c020400401640c40c0e0b40b0000700912408650851802030814000b0300c0802140c50010314410906c0d50903006e0143d81e07802402d5840f02960306565500080310024000e6110a04003c41d051400240342011 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 633126025 1250 633124775 633124801
    0x408070e0a0c080f040203070504151508240a0b0f19091206051801021201150207060e010e0f1302070b010e01080a08250308070201140c0406050c01090206070b0f 71
    0x41400e0b484603d815210700c000c6020035500208240e8040c030901c40005003645070744c458001d10840210042d4000360410350601130050b514104a800c0150027002d10503032000440440820613401a84541191200d0010903a07001480e40402c9410380013282880024031b01400500381c541204024004000902c60b0560710b205050140c0700a03580e00ca9400340010700541e20080d00040c0400610392507180e5640e103142643c0c0441c51287e200e030314000040200e81c081c80f5107400210402c1c00070b41289801d1a00080c44080f141151078100480801100c0300d907112502106c80c074280180c00344160329007a060000280d413218004441d0344060368000103041d01c01c0c440d028103a0790200042d0000c030945807980744c525040801040341c070a040340d000c00611680544090300c090b1094840030507501e441d40e40a42150002c0140700e220000c1c1100f0081445c9040c0111030030b4031010708180b03031540c5000d244140181801080250400030000c2c12405000b44842c496118000355462107405d035030350743c03000114 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 633127275 1250 633126025 633126041
    0x2506030b0d110d02030109020409060c02060c0a0f030c0c0515070210090206040504110c0304120b06030a1a091e03030a0c0f0801051309050d200c090109020d020c030408070e0a 77
    0x58200c5400c0095000c3c6403034540c1c00500e90000380041055401900010120341e80c0040c1158032039030790001c5114180d014030015510920140d082c03410504000d00c0640300c40b0300c1c12001c0e4101640d461101001d42c1c004e103c0d400c0c445810408a51000441070036450780b00c0002e4805a0140c400c100c0c01420b00da00c24054040043e43c00303080c0382c0c1014038000c240000b50010070100c1800318800d01054652140c1000070700001c2c11070740480d82a08005060200710820040d091a00a07044441003102003010701f4092825030303c180060a00315998072608505200d1181110301e030040500d41d82c0c6410b10781c0040958003801c0c21403010040c1500030007082d550104d52046e6500072a0754031004102234a89141000c41d45000c14401258420180d0384030303030510900c159584045402d00002500250984900b080b20f0b613081d000405a094081c00011000101403041e0954590001a48910a01c143d01a500500b400304112503c9607243d048883d20303403816015141343c0e99801c8000410003540b60240b410 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 633128525 1250 633127275 633127283
    0xc09031716051507031a031c031b0f03140108060f061507030905120a0c090504081303050312060405062214010f090f050c040510030e0303190608010c020d0c052506030b0d 75
    0x200c083c8c4400030078544520100c00341040c91b50303400407032400044483e50307250742032080d9840080304900b004018040341d95070341a003140c607d841d4006000700c0c600003690f01d03013142c0450040f55040e0f842c40000361070400000c640e652550340c0840d4540070150010b01c4441030715001c40751080840400f01c41103075111107143c0040e20b0b1840f450401c03c50301541c1c0d8082a0480d0249960340c1ca0b0020b6090b45034000700706688111000da0000502240000241400d079400c118126000d100d942418400035954290100f0081e4444003e030180c000b00c14099440202090300d81000d00f0003941e92500140045440e84c482c6d0300640f0708000001145004030711032648951012107110f03042c1810201400b01100e515403960081c540c2c0c0c1c4868051803441000510702c205000302c241c2c040542c1d400090003e5603c55804440e1583c1404412009141c0201d500f40c0d900904d441c2c03450400100b804e0042c6051500307101d03080755000e0070490803584071045107110141c4607951414000000c0c11000d0088401c40c001d4050 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 633129775 1250 633128525 633128533
    0x20f0c010f27030909060f090c030606050a03021804090b01060f0302031e040213050a0507030e0a0f020f03030706050c0304031706030a0b09071e090c09031716051507031a03 76
    0x69860742c420800c03121410b000340b03400c1a1242e190350300e80b012500a41c00c000920b65202c513040080d10400d005800c2881028501030150914081001c3c1007070243ca642d800900d034010131380e020600d0020310440f585850050085c8034107450742c10080c003603100a002d40030008151004150415001c1d00071a402103102c2400c0b598a10900310201d84c3d8418051f004903400040f0100100a442c209c1c014580100b9200d00b000855052903480542129042c0c2c40302465608a0301c2c00c1808180c0200750703240504d80645084442886050000b030842c840c141c00104001c1c07510060050a601f01e2015611503480b03511041c0503248448502e02c8000e000f16101381e4194005c141e0b030300009030123005098100202c5c10448924079240e42482e0010044d130a0003492318002d00c4c0e82004250f40e0380c0140450700c480c5081c4070706c6043c119204c0038034480f10b1011420301c4000000d6155039062038640c0149881d6004410344401400c1a103401c1e030301600683e00007001034141801804101e41c2c03940e1880750308400030014 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 633131025 1250 633129775 633129821
    0x180406090f0b0d11010c0f14070501080603150f09030f031005040f02040e0403121d0c150307020a030f170c0d15080a0209151207060915120915020f0c010f 68
    0x1101c891b040084100d40d416210a2054005081c0c11040d500070b80900000d040c01d1340c1050001045600010700c12846940010701e00400491286041500304084a0220b600d607940d44640c1381c5540318805203050b40a074000100700019400710646016502c08031010320034100c100320003c0c16802a4058102e21901e8203000c0740000740508105500c103461594085403c8649519603032100264031203114042c3c2080015544074505009104d00c4200f640000609500700200f000759202203009000b03041c00400c90400c0c81503801100100010820442603c8640c544000c0303903030440d084203062101080c03c192070a41680711920914058404d00300051504144580800004ca940075144100019100301d07c50950b880f052480c00341c00c4481e030020640300e4a00000102242c0c10340d4045485011a080c419422503032201014016100100022800380f58500342000442c14200c0700030680c80c4002024055010504058184122601c008014401c82c648000c1c081e00c00a50318081e03c10f43c00030075 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 633132275 1250 633131025 633131027
    0xb0f160f030b0a0302130b030f0109050d051b060114030114010501020309041505030303010b03070908120405060f0c0f0705180402060f0a1403100510051e180406090f0b0d1101 77
    0xc008807805000740302c030b2074040e9244c01241b05650b0b041c2000303480e070307841d410f540c4190305080008014136029280200040c1c20140c40300b0340c503110305000d42c104018001074401000325001d440c01d10450450700640301c031940e450304030425003070031820036074041d50a08141c5050340d40c240f0007040c12204107030040c43c608210041004000c00309190074000d50030400ca00841c69031810030145029114a0010942d641000e68001d0500410356120b0455648030030b68007000a00e20030155000ca03001629600d4640f07440341d4003081a4040c6801300840b40c825481042c10000c0300241c12400c5900964012041003410907030220311160450f8007940081c1c0800900c80142c03003550040201c04503505c0c0610300b03503615540003982544103480400249521803814841480d049030020044581c0c1d0420f00c0c9081851240c2d0140b5400e240c0300c19a0300b400101d008695500d078182c1ca00028a8020010080c09444160800040c9003060701c041003242380003004109800c0c00c40a458100d034212100c0d1641d5060000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 633133525 1250 633132275 633132281
    0x203060303070c0e04060b1c08030a06091506030507110c12070e040f060b04020322023001110c281e050d030c050403140703050a0b0f160f03 62
    0x110080d0980720801050b8045803501249601800250f418524142170070300700003058503407030702009118038011000045160a0b001d608802180e100c0c603e10f4481e501c01280200414030b9500c00100c3c0c0342000814003c22120040540c162501618101b040ea104c680e003c54050010300e40000c080d500200391100c062030011000e40501400e101241d031155210303c0e103458040c030141d40444510150305800c034208407090240b00810031040d1000c40c01c3d49000c04103030307540800220066840d1040075112000b0754561030031000b00018031403200b00c81e1041c14070360101140040d2194943e954680340b0300051201c80034049400308540e03640100040c80d01030300c401590400d031240e101d00880c90303000c3c504001249504440604000f540121000c3c90781c2e03042c6282403504100050701003502c3c1c044000034080d0814141d42c1983c0e0090312800c0c0040300c0005851428001d038001800c00c2c450403c0310000c100c40482c0342845801005240d02054658460b00112045145031901c0031a6811202641040c0710358 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 633134775 1250 633133525 633133531
    0x17071409040906021c180308010909050c030102180405100509010611031c020a02010f1e0c05071b0510080603060c090105130e01060f0903050c060c2514010f0f030203 73
    0x3031000551014503600d42c3c040368480680201965650845d0b9801c02c13138179105001034903848000304141014140e40040007510140a00461603503107a4600e400d1200c100008084648003600071961102082c16060510200581440c4030b41c0c1070000254003148500e02c02c80407140c0103030584170907909016003550100340030907090700707184000e102c401665420804014160001c07040c00503628201c2180003425a0700004410100500f02513609003007082c201c40c20500d1030b5134a04002100c401d0701204030f8039440381000203055011650408014240d84008550440703500702c500128140c4002000c1d03c080b4412205035034583c20000001f0383d0300300f003c0c0091980c0c803c1450031920f000c4040ca848a000e840a4201000c000a290014014030b50403c100e27082d2191682003003c0035502c0c5a603aaa034982140008078001c0c2000f0400e42da00c000100300e615017081d50f410445580c2c1108480c594820100d40c440c209007850105450744855000e01c08485502000ba907076402102c1202c40c06601a50000d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 633136025 1250 633134775 633134779
    0x218090c1e31030b0c0d1103010e010e060907030b13060b0c071203210902030d20010603050a02190e04060b1f0e191505121e0a0522110117071409 64
    0x400036a1042c881e180305140c0d544208001d1148c4950400c24441c42008050b00039111b400c200350280420f40e43c0b10024143d001c4028603001c03907031090340400304280e0345441070410a0142003800114042410f0806000017400c040201c41c1380c1c8d6038601880305170103031144001d00407500c00e514032041d0001c110f80315201e045011302d010455000c01e034046403904050492100010b141d0f0040001100506040400c100f00036000134480c8a0a40d00c074251640b404420080c801e084c008403180b14401c0e601c031410024070241800c0c2400e86840c0c02c10034090408401d141d172240002800307200400ca403401d103901c04900306a5a450407061500d040c4268940c01500107011301c00f9808001070389003500d0307114408012461b5181511100003855900c3c0c80c010103803c04580a541c0142c5c0703803070f2002c444d00d025800203191001040548460004a41d88010024481d121960341c4080070309000400c01d00681c04102070b40c2ea0f4076175035400c5056145406c0d0903504c3c4800503141d6a18100701d20007100c090401c000300 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 633137275 1250 633136025 633136027
    0x1060510030b150a03091101020601140607110306010f03031806090b09040b03030f12010b030106022104081204031a2404150620010218090c1e31030b0c 67
    0x3c00e54001c00e642080318131400007034807122803104211403805c40c115184e400303000600301541440192000388a4042199001c1d01022600c0d205100c001001030036110f2014041d9982943c41e00c2e000d01e06282076004c20b42c00b0450f519000010141c00c402506c0451b1240d9075075410320307801c050f8010450341c0030104a0394020b450b19021102d540c1e060009111440070509600d603690305481e04504480816803003140c5206050004101154012512800c4076030385208003130010242c0d40049030203010b80d822000141c0b050419510590310410b0041007613078020355004020b0184000c609a00c00c2d81281c160000c1c25207041404103800390303810b005da0403050003440400c1c204000100d0ba5543c0b640d56120800040c2d08625500c0c1c002490254602402900d4009504d8402c1a0f92503101e60504003e19600480d11340e000101111300c507505652012142c1100c980c400d03c50440000d003183c2011b03c28040c00c0741d17040c2042c07462114250400f00402c0760003511200726031940d22403240c0410028144460014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 633138525 1250 633137275 633137299
    0x10c0209010e01090b01050313140f0d021f18030305100b0f04050406210b07050702061813020a080420090a06180b030a14010204180501051201060510030b 68
    0x1450003500c078080c25910000201c50340c502190741e42942c0f001c0f80307402c0c14410100180500f044129800c00c000f10b0300420201c403c3c0300c0c80c02110740b52560b0003007110203030301951224045040e408100c2c449011510003c01189100c01c0c030890045520f00c00444082d521041c0000000901a4100c0d41c1c0c0003004030f00c000f0a1950b61003160000b82c1c03003040c451250440c0001c00340964a4140318540103030402140c170341c2440645100114148100f402c000e445204040002014070344104102d0300020750241220f13880c0c01117200070950019030902c2c0d040c4202e007904a5580e182040d4420b8034000780103590360005584031500c440443c0441d40640c000000940059405242c4500d43d807136000309441c02c8001412440d01c682d81e44184d45105038054424144406000783e039600203810890241c00031140c600034503850143c6130081c8603d03070000c10710704810380342e075078031051b141d0b0046040321410b80d41d4501c01401b0040103401c81d0001d0080c070741c0c00042585050b540ba0320a900034252034001801002d0548 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 633139775 1250 633138525 633138529
    0x40b070602090306090a0c210f061514130506030106030501060b0a080a1104170c0405340912030e1903210f110a060504030c021e0603070e010c02 64
    0xa8000401503610503000100800c40e42010440c09612500e800c0150251886540d100449220710381300d90301440070242c1c29440c00f50160404580c84640c81101080c0000803880d010025000d82214000342e914a44800503000c60301c0c41c00b00070001c0c00203144084c13400c034048065000740380241a5640540d629000403000403424810701c40174201c60303521141c5403c3c0c204e00007410b503400140002031807818040b80000c0b400703203d82501c007680c2601c0c2d01030904284110381c042c50f001e40485c4942e4070034141028000d001424502502800008a03050724861160058444042e8012103c290000e607181c801002410f5201e840d03404160b102c5e15001800d080e0707042c006152111040780450400c91811b40400400030055521a40b0214148100031030101145c0040c103242d00600d014024001c660703508002c440014070440302010340c0030078100401d083c1800d0050840e03001100481c00b940d110032950a2050290440c140154001400c9610b0740c0d4a101d41100c80041d00c041702410b1000e5003622400507 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 633141025 1250 633139775 633139777
    0x110901090204181107080c1f0203090714090f06061215130902280b04090203060f0d0f080a050c010c030c030b010504050102030301140a031a07030b0f0f010311040b 72
    0x80000100240e180c50810200c040d048080c840001c11807440c00602c416102e201d00282c45841d03401c50381b401e0b22000c03800c1215043c1507000034600b001940c00f03101401494190342c007840c0610140c00480d10102d403103c5000c400c0020074281c07240e0089116000440040c03519510300c0e8020b6000d40414282020903900420400d0195000c810800c000074159541e4141a10040381d0040307841d03414448c910041d00850850301c50406150031104444071012001605141110020100343c6416a62039943c0c042c604025001952022721401d501e0b0a100d585140c180782034081c440d006100081d040829984401c2a0743c0411242420f10000744010301a80c0420312490031320000c0c54401190101c43d070318004040394180d55100d8107218080c0f10a000a13640041901d0544a011035000460382d040f034002034203004c0d5603200034913200484090300281c0750b605051a02a45160b00c3c140902c880e45010400b00700b080d81c120a80258500300b102d81650320070b0708056001103085002a02c1d16480f02120211 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 633142275 1250 633141025 633141029
    0xc030603051905120403150c1809021206090415020a021c0f110601210c09020a020a060e0a08070209130209130203121303030f0e10110c010e0319110901 67
    0x8000200d4040d00f03010080c003031280b0014000120703618140c05c1d80c0d200c3d400026020104000350b50340b40881050940a04200000307075000c41d90000e402643c600b1440082c3d40082d207108002c1407004041410f6061149a80380581c0c4c1c0603920401d11600d4515200c0250414000002148513800100c0ba4482c10719600c0310040d01680c0e6501581041c0303440207010ba441744080b118040d440b030b0004102010941001e840720385510044011410f0a500700a040c1030301a4000320002440052558442a0005405041d05105e02424008803090034925503d4421801000c1c04448080002c1c00061600754482680514131801364544d00c22650045109a8012111640c960404102d11000d6290401410f10340c0e032000d0407010702c0c14007101c29000390031040c1d00c00103040c00798803140361100a001d8030030010a400042d0080d040da07409030500800d0300c821241c45402c240201007801c0303041d501c00d00400b95100c4025004204d040c00351004040b103025032400c140e030300607515032411603166a01850540 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 633143525 1250 633142275 633142303
    0xf02070816080f070f2618300d0c1a250201290a0b1b0f071a18091305010501120c120c030f14030703090f09140a0c03060305 55
    0x1c1084172903d031854034010900c543c1d0710001d940e68080c001540b00b40080758030f0262440d0348002c0c103100c14404a941030388501c0c1348135003031b280f80e08003136940001c800d0484420000d0a0111120b54000c0c410507200304548000180a01900c8040d1040700407154201c290464600c0312260990b840545481c840092001c02c482c006075110319000040861b00c1d680e455466408004044501c0009000030b411180ca40c8201174141001044000610403401c551401c0d00480c603099591054141040c02d0311002c490142c00821084802c1072880b01400d003041c2c4041501e2511103560300c5000303404010b1005801841c44012400040d80c85001074001c4c05a1402081042210701468410385080036a51125400c40000c2d07825501c844004140c4500412040f20380080c40018440341d14101003451208100d00c441303440c407001494004140d4403204050880c3c501e4203201203400d49034044203054803104900701d910048080042401423490740d01a5062121505001401c40e0303a80ea201420300c0d64402e040e030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 633144775 1250 633143525 633143543
    0xa050316030605011d01120f080304030f120911040509010b060708030f060f01080a0c020c0d0308070908010c0504090b131404110301060605160c050a0b040305010f02070816080f07 79
    0x81040000d00a0f00e01400703003000c40e001d00c004040520340400005104582c0311000c0043c0102c01d000904c0038a05406421441840c0c0e40c2c60f02d400c0c0a4100c10046607848000b600503c01035491200300c0c07240300c002a91164854151610900030032003d00b0010b00f01d944555030352820790300e00369150002006034034410302141d42c4900d4809000d818480c1c0c0105801d02950a0300801241680d0006016500040e2210f001440d00c4845004926080006022a0f002528400c8180525400c1303018a40310340d0403542c40000d82a15410810f0036075980c80c400401048051000b403105990300d030082c0c0109000540790890303662510362a102556100f0807854000c0d1581c03410b210501c140c0384100010000709034001c1c081c2602e0300720001c00328414042c04440802c8000b1480c4100701c2a00c2401c4001c1c0b000402201c4241e8130313142844440c2c0d10510003140d09d5031a000c203442d501400c500030b4906598010350054140100c0d40328558402481c00d40446d0500c030108107504010b0b02000142c4116070180d0981 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 633146025 1250 633144775 633144779
    0x807060906030b1017151c02040c09080606010c0204150e160809030421060c11160509130302070e0703020a03050f060904020609010c140a050c09160e0a050316 70
    0xd0b04545048481c00d00484096800707014035a0000c828102c2d0900c0050740a031240d603041c4000300102d45003404240d10445084101c02000c484811081c0050300856040181b52002e0380c00341c4411046201d6400603070080f1001551643c02032000da041a40090b2000c507034541d03840600034002020360448011580c060042c003d1014000703480041001d8a0304102c12581020720042d65280601c0c03113611101c580c80c50701c1c0c4c002842c2054024100c0c1343e0207102408441040c880143c85070562919a4000340309a0b600c0203c4003a42c2c44003c8215074029040c4420394940e456210710100043c10140d0075485503100c006007032340c001060a4400d5a2580c0c0041c2c40744546840201560005040c0c0c0e4030100d04042030044a076900aa02900aa4110358246e40c407551580180c503150b610b008041c000300111b1074005211000031542081c1648940159456040780c9410070508804c1502c000901c0310581d030003a1041c078012061390a0400005104801c2c1c80e0b50317900003c2c43d104c1d51100103007001c40e5520003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 633147275 1250 633146025 633146027
    0x31906081b1203030109051003320309010c0b0a02040f06020a03020d1707120b0a06030e010f09120c020d0206040914010603020c0a022716090b030c0d0903090807060906 74
    0x100c000704204680082040b1030414281c1e559000c18000e4200e600d81e14000f0030038404101c0c00020096a01240b280c102e9150080000c4045904a00312040345000c0200905031100102c1155500340c0161140b44611140f5203a105007020000c01c1d10100c10b80c03c02c03001c40d8a0b2203207407402c001000c0c3c99008160031780451400030f003810901305080c0280700c4c0c46c09406220601c0c80e5201d6911043d04d1501183e51030300707089070700c0142c250b0800302e0340c20141200d800300307200c1c2d0f2540000c628420b500c4001e20903816100d4665088605010011384424440145007411a214298104079140001e2036035021081c2c07500020380b1a03020703611900d0104c0d178849000d074500200d004405d00500b0745040031810300c8003031811580c90307100041d8006d21402150507040050709422503028200803580259603c545868891130001441e04122080482c10310700700040c902884070100c900c11151030a5450401170400a000090891604100c0a00c61000e001040306c90301003004100800340c5035940b0000c00c2c50000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 633148525 1250 633147275 633147313
    0x30f090605090703051b1e1f0306050111060601080606031803030f040201030b090103120309150507020f07120c03080c03090d08090f09040c0b160501020703080604061e03020603190608 81
    0x40d54408101c00401856120f41e140c01c00d0004803010320480c21f15440c06800043c0d03c0c1781c148070301280741680d50401c004000b58541e000c1c6043c0c40b802c0c0ca400480100c07080e40d03999980380c201c6400d40012040b0000a00500b030010245070419410002212043e80d00104141581c00440307a202200c4030749020070040d9a07050040710002101512008041c0d411915030660078100340c40302130709042d100d8083c071003000303030140d5020810311000c27004006909210764001d48650342502c0c0304140c0d10a9040200e011003041e00b26854240e0b101d1000d1441c0c52560f521b44e141600100401056800b00b401000c00e0b88e00c03140c91401905109070341d95aa04c1c000c01c1d04000c50020700048150140742607030100000100c00e0212441680d0681c0c1c100e0ba16152480d000311621088110010081c1d40080b61490405401c40da0450184004480500100b83c030344800d0812040e26030782070812410b03845020000760600400454029000c102c0b0000700c1c440c0c41d203e0b0001c1e1000c0f03510001301d035800b40e15440d850140b059 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 633149775 1250 633148525 633148543
    0x30210090b0a0609150b09060408060103050304031a0903041a160311010c030c0e13060f0f0f0e091f11040b04080705060a020d030b030a0605070305072a03030f09060509070305 77
    0x6a000c115206840813201400e80041c042d255003c0c000140300d0202382d80b01401d0310010a01d1408239840c66841c0d28000b512a0040c0c84100e03041841112441c070300e200c80d0100c040c4580000f90003141050b151105580c1100c0310141001c2d40c1403020400c540c0c148500d400d5609545010b0f4841d07500d403007800070010342125550000c0e41c041600c0c2580200781c19602c1000300b0204001102c142003018031113281500144050f138031180b001d00300703000b001815500010000301210540c0c80498078a40e9038500420a40c80f0031504d410f402c0e0861000b40c55080c0c180342d205070704910180000130340e840c0440034955a540c0700b50000911180082000c01400d5810001304014020035141903007031020110b0083d40d44c0710081815801c4c55198242c00c031261300c0c100058080650004c0e4244501c3c10700c0b4030040e0051005a96410000d071070728000c0c0390b2071803101c40010a00a54861046100c400d82d0b00c0807002410240031144002d43c8030041036011070520300900340680d0402000e0040e0f40c2c91481c000c0e203084450 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 633151025 1250 633149775 633149789
    0x203030910051003060e070f03030c0b06040902011205090114091501080a030804150f02070605070e010c03050a0320040b03060901060c0c090f0b030d0315060305150607030210090b0a06 81
    0x4810091090180c0c000242201e900c01001b040420740444403074109a095040a2185503c0990002c20b249c0e200464aa1181c0940450b000366252071051100356150120080e010038210030a0707980111003503200640c004061000010010385103c007510340c0740d00c00c0e2211b5182c1d6100c484080b207520700b98040c0b14010030654004007021502540c02038040007000b04040c1481c0310841c58542200a180c00a80e009079941c081159652040d10b40280140300646402001514138011060310f54001c402a0602e00d40513100c190a1990040080300946140b0300400303801074041112000b400d514038003400281460000854807464070000f4004a06e805900400403c1017103030b040c001080e00c0314041410341c0c1801001050100048102e01d014101e50a201ca40501c2280074112203198141d0099150084681510520b66502c0d0030440c1614010348050491201c00c1080c1d010515000c8028410b562003801504d00b0a80c01c8001e000c1250b6402c03206503a42050f04013080080012486004054100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 633152275 1250 633151025 633151031
    0x20f0f100e0712021c05071d09061e060109050604080d03050f0403050a0c020105270906011404090b0a0506031f060507110d0305270f1822120203030910 67
    0x30b0901207443c001152a00030b0b006461201101c5841400d900341ca10032030b41c11104441d105030b0348042c0000c20a0104c5c82c2c07800324491800c0410100c6c080400d509019100c18100061041d030510041411507038098800d03818803200303c10029035511404060301c0189404005031030640440c0030042e05541e0001c040091100c04041080300007034214054508019052038002084841440182c546100b100c640d203152540300d010380707d04240d66080c0c1c0620784c2c0d410395403015103465010054883c46001c10342003e4a03072041c8006c0c0301c0070600da400700040c500028061107000d55668040b85035640103030b50a180c0d8841844c00c8042410196070804020001031601700d02c0c103085030f150204500c039440081c5118003c504034150030725110f0340a844103010290089200d4510b07600d00321010b8440544100d020b0792000b111110945001007078100003030740004e1544215942c248002c00703581110814200301c201c48a0392103010414000700304269a2007600119540c0c01c2c01c0614900e0300c4980030b010010241 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 633153525 1250 633152275 633152279
    0x317010f03031403070306050603040f02031002040513090c0302180a1a0105030109050a0f0e1b150f030901090503180f0a06090b090604030605132109031101020f0f100e07 75
    0x1900001c4640c3d00500b1204040d201d8a400104401401c01a030007140c0c801c001005220074891203400741c64056100303c044030640c03219070102c1800c3c0d00541c440c0c1540001c41031010356581200b9003008030b41620421500c80807070b0b100d50000c0e090310380541a02034103c1c1c580081181040451285560b00700c3e1050341c0750300034902c10b40020540e01c01401102d200316160000705115040d540c11041110422038828484c1c01c85a03041683c0d40c06850010100e5400001c400309000c0c00c1c00c0300304240b0010401c40e41d40c40d110440c0b07031040e182d610103000c0103082c1d0760386d8003d0b00218070240040c19165081c140e00003000c0204000f040180320002e01c1d06441030b401d46204010481d0010a0003040b10729800030692198502400201d01e401690702c0035041c40d00b0101001001c0c085805516001481210701054882035944031151401040a50001203110003809202040c070307118110124003014411141c0c00c2200240c05800c106103c4000c090035404800420030710310341c60050b0324002d0344440040050038 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 633154775 1250 633153525 633153527
    0x30203071a0d0905011b051801030e070510181d0604021207180519050909070308040612061701060503060a0e1203100e0f190e0307030806040b0d0317010f0303 70
    0x100c11550340c41000e965421070f16003001000e40061004000300000303110340721203102010741036a11191403840420307852600746c04998080d200d103075852407104000781113103030401040c40b0502500c50182003d0194041c0765000402c50381d00518080c103012071680c040701d101001c103e2480e41001d080741c3d1189005111700c41840342007260039980000d640c5000f107040c000a01099504400a400c8180c0200403138412400041c40081050120f60094407860780e16902c4141954452410703000082442000704010400944155884102e000311703007000240580e030300d02c800314034480e900402c106141d450300810805890b0601000b64092503280c4148400c26000800c6070b101d40303408402c44058440440400e485071003400400c070161001c404842c507581014200e420039030302c040703034600844071b000d007091740b5070034034034010380d403035400000025030805055079019910741200078000750b0080d5982d0300f51030080c2d0b148020319106500075101e03401110481541a040a54141c1020303224180f480030410000e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 633156025 1250 633154775 633154777
    0x16050d0f120c0905060706060302030f0a08040303030f2904050c1c09170408070824070c11040501230a0b1605010e070b21070906050a030b0a0e01030203071a 69
    0x590707050000080c0b05000c41030265104003082d009a500a40042007050030888580e0154040d40e000b2000c50340c2858030484900d40e983d0b5100310003005c480003440b040001a005c0c0c0c200502a503c8031101282c9940702e5000e514414180c461208040c02e46c648090035641058032541c2d4003c0e500340181ca25055241003101f04038019003440040300f6544000b4001400540910006104400c1503850b98890384c1e4000305544010a0040041602030b10101d00041009240e20307072252440340d00c00728a144d68644090303030018510388041d100c1c0d010b242d1940c9003940da02d22640340a0804003003100307580c044102c103407039018801006a600401032140140500112402643c00e800320809100319444040e207402c1e400b402d48588510070301c0c41681c0f0041062598000a1b0200c01c0d002c0b8101d90344e076010095221045802900c044010400c40881481001e106100414008105041c0840c03454030a90110307204541d02d41c4100c510045200040c011484e0034881e0100418600c003955004480010560ba01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 633157275 1250 633156025 633156047
    0x1403131a0402211002031807080610060e0d02040c080916050303090f12011e0c030c08071103071e1b1a090406030503070b1f08060a0c1416050d0f 64
    0x200d010060310f20780c2d80075001c00c414042ca00850605544a09014000c0c414070740034100240b03124000c40201103609580010b0082c03003850300c440507840c0e10340b0306070080c0d4020701d2010101e900320507900041809600c0d5802841c0c02c101e42e941c0d4502c5c80d0300d058926141044400300700e0920800d810386041000e40e400200b500d68108080f9001c074950501100020340d110180030f001080f079424440000310711030144925400d040e00c01202408188409101141110091140e04000c29001d1020a00b2984600c80344c0c000d0607060000c803460305441b41c840601c411405c1d03007010202100d02c1028020000110700c5101c9414060349841499801d2501c0c0d2404107250750301e500038906c000304001480c0d03511074014900940c2c02a0503650f0707030100f500b84048900011103001101c0c0c041c0010302c01a10718015121421075030000c0c040e21458442d201e0040c0070342040241c540c01c02c210303100f21003980c11000f801002c2d0011122170b0742103820f542c1c0c075120741804155241402800034484008000681026602030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 633158525 1250 633157275 633157309
    0x51203040e04120513080a03081b0a030903050f0c06060f01020708030d0908040504050f061206070c0b0408090a08250b0418150f080c0405010302010e101403131a0402 73
    0x3020f06121041101c260140741051805090303009400202c070030340070585000e038500035510300c2520381e1403035000f1080b40c0981940500d902c03403c01100c017445109500c02c0000310300c81c1c50b00910f0318424211004294101841c02156500880113200d0a0301e4a200000407441c400c0c006014014604400f6588034080c1d2540c01490f03548400000c0c003000703030403021100074213070051040140d801c0860500b01c00c0a002c8814900403c05002c02c00c100c5040001c40ca4801c00e1a0f40d503007070200006035100400e1000c007800468480c1d006005059017603655101134005000440d00500310041c0d11f101c2c80703103001890502c41502e206510320070700100a0f032904031003c0e10440c01d100d407029901040b0070001040300d0302e030b6419800c55207600407841c0007039103111000b240c1c400811540d200324980104412610284802404074035030703040c10400d904019200900141c2c142c100109142d01440d00070b40c1a80c4101c0f4503000031111060000c08108000c00707001c0c0c40003e0908903900790b240c10f60109403d5100204400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 633159775 1250 633158525 633158543
    0x1020a1407150809010c0e2407060e0303091203060d0308041a010b130f08060f040206040f24030b01090302060f09030304141c0807020631051203040e04 67
    0x80059902044a04000c180c804102040800c1c1d000b40200180000d40f2042450350070100324600d640e00c9251180384100004090501c0e26103010344501039148400da0f0ba854510090000d10041111481010603600c8008003035a80c0389020b092150030403014425842c0c0c91035080c4184003140e00d5070840b00e24210f916060030714013a10f450a08016080814034011040b0084400124070710548401030700030041d52441100e01c15440d070305008010401402155155840344000440d1100c051610035000790028240340c0c03405848000c107095001040c1c00c5208500c1c5c0c05119a5140403640d4441212030107545010031500d05a200020302c07038000c4d8407020703224420100f91400c0102c142d00441d01000d0b070003012680c0d00c80d502d454200039032440310540c500c100381000100460b172494032240c3d14120b500420007071500240b5800c0150b2600030400100b4203c403a460610510609060401c40c821000e40314400340f1440c110810401c0c7c10081c0c4400314076001400100041d9600014450304168490051 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 633161025 1250 633159775 633159803
    0xc06090803030112111c05120f030a05040f020607030e011805090403120e070806090f06010609091503020a03080c0c0f100c051504030f0f0503013006020d0c031a01020a 74
    0x211117030340c074115a04e0360701100794050418080c40c0b5145012046105c1e006880c2c0ca01005220448140142160940440810070004055501c664005640144107503201021484a9008540290080d85045001c101d088084c2c404640e001a982c2d5062078074200402566800c14020980a802c054002018003662003018050b021480d0415044884407204941e80541d445100c966640c50982d000c0740c15000d00703c040000081c0114070130381603403e02e8641a520500e00b454500040001c84d071604003a1380003807008001a920210150b0082d0b015180240d1241100382c035240c1003668414425126100030158910151181e0405110304800d88c01c000e104485541415424480c92642009c07011081c8410441010340207406003100c2591943e5450b0001c0e80c0480503a110f00c0280038841100800c001c5c4420364070090116010080707182d035411041744500d980e60380141d802c042203030b0f50802c0e15010a0051903616200b10f44201c0c004e03082940c441a4018000b030345407001e080010b04549440810b07 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 633162275 1250 633161025 633161033
    0x9010c0b040c1e031a100e0a020c0102040b0901110a110d060f020d05100e100b031909051b090417030603120a030c1b051b12190c06090803030112 64
    0x8900207000a00385070381d5010300f2a050358001c00d564042160071981c0700051000b01041c0c881918030440d02c0807203030f441d41c50400c00d00c14610403000b0070301c003c01502004400d9048400380040e10042860412442d141d03d10300d0005400c0c01c40b00d000c81c010315449010180080b40010340c1088200b0010f4802880e68205410b01c0006010b0850b003e0000c0e50001491041d9410b80d5070005100342c680c0398442c12820344039030541c414040c2c1503807030610442ca03420f402d11400c1550001150808541110040d044070700b603034030209a83c402031069541c4c1c1c2001c3c00c100780c1c583c0f51810002c5004002ca80c081760300d18241c0da96840c01c20b4840030351442e036580840016150385082100a03402c0265001d12038480d84030740360060140c20041243d40000741c0280b480080d40540c40d407020443c0e980100078100403c0c80d410040c00c4c441c4852441c5521500c1002c505030b6070103040c0428481c504aa40b41000c94811604001c0d0364202d1f141d00c410100240010101b01e400000b00c01c1ea41514040c5560082c034400d5401c5c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 633163525 1250 633162275 633162293
    0x1030c050f03151206090604121205280e1f0b090414100912120b1201021308120f030903120a0e060108030a0507110d060204260309010c0b04 62
    0x507900c01d41c8800000d001100d20000c001c0000c0c0c1c802112030926000f003000210740c03140b109468915a550240002c10000b4000b80700c11501c3c16110300d00454144000000311040d0780c01a51851580c550003030056441540a60104502c3c0d446104248203035140302da04950b580e90f4056101400c0c0c1c80c5081e0307595502c5a550405000d1f01b07402081584942480d0800e0141100c040c005e480041c07141d1544804980100d004002d5540d80056903150706c8403c5e40e90a480780006002d40324426a505c070083c0c0525a03c0840c0031f507180d500c0390001610b0b0018100036201c8880c89805c864429884001c9240e04186001c0440d214800c840004613202d44504440b43d01e540195005415010801c82c100203401e142a801481e010400c1c030308803003a50b42c0ea4010a17440f84102c2c114038000800420100c0082400412030f09046080580302d01c1c01104a511980d049811a8001210b4041c07100702034160181100302d040491400f202c00303945030501c078900107400c2400000300100040300702000982030059100c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 633164775 1250 633163525 633163537
    0xa0501050c120a0f270b03100305030a020c0a14060306060c03090a2d061b03020705040f051008070e010e1f090203060a0906030803010521072408070e01030c05 70
    0x95141511030f481e40300043d048480c0c086440000a01114180d0480d0066004050451107281d091415040c144624032855902c000d08540768030028074000800039004000600704004150302030011106940108500320405030f04c002c00c83c0300b041c0c110404582e82c0c0d0702240c0e081070086909550b03540103410103a003140281745506610079211000050800009001c00f540c41050104d50110a406964907025018440c010754001032030520550b8008250f20f00801c2099000c2e0041352912079545001078242e0300103014100450380c841041c000d09030341103008040a020074401038040da1781000c04030003c2000500c240c0305125485404120000490f4812800038003220409020041e1100054006540150782213402900d11500005808010b4401c0d0001d50340e11041403481c50746818204940d41126642415000c540150005071100007080248020120106032811440c00c0803c01c0d11401c3e903c0030341d4018001080704002c142c5074091038000503654242000910b020902c1802c6485000710 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 633166025 1250 633164775 633164803
    0x100909050703051504030908191214040909050607020303070806010804030e0907110f160312031e0c120c050313031107090e06062205060d200f010306050a0501050c 72
    0x60381300e100c42440c0c00e1406901c01ea02136245c403130103155508545565440120b031844c0c4802c141200d42c8000401d4045180146812840d2881c017507000e015002c02142d01a9100c0c0b49104e0f5510082000c100f018400c040c2c2c4420680003846c2913103040c24015000b034000030034845c10881040b001604060103002c140412420142021255140c203103070142c04164111a0160580320789250070a824800086049450302030340c0c80518081c2ca103070384010074105040301d0701c0d0030300d900c8040740c050134003030b11002421610019402007203020341140c014200d907040d044103090b10f50801604584868101c07040301e0b00060b00301c0790084045005d003403c660040e00d40d80c1203885409040710000706800c0b2a04100f0b070881d2940c09442c41910351104224183c2e805000641c03031a0700d081c5441190300520341c0040c0d481000903048940e040056600c840e003542d09044129244010071500d8482c0d814400721040102800382020000030b03060a0000b804a001440350a04100000405085040092104d142e103c801 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 633167275 1250 633166025 633166033
    0x4080406033803010f0c05160501200d0e0706090b0a0c320705030a03120e0a0303090b070c051b0105070c09062d0e13050d020106090f0510090905070305 67
    0x100c1000d04a0001058041c034425805c0103a42e10039502c0c0d511603443c41c40c42a0f1241483e21706074071148a02c1e00c14900c001d546035580e4a005651840b40e0030041c413595008602e00c42d80d54200c82101c1c0085a01c5044c814405600c5910240201c64120380d11100340d41d00041e005032500d0040d00101c83c42110500000e05041010b1840c1c11070401020301c3c00202401c00b0241c84440c04007540003541c4120394450b0581c158440240200400c1c0128041c1d0301d840480900412510324a065a40c500a000d5030101d002075a0b9404d0f17030081c801003034055508640d2501c0c00c105084c0e215210300c0d6031031180e440d040010400300396108010740e0040c0112170a00754081402c007c0325a81d0f8200d0760081a162050030110b00910348042c040040c034a84100000c9006010003000d281403000d8000b222900521020480082d200307114081101001000710024450780045622400e0803c410143d58002d50305690f001e00744001c0c405841100014102a1818100001a0b03012142005450f00725164000390141c02 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 633168525 1250 633167275 633167351
    0x30f070318062a081008013308070608010e07020105060a060302090d0213090605010b030705030412120e0d1103070302070b09010e060c0a02040b09240103060b040608010906060203030408040603 85
    0x1800c075400501c81c1c03040940340400c5e56550300001d401e88160381907950507482000102c24525500c802d0340311241c0300f9020a245180e03118203100d031900d01d154100c3d101155030b20004005a10024101ea40d0000f07a40c402031095082080208569148900603c41419000b00d24401141c0740c03905021070300e64006102c40d4824415000041c020407130785070f05441c0e00742400000f0440c5105c3c0c00449000d01c0d080c1d0f031454031395a034641b220361300c001ca21480a006c001c282e40085103c06007600502145d00c804074080c02581b07410300d502402022556400d40104e420501c030340c0000c0b030740220744441100c1c4500403242d503a91501e80120749901c010301d490b55000001240f40a80d04a002600500d0a4030907201000100d01d42e00070421405012070703400c0684508505108651036888180b0904d07868181800319609458210003400d50700107801040000b40d2000040203152254002c0c1d0005140b14009189941441e440345d072040e1141380034500c24961550780410326403160004000c0204010300700080d00702 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 633169775 1250 633168525 633168527
    0x40e030a14090a260a03051e04330e0a03142409010507180303120b0a1514071101080411030d03061403010501061d180903030f070318062a 61
    0x3c5614407030098041d00c0300603600c0b01c944d00050f144ca40d0b1601620340c6400d252541841101d80301c900d100b8014a800c0a2100007a0b0340801140301540079800e40000046ca001c1a075001e0300140f80c00421400c120300710f503680720180c4801d02440e054940004800d401c2e4442d40349043d20345045003400d0321020041010031011102109019070190501c035000380500e845206046a0600d1044000c44040250300b03010400a0f009101010705032040e83c4000c10180400710005030300c4401d40c0c0c022500c4d2501401404455540035400b14521000a900b040c104002c503103034262000c01c801d05170742c103202c11500030a0911541400d10098444e000301124501b1200d03440c020041c00d803a114100d914640302c01030300010f03d018081c0c2c0d03041c1c036000e13503400d02c40b24400c650640741c50f0800490b15030414850400c0c101012940c10501c0d100d065008010b583d00e09095801d100c13a502c0040041c402c061406001d0806907184102c410340c115007203900461100603903101e10502d0310745003d505210701a4442035a40307003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 633171025 1250 633169775 633169799
    0x5090d1e0c1502071b0302060f0703121103160215060d020a0e0108030405092202040f090605010b03040327030209071e080403111b0d06021b0a060b040e030a14090a 72
    0x2207031145c0380a00e8040401c1d80041c00d6070009000c0298403041c14051608458040d402400b40d0501924102c102070350005511800c6444943da40b107070340b210020420103000001010154129a148000d08068241c0d100407421000040c140a00c103011082c00201507644042c0c0c0080601881040e14010b540c1d50310109550ba4843d1265a02407010030000803082c0c00300c0c400d001c0702400c0341ca03410501000360364208001045912800703c8819903c88112011460920515000c0c211742d1690b69901d0400d401d015215030240c140c014400c85484603c0f8943e00020258041225030541e500102c03a15840e0301501c648003000d050b102c44003075140c1c84502031a1310810b0540628025101e0395240600030990b2070b1504a0103285401a98084100c100b5030b00b04128444c038414012000141403803440304a080240390305410360415903021004840a00c0520300c9110341c068000c6904209030301c0303003640c0e83da100e00460604d10b062240d440c0c1d46604000c902800ca818900c801010034a8080c2c07944071203490 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 633172275 1250 633171025 633171037
    0x1118040f050c130c02011a091f1503020c07051f030209030a06050f071701150c0204060e0708040b010b1204030305040f14070611060705040302100e0418050105090d1e0c1502 76
    0x5608011501c60803288102880c984110098800122903450300c4c03d4041027031401c1c070208160205040c0019422286020074841c62505a8026940d48030408503240760003140e801c4030f40309a002803000741c0b00c41c0703111003d0400503486044c05a241d800540009051010700180980524200020004100020181c0d184140000d4440c3e001409800c40082c03a42842405050700b10a00000d450b005540126a40c4014900c014804505103803201c211108026099a0b00c101045141c4180010000d125440c81c0c09040308615250034032a551a880f200544080c2015040c19640c02c00300d410702200f510110080c82d000342c00030244001c00303000355543c0c2c1b0051080e040014005680e00c00c120001147c1140110300c40c0d40e4245c103090450302000191184009a070082c080103e200e100e1948550283d0720075203010807003194070b502c00c0307040040c2502c400601d40710003501b10a0041c0359050708460100500c1b019041c01d00545042e8120a903120a100c0d00064010601c00042c01d80b80803040d0000c1503 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 633173525 1250 633172275 633172277
    0x80c032407120207140f06190e0309060429070503030f07031b050406020115030c0b0901051903150605090a090f0f090b04031b0305220915031118040f050c130c 70
    0x711206c010303100e40d1201c4042d141c2801d210b1691601c41d0318040c0580040c9500005003050301d1601940800003a050b40c419800101584030509884110000c11a021022844142c1c1b86038030b4256141c4e91207890b440700401080399260a10041000c0900c25402000a61507403000c00025001c103000c040e0a030b80061081000540c01d14034813031416081c0da81880200c9a1062200354008d050041e448034941102d28082d0402109002041c050358201c9003516030180e09880000d44084101d404403100a5260000802c0c800100120442522900b01c04022504590760009000034800b118401410202c019250007034202006413090001044081e405284651035039251107141400001ca410b02d400000b9000c510140007007071105034140c441420304c19501e401c0d11245a25032000d8400c55030514400781400900340414000c021003103001c01c42001d8212880c00e8048003000b40d1800d807400080000b09008103004011003001810401f4010180d0028030b810054026140344400a00101305484 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 633174775 1250 633173525 633173533
    0x216020a05040608030d020d0b09131506080c041d010908120f0f0c0f2701120e0d03020f2b060603091e0f02060a09080c03240712020714 60
    0x5a240b500b8801e0782c04803042c80001d142000b40c051900402900040915003400d9105c52440250340d54444030503211300c10340d01046440244ca81019591440c0d0071100392803440c50700000b40f1510700d0004030442400c83c2201c01041111102c58500d00c0900700d444c03000050f41c24038003802d080044200103005c0d00e881404080354135564200060100180585200304846001408100051034200040412440d4128a2442d10401344084240c0c0101141026140e07412580090001e42c1e0140c58400d41c00e12801e0f044c80141d4000c00e403030784c403450b00d031009a081c964000740c1144500c48a20503109202415660002d00071120901a0a8a04030800c41402c592a00d4008104c8500072b01c501d942c026007041e10380d22070544050720b00c0d01880c5004170076104031450500c2c1701c005903548002059600c1440e5a0442301628240300c403883d00d00380c880041d00c00e4010285000000700021065400180e20680034101d6803202e4100303481800040200080d014000a0001c061150604800c9440401c1404603 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 633176025 1250 633174775 633174779
    0x302180a0308030103030507110d0b07020f060f190f020a0c02240702150d06030302160608060d03050a050d11090a0527060609040e0f0d020a32010216020a 68
    0x48080c40c0315001c010586141400180b0120f03200c2c00240503824800d1400c540e035064058000b850356017103498119800175212003088645581030080a648501c050010006410440c07070240030741c400140310907101c4081c0e83c1d43c480d040060b40c00071002c515141004640d9200c2c0d44000900a5224901c1640114103120300c803a010010355840200d1300401031070403400c0041c183d003040074560f1407070f004c151130320300c180100c81e0345011301d128130002148650005c2401d00499012040010115070014040c0000700c001c01605440d4003181c09081ca42c907107015950740180a1382952240560f61302d18020f140740900c41c5031040b0010005042c100011550064010f945034100302503031000c00d12072010042001d4400d600002441101604401c0c020700550070484c6120108080303031010f10280405600802000009034401c0c000f4240e201d2151000e06015440d40e01c1d1803030b81c041142c2d02032406c0c40310360b94039a110403036042942d41c0c10b01c0210006e554880008081c00c2c2d5004000d10181d00c10030b0714400c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 633177275 1250 633176025 633176029
    0x201020d170a02030a02070602031014060a020a080a0516030f140906160204061805060414010803070f05011803020a050609060712090203011d0303070206060915190f06030218 77
    0x603803600c48180c106011140c0e542e9090101075000500300450080e001c0c48a10b00140ca140080c600c00c110007080250081e1814401301c0c6075003401c2030a130f8014403040241300da4030381d40400d429200d5500090450703500c0d00007200480d600e10414400840192a241c4240e0030035611069680f000700301591140020805403900381d800707100c0c00b510907a0002040042c4554107080100308080580020000103d007540d03030394104170400551148104065550b420000d03203241c10711607507482e41884d0061210943c104403c180e41d0f4030580201811400c050046030040203025000025502009560504418014035000c0d585540b03000c81240c00703004240c0002c2e2070706400112a481606a913a8400180507034210700001480310780005d03138142d52030384829030b250014641200c80e0750201400440d41c5e4030746080005d0400e400600503d00c60700c8814180b100403101001e8000e08203404407003100d0700b00301c409403c0040c2080c581c8500200300f94400001440d94255001c3d119440300724030003941c05001c60342 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 633178525 1250 633177275 633177287
    0x50109030207080f010209100804020d0818010311040b0715020418020703020f060c0307030c1403090d180617070e040e0d031508071509172a031c2105040201020d 71
    0x4415044000c80400100149c4030b034070301c0e640082c0050300380d1007200d1281e00d402944d680b054580b48980c02000340a04e40c903583c5032041c01c0c0e6000c0101c88030f80c10b00d03003483d001141d54070038004082e01a100901007842d4000c02c944c11140146290fa130400e1420303038885080c03006500800000d41c0580200540b11010710000b1851510444440020920f0350307541c40d2040d40141140c45101041080700424110840004001540903d9448005050388225a2401010381007010001822180070b92000c10030207400a6011603c0d0303c00a100070340365621030504503008a820069158000e081144080d05100042204016000c16503003c3c042043c02585140c01e16000e889400d5566003c20800c00680410300e0318074914071501e00e0110a01c07952102c6940c50103000c1004c06825810a156650f000c1350444200d80c0089144e0250b1030344c1a00715800a52182c4490b402c054417842c401020f114004c1c410f400031030400c600051288020390400d0300c050020071007260128058400d0161082c04940a45 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 633179775 1250 633178525 633178537
    0x91406070903020103020a0905030f060901061d1321120c020d02100203060420120105010e03030904050a020d090501020c07240c2414100602070918050109030207080f0102 75
    0x3845001609180d50f004400030b40c054003a420801c0b80e10b8a01151070340d4244034140d04082490000d10340e41c1428050b80d1b00719089588841e10780c0080703407100c0c80402007045403941d00c040b07443c0101c4002c0c000341c20945000d0807143c01e1300070200700284900d10100d41110403804107140f1454208150043c0c802c050b40d0b150103000703903040907a020003032a2078881041c2e0001e6900c600050004a038022422000d0000b801041506005001d004210248624180545a80100000d181080e2145001c4001c030784c4a1040c075a465004036100c50015010310341c00d404560010b0881103041096840904000f4000d4011a945529030b000c0d141000824100305641c0300c001410348004810040040700017640c0705041e1a100311403860049102c0a007403101005d044001100101c0c5c0880c0782c6405500d0702c0b40300303a13004011103120340100609106042d40090711f2001d454070010005445025010f0b6400003ca050000170301560a00645400301503001c68403c0498500004030340f01100d80104172401e0340900 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 633181025 1250 633179775 633179777
    0x1e100501060309111e090903090301020c0a120e0d060e07080f0c0108010902040605120a180b0103020907022109040207050a0602090118140904030e03061824010b1b0109050109140607 80
    0x8a1030030300140341c5816111f4001707140600700c2c0c0c0b80104180119003a0b8001100c611030a0301b11201102c00e001c040b40e006400221103140038003901c0c05401c001641c080034010b0150415540380220001010100480d5018180c64401c031202540300940a03079941c0110744503203000a50040000070078500314002d80e010745919880b26410708a1021004442c503000400516411381c44286401d10030741e0700680004040d01502c0480015810341c010f02c0300f40100507000608560101140080c0b0a2455014558000802441e50394403070444d00003078082c2c01001c40103841c03405210340010801c00513070300800d6480b1080c4c80c0c80c29000e0003030f001050a03440c1d0f03118000907201c0d03a900c0c6070141d25014114aa2152181c10544002c40003a008a45484000c4131700504903401c4a42d44050044200003152443c4048044040c0154908c134803114007210620502c41084e0001c44c003d042c2407080c0350400311010841c0000c00424130303107041590280c080a0741c25100b090300045107100900c0c003c5500d03803080b141 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 633182275 1250 633181025 633181069
    0x91003060506091212030a14010b0910230d0f05160e04180605090a020406080a05070510050f0309151302100e01090803070c0515030403021e10050106030911 69
    0x1c2d0b03080c000300001c01140f0111501850030b1480300f06005c98095070185000700b1000445522030700340314100d008181c04c280110581030205800d20340c1da5080c070140b04000ca1a140101183c0c3c800903910000050382d0200f070188011401040226003544801d18620b400384041c0501d45030785148901e504007001c0c0110004040320100721460410b03070400d0034100b44c104200c8508240e00d440703400c2140d00c01d0742c641010782c010440040952400d4004c0341d010340440d002618080025644155541c9410300c1101d01030241344128000c000d0103581a030700001003045910307580f440c00d44406a242e1105042d031170300e02c00340c03980407640710181e48500d03451245e03014001082420a1000c299441c3da0100c3d00f20781000102200412400020b10280c074515118090040d9240d05120800071948064411031441038001d00130400402d07400a0811031008145a055014000c013282081c01c0514411101d08100e0612000041c1d2a52603031212103058058440d0448c610100700c00c00906d8140181e898070301e004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 633183525 1250 633182275 633182287
    0xb220908040f320d080f0d110a11030a05220503010e030a02010c09030c090e0703051e0105150603011a0f0310080607020d0e13020d3e0a0f0e0a0b091003060506 70
    0x1000c0c0000c212406c0c0e0100c0c0c0c01c2c24500d90020070016161001c1c6441c20f1400c012445d08810f617004115842e18410400182d0300707150803c50300a0060155082140003904030740001c4840303048208010014010240c02445410340c0558030aa9270b6000c0080c0302d00640c80c02ea102d42038107104104d080c00383d0351b100190b0210940b8020307803080984801c1c600f044550060803400400600104080308096070070400c00282142401a00380c01c54800074402c454007117035180903945650702d10080302e040d50f00c8443c0084188520181802890050099480000c3c0000040c420408051840f40d001c503001300c021900366944d514030032611000d00f5030644001c15503070b09100d40245440400001c11550104c801410000400c0f8084151540409481c4e82e03032203501301510f410885440c901c000f9411518502202c500281840074079842084110f4040010f65442650118407a00c00c190304480c0c0146280d83c501d4680c0c0340381407507a000d0b6a00c148118951001301150300c4c040e000d10b0080b00c20013880941041 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 633184775 1250 633183525 633183533
    0xc060a0b01031e05010f0b030112030810030615231806060c011109030706090f18020c06070f033803070b0d06030201030b220908040f320d 61
    0x1105000314103043e12115202c031421280d100d4443c5240c90980042200c1d4545072050b8001201a0030004080310300b000103019415070690413038a880e42c1407030200d2080c1d50b524199034110003c2d0300000c0c041e50030107460405c000d031b544141c0c9042d01d2000540114200080c03406144010340f00c2c0400340c2000301c003a0091040b042c40c00d080c503400403002c0c4c8030a1401d0000c0d0300c20703401c40e0034404405065010110f51180c40d0b04003040031170040c00440c14000c50860824a4030350741c180d0144140701401c411510072222902168060700d5005408804071003850a1180002c0d0101c140318501000103490700ba11061542039440751454003c030b16070700e0703c5068120303519070617a5444100040e5400d4131440b0400200c0c64016001081c1f690318180000511070300b1031000506403034512080c0d9201e00c200a01418010754038000000d0203880c40300b000544660f00303240c1600300f409030368030010038039854080000e0b00041480d16501002c044d2501c2c0b40702c1000c100e082c042c4480101d0700704d89d007059148030010009 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 633186025 1250 633184775 633184781
    0x804080c2e050408100204030b010512030304081c060801050601080f1b25030206040b0609010311190b0301090f110711060703050904052707060e010e01030f0f020319020c060a 77
    0x42140c50400e24140d210a0028031709007045a2001d402940041d04005005000e2200e5003d00800c903503401c03450040010050781c07800040c3c8090f220940018403070700b5400c81c100c140058441165014000d240e501c08001c0d00030303c4120b40180c04034201c0340000311801280074040d84900b043c01c001d07d02c00d4580e403902c8a5903401c412002e01403240b01010340d0741c00b003020500c03010b1590311980c000c0c0140d241a00d018a250b0740c020b02001c1c040c480500c01440010341141c4021020202070711480f001c2401c1420341800b8150310350182601c0c000000000c42c80d00f01681048107000c1607a141802b5440da01d480705d20083c400d144c8003610240a039400c1d0050b510740040200a00d03070007840d14604102c948000a01203c0c1d0942c4e0400300303555900c00680d1142684000f550611100070040d09450380703040800b410043c0720030f481c00d04220360042c42c92081c1c0c1c000d502100141101c800c0401100501500c081c00a41c81555501b0306403041518041a040341c1d40202c40c50340d004070004d0030054868079481c1e00a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 633187275 1250 633186025 633186109
    0xf090d030623010513030605010611030a0905010806031509010506040b060418050601050705100605091326070c0f081603030906030906180501050402091303050702091807030804080c 80
    0x40040c00c0090348960b4005a617268044c60142d03c0c0002c140d454814050000c1200306550b01c0203070000d0100101c4940c01c0105a82224800e081c08030080c2e6a04e07000a0a200d5076110441141c1900030622170308840540c03105d03200f0801520308205081e248800c002040c0078511a031081841e00340a881c03814080d941003a81c0140060400b60b040c200a50b030344a041c861640e080140d21507441d1010095490039200b03d40d004a420f138040005a00b090b142c0050400105d411001c040d2034403561074044201e1041100c4442d83c01400b000186034648203809070213000c900c02c00c4c00311311514a40d490f04480040c1c078881101c1e410b4446101c05850004194007900c3e002c241551555035600c21158160b840104005d01240304500004d03230f603d042e01c108501b5250150a060035540c4013002c0c213002035003140440c2c0c5400c1d01183c003031860360b4030031004501d0f200b50070405610ba402240300002c20045100003400c1600c5400c3d081d60f02060608003404000254034240c10142c1081481c000c43c4070b2190844550 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 633188525 1250 633187275 633187277
    0xd020901050f040803090103050a06260f15010f0f0837080a090b0309030409180c0305070807090b0a0b1b19020a08060708040b0703090b0f090d03062301 67
    0x402c0281c00d021800158000340c0c4480d48030b410006443d080341d079251140b60303404184072404101460502c6568503441510300d4810354a804951900302010b44200500304c00c451486044900d106206541850a031030284640088024a0301020801d034202d6813006003a80c500d030004018514407004802c44114150782e10300079080100d005882c40d5080c100c21b151072607004205440e640c1c5107080340100406029400710014070030910134812000404030454080b20a80940802d04102803040c000c0100101e0100070412642c1d130348004100300010030f408084410709811341d004030b5a914254000e0300c44c0c0142065115203000024008500386902800e0109410960600300f840c52000992403c041500700d15101d803650420300003145404050240034140450180c0064141107002400050000e0801020b5900c102d0001d001c0c0c9220760300061109820a05040321405e1047c0c820307075003440686040f041030141c1c8501d40681c078001d0007202c2c102c45c07052010501d8503409140f851080140b0000440c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 633189775 1250 633188525 633188527
    0x80c03060f0714071202100e0d1d0306091c031b05030c12072016060c140304030b15010c02030604081b01060306151d061e090709140111030d02090105 66
    0x4a1003d00c00342c0600310181c40703201004107520b000c00340a031034440c00301001c8840c00e0034204c9102c1c0e400008102c40342c2085050a03c210b00c2c00d5403120220011050881180d010711411080018003d0005030100c400e1456146186882d90450000c40994401d02c1071007401000503002c0f1403259200340000c5070700c062116a243c1c108004010001e00d198010746103500020100e400642441003421082d6204040030001001280059002030f80b00d2020f91003410288807042400b039092015480059089441e0042035a656a4891408000940c1d007176481d03009840e4404140d102e10350180a000c1181a002401001c03141d850b6a54079141c3d9000d88401010304800708801c0c1c10269003401000040d40c402c0c10042410003c000e415641c03c2c0d070340c0d8401d00000e034011409e5040100f03032a018940042c000d980c01c503503040d0348500408080c00b81d180c441d40c000070104100110554840107943c00c0e540720f009140c0d20400010011070b22a540e02030030a006820400c150342010805500801001c80181025 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 633191025 1250 633189775 633189797
    0x13052112070204020c10090b01050301090c090504080405030304030803040c0509040b04060902312007030f0e15070606060503071202031f0821040308090607060906022101080c03060f07 81
    0x28905086c3c22400c181411510303444541b04006039821143d0150000360b000700702c0c070515a142d0783c01c030b01c41078404c000d0095550710206040c021131400302c0d006080e0150480b07a03900d58038900003806074421a419106201d5004001c070302c81c600380c008240556005400c01c0c1e0035803a0b03034468400034042074a04036804010940c0300c19071064200342e40c1070740300f4101d051440c42000e146049002d075140f44410389447e03040c24401580c030303440003801c3c1c8c0c2410b601858480c0341c0300501d05080d1a5800a440402c0d844012040e080703117602c1c070700310003402458441c14045c046196116030941d15404151002c40100d20440b00403c00148554050f43d400085140044a401003203c040402241e09410a000710f40240b140304003c1901c901c42078016070f0741c0300c41841c07074249507840390071450184040c6103114420002d039140902089801600d00540c0001d011540c4680c03081502c1c02c02c094a0b48008240607112000081510002c10000c00c80500580a4031803279030361124026030494001c1c03100050206070b0086c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 633192275 1250 633191025 633191047
    0xc030b040608030915030403021c0203071b090f05040206030c071a0a020309070f0302090a0e011b020106290d02070807080d200307120f090203031305211207020402 72
    0x40c803070090038460302940c1c1e54825101841400a40012607101c0c0388070400900c4006a80059013010b0540e078001d01405010039000101e0440c820060041c0041a191042c030b650214010a4102220560300c0c0410044041420f6103081d41c0040390042d41c02a400d20028148404000013010346600c02c040d070500071301040020042031501620021001c41c1c0c04401c01001e100100564070291548459480d807842c5968002510400010706001d0b00d04e464141e64102090f0940010b0102e0500d5612030020942d8088001d000780b10364480c1c4401c40100c281c072134203001d00350140c0d403e454400d503000c82c3c0307001a1a6400c0010f503200000c2120125420482d41c40840c01141c00744c0a9000380c500089a60b580150034964000780800320019580c03010028000780c07541190050011211001d00490340520601807680200b00f10f41000e0340500000421000b41500c8441050035034034121010050144080a16610fa0724124000c0205034050b8010081115a80005d030034140d00c0140090f207000d8010f09 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 633193525 1250 633192275 633192281
    0xf03011419110c072603040918120809250308090102030f0d20040803070f11060403210e030d0c050a0f1110031a0906060c0a081b010605130c030b04 65
    0x51078030560020f1009000c6101402030030102c1103861001c4808590503090313456241c0c8201c0c030030005d503a80d0320301d420040d21203009030031342074540c101303a5000010203c0ac0e00906482000c80380d40c825805038640e00d040c1051811100300441c01071040da18603840c1940e8582c0745603230250607920306600c400c1c424107141d1007a04000b00b0f2900c04005010030741c215009010300141400d50701c200c040c0c1c2c00500041c80121800402d5404058101c60088030004440c142004510b655255454200303c0000b000702c1484580e0400101807010f001503992480140071040b50301c21884072043d541a040729001d8504107220305490920103001e80305403083c0b900d05540d000c488520340c01c8101d030409403125102c0703982d14003480c5000b0001003608040c419402c54035125682001e41a0302c40e40710740c0c030950100f0321300c1d01c844059a0102c58000c04640b0210403900f0001059002102082e42040c40341e40c00d24080c1c00180690811650098050201c103152581c90344003030942c01e45420b08059991903800d1595942e40 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 633194775 1250 633193525 633193537
    0x31107030516180c1409042c16060c02101106041a060a030201090504020c0309060309010203010305060108120f09030a060606090602010612170f070b01060e0f0301141911 75
    0x10215241d840d24543e410240e10348140742036414a85a84280c1043d08042e4039404030341c00440c1e00d640d414501d0f0000b8024003000414001c0102c00c01d40c240d28440c0c1040440a5400c100340481c0d540144145101d1050680c901031400054a0291001c0041c101494031304100f13040b908018462010b01801c603440e01a046800761088130713006880785d81c0c00c0d030303c041c500d9002907040d5600e03d0100d0a680028040b107800380702c3e490085e923001903804507101003441039803e002002400d00e552402c050f40014041e41080c0026a2540a400300000d01004001070b1001c0302200c44902c60b00b0b00034140c00c1d14003190045141d44d5050b020303003215030001072224450b0300c01501c001d031210551503082550090071950b56802140085002d804400042804080e5648401050104243e030302e625402059100e030040e090001c0242e640c00c800405c58a400c021035112565083d5039840c49105048105401c1c1c072501c09501c0007564110010404800d1481c1c00042c1ca40302040000c90011604641d240c0964051 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 633196025 1250 633194775 633194803
    0xf010c0b150a060e091803040504090b09011b0807180806040f03091707050d020a05060412060c03230c04051e09151309020414011706061c0311070305 66
    0x120054a894800c14018081901d460340811300083c2c003040300e008024001620490340780c0c0301079200e54400c1003110007a01c0081c1040c00700010903d481c1070740e14020b9a1302e044035402e05840d0b220860f1050f511400540d950360740c0d074102c1e03201c110080e82c1c00e60100400484008806101083d490010800c0078022845020210a00003407810010800300300340c0c1200402014200b2103004620340016610150f5000311001e80c1e4072001031001039101002a4045070b00058040360006040400480c0f041036180519014003400e45040c41c00c03021104500310030f1890703c120320860b04203035040118141d0701541d142c82c0c1134074050b2a440010440520701c240c220001c103041080ea407a600700a503a650b040380c061200444054004000242c600c10100e020031010b60740c500c051819035490b908038200041e1501d03400002542c50300c861610b41d1035440b0f114101441400040f619030b040c1000c100d000c504003220029282c950540c1c04443c6082d0148000e03061b403003540000f0010030811b204209101e604 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 633197275 1250 633196025 633196051
    0x20d03020c010e09011a03091009050703110a05061207032426070308030a06030818090f0c04060311070b0907080f03030f01051003092f0f0f0f010c0b 66
    0x3079000040248100c1d110441c0036a05080040041580105900140c0407100038041d44030b5035404809031414605020707a041403818484c2e05024800041001416a4041c04503048903401500c18801248000d100d820f800840401c0b046410441c10540c0300c0d00710804c5d03e000f0440e0a551541c1542c82c8014031004440c071800250100002c540d40c020110300c800070400414101d480300c1c142a80c0302e401900c4090824400003000580f5288154451800f40d42d11010443d200c2c0890019480000c14007c1c2d00c0d40035099102c08610f070380f08070300c03151442400b11480080c509404c000c412006041203609804001c0424450480000c20b0881d005100c1c040c0c0000500004c0e1804140340d02e0040300030f10318002a0010024403610059142d031080c1500c205032a0f40e074030310000000c03c400038150147d01a0100042c1d02d081600340410f502000311004100c09501101c601da20308100d00310018403c250303404244000111828142440007440f40101414694100060740d20350801640e005c036220348100355 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 633198525 1250 633197275 633197293
    0xf030105101d190c1e0903060b0306090d120204120b161e0e150307020c010801052b020105090a0603061e06081b0c1207060c02010c050a0e0d020d0302 66
    0x3484080c9407032041070400303035800d0400351000f9060000e164101c245542d200d44920050f02e00803000d1600c031111031030001c0c8032821812801001c03a110350004480c4981802d107d040a850006003a5000c1d8200d10043c01c030b800315594064860200000c0300b17840198081c840090520504400746003118041c03201c0072660301d041c44020700344c2403e030503080040c4041e41c0315111408a06c0100f4809046841c1840e03000713080c00300700183c0f0301c030707100d08401108260000c04c200c44c1590101c1c0382c0005203006e0300c607812139980740c0c030030030405405210f10740e42d0141c0320301d8501d500440006103503403003280181000c80c641030072036011880b080c1141e000140440e032200020003003009458a0440e001400740c1c1c20681240c00c1c040e00a01c0d44002400300008584501d030102c62040301d01c0d0456441c0f4800a048446401102030040c0030340d0008a0f0589603207141c140492007040c0107000d45206540c2039500d03149086a0362000b610841f40810b0300c50b4012182c4882c0e500107032100c080b0600464000d0f0002c0a03200 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 633199775 1250 633198525 633198539
    0x3070f021207030308010902072f0a14060a08100f080f060a020f09090601020f030c0a0c0510140d140c072109090905190f0312050115030b0f03010510 66
    0x1c64140c03151403495000390b800700003080e4083d41c041e0640b20190710150f41c4030b4481c03c1421200d6880030100f5007800c54240d504a2542809054440341038042d118044415176600010020140341c0011607080041080030a292038807407c13205501069101119028a880340314107416185036410200c51980b046c084145076500401000c0d5208000c40001c2d803600d03c034140827040c0d500600340780a02601000d0081170b0b06038002d200300c0e07465400800c203d9444200c0610703c6a504d4003103d9080d5480000c2001c00701c2c0034102200d913522907000035102d080781d45604c1c00c8070b001582e0110f13640c00c15a80d41ca41042c600051005059802482182e60341c039280c03005030a008018148100198182017a2000ca0503140c60700200e19404644201200150070042d505060f41021009054a81000c0c280420700c4100705c6000c0c202500b80307000755a800350000309034000d001240d10a000c1c440505200c0c100307901c0203034841d4220340c0d482800500031502e0021001c0100e402c3d12819902c014981144007010711a032 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 633201025 1250 633199775 633199789
    0x506090601181109040e01200f07030804050a08070302010b042304110406031e03081003050c0f04020c010c02010519092f0303072117180f03070f02 65
    0x44904014218035454942c2820754040602c2e000320205441e00803031048000c80009850366540040c4c010b10000609000041c020851071b150b500745410081060003080303043d0070642c4c140d0300000b81d074285085010348040e90072140091040300d05114401d004c10000300c00b4070162a11034030a800124524001d10100000c0e184100d2040150725170106d01030700c20295100d2001e4000350040c1081c48200a84000314005d411550006070181c500c02c141040382d822110201c484250003941c0708007003511101c43c400c41d03040c040e00c00601107500951507441646480c0700366446401000700018502650342c40f010b400d407841c9d07820440250750764000300325007021150740090100241c80030402c040030f82a51a152004008055500c0324040140c142204052002c60349402260003000c40343c0710f000d0752a00c10030b40c1503400007141c12540e401020958a41c0200c1e500007001a10640798a141e90b41e0321440b400800140480401c0c520810b4586541c20a041c401498060301910100b00da1070042d0040c8111 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 633202275 1250 633201025 633201031
    0x5181507140705063d0815010f03141c080601080609090d1101060e1906050402160803070306050a0803070b09030a020c060a1202030a0519090b0a0b010903120203070506 74
    0x7a952040140000141c03020960503400000c16050f102c400b0102c420351001c908842c6101300c0c06203c81e80c0d0a045041030143d10f10220742402c41200c4038a860803805a850b00003e10074200418140c1d04c0c1800020804030312035412504a40c211940b8110154000b10040140c0c030002c00401c2483c000d0001b00d59002001a510140540d00350100d4140032150f150b40e60309681c01d9034108030981080c1354003000207400c0003004100c9100080b0884c100040c4114003011101c011000c5203207070060004990400e4026030303540380044141c1c1e41400300300303880d40401c5500007001e07641010390710a0049003c0c2e81d210003070f0015000c0c03076004680700c48451904100300788029240e000258024803a0441040c1d0025200c801c0c140c06580003a120600350170140d030713801440e11211014500120400c4041c1034142c0c400c41c4101c1c1c0100c50100a005007468840c01c6980740180503011019a80008695080c5604551402901071401001480da00c0c0c81e0301402d0322101c464100180c00004d00395040c0101080a590 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 633203525 1250 633202275 633202307
    0xc06040b09010f1416020111060c0903070915090216050106030503090102103c050c07210c080c120f0307090e0106080619210507090c0503060405181507 67
    0x1003541c8904c44032a0390f81c00703a58154484544440c078400c0c1113901c076074403481400d404001200d0660820482d0300c18642c002041c818000d1045140c000b07002c85450082c40b40302e410040280b44c0c8541088005c001a5100464050698030b140c840d07076000400c240f00b003d0082d4082c002840e1184c00c51800241002d0110000b0702c003250810308420408040189070690228016070403d00c06100000042e21030901c00328048403481c0303828100490419084001e05280d84100403002e004018922100440060081c0000009003200340c2d00c000a02d5182c01402d031580e502c002c4461003c070681c40f60803140e101150303084150303c021090004e8282c006201c070380580b100c41140d002a43c14954010440800103001d181b10b24890b490390f50070308550882e101c02500d80c5006a5040303003d000071005100d04504070407a0306109070000021041c15522600e4028049a51010300c0c68851341c007000040c020140039405403565611811a40420410810b82c00c1d4440c0e80540c61103207060b900203800c2c9244000342036 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 633204775 1250 633203525 633203537
    0x41205090310061a211320012c040506011b03021b03010203010e0f1f1d0109021c020d06080703141c050a1107080601080703210504060507050c06040b09010f 69
    0x10341d8841c4d1710104032400000f840d0071603591081826000d400c060365001d010082003030105501601103807021900c4040070780f540300801c508440080c2080406c148004181d6509980052591a060304180d8001c0703414900910901a002d51f0700e40c4080d06994100c000d0303400700152185054405024801d403000481c002c50541d85000518103035600c00816000c10b81401c007000407106027881c07000800840380307000300620207034030762242c4001d00d0010001c0001b03c0d400e00000207202001402114004060f104003080420021540703000a900800f0f4502d5a06468400116880c402044140000c5005040c2400c0408411024900b4064425000c100c241c00c20284420029003190071100d00c080b4a02d0a000b060004d405100d0030a655904001c1c41809103000000364254002030920580f802001d03900c0d160030404501c48540700103450905c002c01d8040c0070401482c1c0c020300103803081500030401d07945c508550000181540c0d103c0e4108400859010440c4031003540e00442140400c401c80c1030407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 633206025 1250 633204775 633204787
    0x1060302040e0112080a0c0f05011401050f040603021f0c0b07050702101b080306211609090c030602130f031a06030303150609030c0d050d110a0b041205090310061a 72
    0x10380c061282184441c00c7c0501b03045050200030300b10040340c051a82001c0200b0058007003030000004400f0030310038a8030901c1a08240160381c600340c03040b00700301d0384e006164003175490382c0a0052200c940b07841f9481c0103001441140c60080f441010440d403141e4100e540700395542d5854810020007000c202803074410014080c1e0018101c00c141a902d4203800d4002d4111501c0e995094000307200166031003031524005401c0d0301c0003030648600041084000e081c0c5480c440c211900d400a801c21507101c4036004c0e0214001071001c0002c1039495008003904e03040091402c032100d850380082d40f440f200943c01102c203458002d024030781090301140d00307a0300104201c019528508200c070351711140043c0704030b40700e100c1e10b00041c107060140d404202882501002034803094a061280c00e200e5180c400e20030388100452003188266005040101d82e007000207602c50714040c2d2070f44030740d2645040d41ca0020403282c14000304004c1c0c846240c0e810860030281800d428008290141415100d03401c0601210060110305030500c06 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 633207275 1250 633206025 633206033
    0x4060506031e1f09080c100f02091e0a1d07170601120c030e070b03010f08120f160f1209060e03100f0b041401030b07170a180b01060302040e0112 64
    0x45071000c50072540440c52507a000d144070303c000c00d15000001c04040000407810800e00000ca5804010160244204044102441030009a20483c0e003056480350f0a06c464640c0c031707101001c0180c0c1c82480030704650007103600c5082480c3c1c40b0349201004021040c050040000065014021070020b840c207040c451002c1c144180042d0090525140c000135168959410342d0405200303074040354a0401c642c003112001d9540d801d200b10070b07038800e018040c0200c240c203034045800600002d005000401c0c15020780e1405000c52180019600918080004e00003010074039004117400c00d41180c8414007514241d42c18005050b4041c181180d960b010409026240802100c280d902040918004001e464081800c03940035407003000800a45000b2a4010b260100505134442807108580c1038038880c600f10000790b1202c5206869082843c10944501301001d4000703030704042d45400801d40c0f51251030700c02420500c16666042100c000740c00110001c3e07404502040242c425200c00c1d401407038024490030524100e074071 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 633208525 1250 633207275 633207283
    0x702270709140d020f091e1303090f05060304170d06060e040513050c040e03042c070302033c041103010b0a030b1f09060b030105090106032a051204060506031e 70
    0x1000b21b00c90f010800014505444003080403201c40181d4840c01410300d404428009008013040042d0001211701c000450100c5030300d207208041e940b00518160030b541c0d990780c403d020350340d803025064102030f02400608130000c03481c040e46000e880b081e2294501c140d000d8040c00102c810003416800002400e40c0d440d004101c010440c4c40407140c0503280828032040402405255114a5101007540103d42c003090303101d902004050011541a8a40521240c4584008600342d000554403c06401d0845124007101c2c01528604101c1905030a518285c110314003580318540142180c0660329100c070a03412070010700e000e00c5a0801002c08172540c801c000d003580c0b61040f43d0700000b01050301c0d032a006850004103610114180c401070040600501c036540d101e202c4500e65400c04e22410340035031400380022412070702a014101505e689040c0d4402d1848003941da002e0422103000c1582c2c00c2c40010401266030740b40c8414080d03c0380d4080c0e00049803904100d0140340c540302c4031342440d034101c0c5006d02c81d102c10a24045 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 633209775 1250 633208525 633208549
    0x41407080402100c1403030a050f090304060e0103090210090e06120307020616050f07080606090112030c06020f120411030a020306131b060e01021c02030702270709140d02 75
    0x6111100f000e840840c0c25600001c038821301915044900c0c42404684800000962003400c00042c103001a0710f5600388100e4060065072450b0064000340014882140b003a00c1a81e0b15240502d0003181d0700c4e070035402003032000c10015280c800145e000d410a10400c03e00c095010341000003500d9001c1002c00d01d1510720344a008008000b846504006500641c02c0c43d8a001404425002016240102c0d10315681d2a540e4500e4821041b4601074400000d404e071905c0c40485d030480b100821882c075031011310fa50890301c80d14611000c0f1f031110342c00e1000741100342540700540301521503c0b80201030b5040c2800c02014041000044902c0780d403000c8150001a240030940c0ca13004a0004050300c03da1415203841040406010070b1610b00240c0e250740042c0b00e6502c50b8407240d200c14281c081d591200040303070030100b000181c21581c1001d0380c805c1200d4001810800c1e0180c03002d000c05110381012005216244c00ba601c0d09480d50000518580b10074010103040c01d040124409048405842d404103070703030128821707517599 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 633211025 1250 633209775 633209779
    0xa0b090d0602070b01061e0f080f0901141509010f030c03080c0c030109060b0909070b03150f03030403080a0906030e070b0a261b030108210408100506041407080402 72
    0x5500310a0400c041da405940d00c040c0e100312600600d607190b0f4001000803010f000f00c124026062100c25401c18040d03103106040c3c114664410f400c41d47c460400070b00640c40600590311a65031240c0e281c08804000310614040d00b868000400c070080d107201041010181030b00300d400301404002d4208001090f910640c01200d50007003406031504005a00e007401d1200100785260554280b8009204000307240c0d1001e94882e00454125200d511840d819550703071101805410120082000450818015500c10f00005003004000c4c007403403072072540400d0840c0c2055004880021001c51110341164212008101900d80740c80c003042122603101100781d03106443d10650312401c038000340e4804500c1c415001000e0f81404440324440203000f074003c4d00e080c0f1004496041d503c0c050801000e0b460030004049034100c0e289900200900c0d400440d412440140c10601c0c0300070f0510070040010000400d005280341110406000112494400180800d58102c80d400644840101c4204090319800c4038800e6003260301 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 633212275 1250 633211025 633211039
    0x5040809010306060528111b0909150402120a0f0606090e031312080904021801120207030806041a090f010e06010c021e13060306020c0111040806161206090b0f0a0b09 73
    0x40a50a8403030f40e5452448102c3da00400c415401d00306030850964152361815a6030203c19520703208071903102c10004145a10f5a08040e01180261a042103402c0c0030300d5100040c1c400484244d0303074103054190b01e090201c6040e9101c0c03408006145041c8146142d401c030718405180b8010085120800600950213091040b440c1c200e8401d0604c24a00160345059038094400c5584020440300120354408199400d030001c1e011104103202000c15000b0748220b81d5040d125031031607454540070400500510200303203100d030600119418041d62001036440c0180c946d03240610803541022000103810900411050610140d0114880141c0360401c0304107598545440e2034480b050080700013142c105038146071350449800c1c85408014041160700030000070400c2002044914249128115a4041c3d82b0807203803190001ba000590244a402a00c1a04543c0d072401c08041e60800304240304940c0f868000e400c00700e50f00c03a000035450521587e62500c03907604a5910005500d0407807111903034480c0f2240e15000f004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 633213525 1250 633212275 633212347
    0xd3b0604030b160801470d0507020316061805030a1205100b2a16140f0303091c020d06090201171b0904090213151706010621050408090103060605 64
    0xe42086c1c40c1140c0c006040b0032005440f13101d1107a1160400d8140b000001e04c1c4c400490007482c0000b0803200200072001110800c2e00316900d51800600c40c00c040314080306040100000020703024801030100c40000c0c0c540d10002e0100c0040b00007101c500800c02600ca4010000501051403020180c42c3c602e038100445c1d00c1000441c400400c1c0700840070440380c40713134401e49542c02d4422404200326016036402201c02c00040f00b01e03404000c420449046c2c0550107070800c1102422900700411400ca030141c034100700040b1074080d68046041300540302d02c1a10540d903030b060000b0031581e0010749941c200101e6200300e0b01a0030046402c010310a400000c1c000c013503500103020303245a165504030307404007038000700340da48001d07003185100c0041c1400100405410b94030790004242c009040545400281d09a001081c80368205003003518050514500d00300d0014080c01030480d40307540d5004062145100c1c40c01c6584030895070001406550240d0841824090140044c20b02c0b14051180d203401607004c2c0c1d40c0385170429 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 633214775 1250 633213525 633213599
    0x3080d02160b09030a0e03060c0a11031204050c09060f10080603100509010609050c04030507060c110d1103010507030911090703020c0f0309030d3b0604030b160801 72
    0x10001d480001e0400e02403000f0040514000700141100d11100d80f1031001d25030700b9404060311540200d07400d10510784180028a140781c411540603000070003000480389060b9171030921480030003044504072000e0340075030940040c500300341e46c51302d401403420340b0214002400c0c0d00c001040b4400c1f281c050002c00180d40009580741e07a04000b01c841405107050100803c0c204443c50350b02070710442c061505118240004141e02014100c1103800b03c98202c0044c10743c540c00d005080f64004441001540c20902001840601b59140300e8107100351032240180b00e071000341034028582583e0000300700c40700b4180b404007180042020f00d080b0820008044601c2c051139642e008040d0001d0140d01c550103550300c80d21000e0003c0d120000000c002405040b01140c5c040100c0d842c04441025150034071421100c41411b1a10310b078010b076400c609460409040308010032071018081000f6810030392054504003072110030310645007208941c6484020031850b16078015030501e50303003550041c030704030ba1103404880d0101140d13180 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 633216025 1250 633214775 633214807
    0x1b0f0d17090d0b01051536040e0a030306051e061e1b0708030f091306051903140a030806010513030204060b04030b15030717030d0f021201080703080d02 67
    0x20440040c40c182c0c82d04400d003030a007541c1c1824064903006d208607410003810001c800c810703100b104104c0d04101c000c12034404440f0000c4000754540c142c21032040c04044030550384c0d60060480c200301c1e060080010405c181001000c4d40c02c3d81d8806130264218503805404240c0d040c0d00305900d61030aa544c0d0f65500003803180703003c0c2d141c1b0580170055804c4000c5840e0101040400c10143c0003000e4204982c40c054494000c41d807644921300f40786240780c0003004451891b080c508515200f00700c01c02c0000811a984a01084a010003410301200a5103022403d20420000d0260001001d94050060120748840d56020b00b80760310140c005814040045200c5514018081881000c0c5d9405042400403907542c950320035003900035020860f840e074000000100407408030910700311503410090043c41c0b454a011860f0141040000c1001d055000421000f002102d0718056002d2220001e40016a280c0150021100041042e044104641c10850b4100007007124807050b0364040d005003c006a40d0700941d0308020385 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 633217275 1250 633216025 633216037
    0x10050412030c0c1a091c0f110c040f061505090a1202150c01020403290103031206170615090c030a0506040905010912030b030d080c0c0705030307051b0f0d17 69
    0x340360b41011300e01614400c07124100e8080d00c4440300301c4882840400310300c000791020b03c200b5000034800c5003d44421605c034804d80700500195000750340b042c44c50301e400b150555040c000e000c10321a80365001041001c100b01542c00c051200307031070404c1c205880d904c005070603245203218040450540607001c0081d56136000e03518004001e0961400c1d40e030704102d0a02030103504241f00a803103074505800c3e1b00a1044146150781c80b90048002c0741050f607821135500741c40c502142071720360001da5a100d80100305140c490792007121f019000c07c0180340600d030a10325110a40100c50f021400b5081080a00094008180651382c00010000000c41c00d0340c1c50f2004140240340b014406811507080100440c24800580c0c220040442203950502075603070301505041d0344407612070008001505010028041072050005000303030082c20340550317200e03666444c0021310f5078001c000c0640ea83e03000924030340d000c140e40c040e4044c3d8061080d1080049030a800340018181d01900202408180194038500c00310340c4000100c45c9 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 633218525 1250 633217275 633217283
    0x803090c060403060609060b0c1f020c010f1401051203030703020d02090a06050d0f0203010f05011103040e0c0406180e070e0301140c120a0935070f0510050412030c0c 73
    0x62510f5403030074250080d1180c0d203d1030103c80c2c03901c00c010800d45102c204641c2140b681e1001030101458030302280386103a019500f03211030395030b0038800618403d000b070141103400101c080020503131130b20040c0e440b102d048041c0e011a03c5403500d090035208408003c002c1d680c0c0a20035041c0183c03140822451040648900314020b0380c492100c800115444d50048040c0a000e078003540204004001148180101c1c84207001c0d0203042c2545c000d081050b5031080700d125000c006540160ba0900c0c0ea50610900d2030541500c0408540d000418140421030380070840101103078000b4201c2c80d200d07251400c03840820324064800c2c010001720081070316103030724250003406407034090b00003103d581d10305984841d80d0f641012160f80345420384800411000d580318011140710f590480b030703001200c0350f4855031405808641d100341a81ca0441d070426a5180003850040c194560280c484602c0280841c601036082161010745546943c0c178060501012503424011041d882c070490a0010b091410800240c0b908800850018 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 633219775 1250 633218525 633218527
    0x90209031e1212070806040b0a0911040806041208070201021305100513090203070f180b0912070b0a081f052803080c060717131e0b04020f01020a03020601030803090c06 74
    0x941902060000f90321540c8030359205400d50715180208400c1d1800442071b00d901c00034114050209507040e6002c80403d00d4200000361801d9500c5400c3c3c0e0424400302c13010740e03480c0c0e82580540070454201d00d00a07800f400310b100862502c408100c200c5521601402024024100782d403c400515008034111868003124000300088a55104914070295000b1a4140d000030f1195017a003000900404d603103c00c80915806448105082840300035130740d007108204a41c07103000d100c6d203040084c00600c40800503008a44090795100d0500310060700084018241c941d619146d2044080740e5076500a00c038023034480480e400f01507080308030320f4501c0301c85003215000303601000c00c03c1c00010029940c00030603880561205903103c9a80306d0006a4900421800004043d50600009251001e12840380c401240c41481031400b0391400c8111205001013041044608405510a100030341c0b50205060f40e051a09100030b00302101d041d50000e40710441880001d103005001320208098980600c00074910b078030042c0c805 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 633221025 1250 633219775 633219787
    0x180c030f02150309071a0406090b070303060b030c040504140106021c030b030114041a07021c050d0c080a0b060f16062417030316050c0a020a1d01090209031e12 70
    0x317803100d03911711410003012054072102e2200505072050354100c0c0c0407615041200342c940700103900c0366801400210201552000e0100b000d80184000d140984407840c0401d03112030402d401d0004403102c00004010000c181001000803560005640389050441410b42c00100203103041130303028000e00c0e10090f80c075502307104c000c0030f40500c2014603038401d50091424803400088004100e108840c2030700d11400503007147c24020b00304007082d40c02701810390080c688980703040c5540100c00b04840c1d03031480320000554920144001815280103c1000250484289103030001c030f440c400380301e40306045d890782d6080030f08071880090080a40c0112900d002c203104800311010185807110306401c042c05420551020004c025500e243c0001c141c174418161500c040e41c40c3c4445030f0050703a0f00d8104214981c07051240042c2c0d900181c0b2200701e080010020600340700d1070000b07009030a09141d47e05030070400260b44180010cca0642c2c0008204008034108461440110030b108a0b8509010400e85901064030000400f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 633222275 1250 633221025 633221041
    0x30601060215060f010e0616080a031d01140a2003090105090601151709031b070f050d0c0302090402060c06070503270a2a080c010201180c030f021503 66
    0x1c4103200300c003481e5110b00c89669040c208103091001c000c125001442e030044000d060b003043d100401c0020050a540103940fa900c2e41d840203290f210060303000000c1d44600011200900c440b04921900304c464009000380d010105040c111808000c0c1040101c5403501809107028035100000780e030f00c02500351125036030303e003840542d8007800064800084500c45c41c0c0000910300d50070090980840620f0b929295041c2c1446c1c0e089149031800340240340d40c0d020400016000140c0075400004142c4158054101185050441d01900035203a01481c040c40c028030ba0702d00040c58040000042d070360704560500190701d132800480e904d401612303d04989445002d09000e45c040d005005140b0074200700d000403511461091000e00742002c4604910810380c081425800050b05102c603007401f5101540d8100c0305280d40054004500c0e03c298003003150342c1c00152100e021540d080c081c0b50074202c00c400d03034000502083e81e124540e0780190b10007d04400400e0600e8400c6607240341c10030000d440000040c54032030a000c40e03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 633223525 1250 633222275 633222283
    0x2f040b0310030b0f0c0a030b2701080f01270305090a0f080d0e0112051f09091b18200301031208060f06120603030712050a02070602011803030b010e0306010602 70
    0x29107001030000300041003055003003004d5100d400301d21070082c184460490250080d00d100e801c2140c0c407208039a03a5040c1140b03581a140e204c035425811034a269403601119505141c004216100c43d0b0341803000025000311012121070b804a8045400342000e075950904403241d0056203141c0d540224030010004200300074689120541b58000251444d90101da4002d583c454403204145022031520310b141c003100344680d44643d0340303c3c5038240451802d15031b0003942480302160750451624142d0390140f64080c0074400c201800400c0c6051a040000c0703042c04084a00c290b2005c0001e651692200c00c02e8040070710381c10030702001c814821115038480d6107910781034005e9890441d241000131001d000150f441d1400480091910078041e0919103032040d44586008410380c000c0c5a5070f018807007089800c1c001344903400d51480040c15541c0d4240c96058099001303040010f1644001e00310382c180495064030001640780612080e500d410006030030169400161007103a18210301c50380c1070007080700000342190081 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 633224775 1250 633223525 633223529
    0x8092b090602010b010e04020306130e30090d0c12030e01030e0c01080a09030905030a0501051b0304120f020c0315090c0604080d032d09152f040b0310 66
    0x6211404940c1d100c0300128225901c188070035002030180100e41c1c1c0d05003042c2d40255000007001c2c11288006001011036000c0c1c0381c0c0002058919844803544a03107002c24154007074501080b106004d01045042c7c0e00c1a400d5010b0151791a02c90801c2002500c10080b6420f4000c00416802e100c80086400e00d003009041c00e00600d107024007003400c00d00c0f0070703498280100b202903241005031038a0b0170300d8440c11400402801054812810721240c9000070603d43c0d006c0000700d008610910021410340340261003048800311281406d20b05803014000c1c000002d68508210801010314540110b01c451649412840e00050786001038144c00390b5500100211062002c0d280b0801c0a101215901d020000c20711080e840b582c0b00390742d10b54008294004e0b00030321030741101c1e060030340d01032844606c0b10b400d051144a01c01c0f00104500c4403030b030f02c81c5c8003801c01410f000c8240403230100e83d0701005000c01c02d05980307034541d0721402d60700e080000c0112a0400c050011066a01504400d00056228a0300f0042c00182e01600c0c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 633226025 1250 633224775 633224777
    0x510081504020a17210c1b12060106020a26130f0501050a02120c070f0b070b0106140a0809070b07052109030703060504031209030f030510050a0608092b 67
    0x101a020414860100c6080c0790b04684000134902d20151405c08458001099001c55500004100c581c00d81c6404005104682c4441c41a81c040410808108100c02180000040080c3c000ca0010803a10303801040303110036103401850140701c1d001001e510404148400940c00030151003c50f201c00c4004c1c02c50004016242d80401001d0b0307840c3c0740c400540c0c96006031001600168007105120300e03403000c014003030005072046100311100c035a26041b5482d24034210350050502d810020511000340828490004e0040c600ca09001c0c0b00e00c68402031180c014494019a402441943c00c0400c000f03060402078900103041010f2083e03125022403500e681c48400024440050854800481011803054400c56034512001001444200d00c0e544d204005030200501c290180540f800c40048003210b80c5c0142c0c0d410720320903511803650144558016017160005402c00503001481e100500c4070342c5500c041c1c1d0041d18004d06110415a0700e007100107103808031500c401c02c0c1c0800040b98030b000701d140303c1c15180381ca2003203 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 633227275 1250 633226025 633226039
    0x70204061e0b0f0c03031e010504140f130209090c01090e060d0b190207060c081302030706120f060618080f0606040c02030c0106060e0103230109051008150402 70
    0x52810369025030310040101e01201c04030701504002e0644082c004108a001c0c2d03692140c10603c02c01600760550b0011141030201c2c0d6071203244151401c07204982c0c107001d40012642000b5109030950a2013560710010038031040c00c14141e01080014204000456049500501340c00131441d204d02016181e83d4080f01081c00320b069000080b818204c0b150240f849040c01130581612414251104040c0074400b42c5000356800210a8804845500f80000c0010320f004810200f001c0500c06401408964018803090880d284042004016640840c20004a07419460403403502428140b5280007040c1e00950400141d1a02000040302508910300f2139600320504d01105041d55181b004030b444520b00340d004041c640000c0c000807184d24082d440902c80c0400c0c0c0c4116420300550440789821034103d43c01c141e011680a05209045603410f014054040e08910415192184c5040601c2d16101060089803145616600010250800d121034500140b105008036806c02c80c4d41c41440f2807115050354103a014100f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 633228525 1250 633227275 633227279
    0x30209130c09180203090a020120060c031605360d051006060c110d171308060108010c1202090105070c030f0b060603160c0501060f06030213080c03150606040b07060207020406 77
    0x9200c1c400da0707200d03001c0103007d040c03000f030b4a0380111035400c110880c03021103003140040381400807802c11030144108009000c1954078240141a0203500440a11401c2080b80070000802110b90110280001001c900d09c40504800032140080340701c40301900b0340c0c0d000390007011600300b4888006418a400e07066100c080007110740340d603801c460001e1200c0380500b9442c0f0f4900001c00606041301c00190301130080008a0000b0480660707c403172940581182601e03801c510f1070a000040e0144035160050207803c0c001c004091700d000740079142c400000cbc605844035034041503100c41c50f4020412154040d500c0501d8000d0780c0c0c0c032858448804d120010058900c070701d4200001e559814400100c0f80550074603021344003c1758560f281283c4009180e00200c3c0c2c15501c48400250841e042403211002d011291000b688540300c04036040604121980480300c56800001007000689012411400c1000d4255902c2d1140c0d07a6000801d80070710990f40020502d40001030100184103041e0301400703241c0d00c00c83d02440355039 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 633229775 1250 633228525 633228569
    0x311030d06181808090303040306020711040b030d0f1803050111030a052805090c0915121501050907050f07080a110706021002070510150f0b03090d030209130c09 71
    0x14054040e0f00d041d0f50884070f64400401c060340c019007400000141160303d0261203507540d2003aa00040b00c2104c402d9000881805c0174902400791045400c000e500402c16490f407204020403080040460006000841c004e440a03844110541c00245410030002d1003080403000360300759030303604c01c0f03440e140060710b0000410440c4481c0101d0a51115010304a240208181d407890701c003d050150520346030384030301400450380d500c4072503106100d00f0804145000f80c80e085000d208090300034028030b0300700313030031400c0ca8600f04500010820b054501c29562009660340d001c1c0b0035a06031003508011305040c0d0002c2450000c00c030300d40000300804216030317658a040161006800d566840703680544000360300000090402e030991a40035002c094011000c4034100392121002800300e4000d621080003102c82640306111141404504100501c3c4a80d80c1d0362442c600400e4072a107640c0524040c1d82059000074900c0c4165071989500a020785442c0340410800080b8030000d00304c08018803030303008031081c5490314040b15 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 633231025 1250 633229775 633229781
    0xb03070807170f0304140402070b04080d06060509060304030e0d0b09030415030e100f060b18030f0a0b07140c160302040b061615140403020303090105010e0411010c0311030d0618 78
    0x36050480250305003410b10014060181d0386c45030b00380d080355003407210401045030802886d01480c00798405a81c0e490b415043d1205880319500020306215080106003020340b12441103030342c8543c04d4542940da540c013050018140c4080904050034418426040c0b0400f540c0c08001001101c51305100c000580c401c0310b6055013900c000b0341d070ba450b054005c038103280350512068001000c1e410141400244164844648201c0740d00441021032140356458959252030a042011908090702c1000030481c68041c1d689031a15140010040020048221aa49848a1040140c4203c1d410900c29140c103455425040c00010100f07200981c422030905610580a04100c4211382c8941c00c6440b0070340044a00d0b8440700454404402c0c00b40816554801c0e4909451f40c203188a4001d610030b5026503501e00b45003410718203581c0103800030600980700e10184000506031225030165440c003804c211120f0300044c2230540317a00042000900840c00700203040300024010f41d00c00002c0e500ca405400c603000000841c04000c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 633232275 1250 633231025 633231043
    0x8070816031e0c02091501030e030406080f010918030c060b0a032402030108210c19060b10091502011b02070306061a070f0807021903060e010515040b0102010b0307080717 75
    0xc0050001b242e08025607008881c52048181000304031420b0000001d86140c9c000e510101c00502c150382400325103460945120b00514130030300305006c070a03028804982350031f01d001d500070240710115003407504100054020224150000f4034004005c0d5803070410121409031180000e000c1c0311010705800c2100040c2c807d0f00d058410032001485100300959000c62a0a44d6448515403000280b1261402d03a408200e1025080041803103510034070031514000e41a00c00e03891b01341e486060754018054103035500884941c22a08000c1056010460b403d509a0062119008190354546c07038100244002d600001c1900803603214207c2049120307074651900c000d90003800d0209001d5002000b164011940340d031000301101d400b60050b2031030441c2075800500e0f081702c2c0060b50700c00800300341000c0040c0002c0d446501040c49100000780403c3c5401000e011400040342010b5220399641e22031000380d64400d40c04140c0000c000340c111125651500001581e5060702d1007074060200c8404a03505c4150004180465 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 633233525 1250 633232275 633232279
    0xf02120607020705270903130f0510052a01061403030c060601050c03120f0406180b01090f0b0405010305100e0d050304150f090606030201080a0902090408070816031e0c02 75
    0xf5546082c401000700f42c1140744404a440080000350003040c006041041e401510210010741d5141c100584001410000340d200b11034403142c403c0100300c0341d100c08460300b5120314140b0701140d9a02c4120b0005e404441d8074141074003107054444099402050552146090b140b00462104101172107604041c1d0fa40708091031801d1a0704200f011411650080010f840040d28207410f40b13050001d00d60410381111300c100c07518080801210248024040c2602c2101d050008041c0e9a565072ba4940c0c81e1500100701c10311918045940c0c561200c0360001a680c01a060400e0080c401d02c803559581c03d0496841031031180d0010800e00e0420341800c030840000300510000b5190f01c40381d0555440d9200c1c108034181070b403043c1e1f10a40c0ca4180440b0490660f01c51411054030940740014420700314000100380e0700006040c0c0d210310f0b03d001103d602590f40d40103003a502030f42c8510856500e903e1072134010351030300501142c1e41980c00c104906204160b000f664003110800311002c142d1501070b0110301258070400c6075101035 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 633234775 1250 633233525 633233533
    0x20f04090f02060d0e030a0206100603050103081803100c0309020a05060c06010e04061404080d110307020307080c01020f120405190209150301140705071e030e09040614040f0212060702 81
    0x600107003041000f81644071402e000c0010680c20305c1540d41d082d0313403000d01031000580080082042e4242c1c20035844000d013007945800c018035811a541c0c03031058858020b043e481108aa4034080386654200804071581609000038011103000403c00381c007829000c04124410140d8460100303242c20b0103004d8070800e04043c002089164604145100180005407040c3c0b8290b40326009528424002c4021074015442807410a0341e6481062007d0111030080301110008038040091045055001050301e08050b08880950b039501001c0402500a00c120704408160034008108103c0160141d100540300d94010350680d40702000c461180c4009420413040254455181d5000c2001d20400400041e04004060300000316503044079030001d00705d5030468001c40050b20018504040100d00c0c4080540d0025000e00450005038a83e40a0080d800081c800b501a61440000509204042d00305d19080f420329105100581081d00340700d848840b14000030b9000d04507a29907007044110004046100310100c4e4060 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 633236025 1250 633234775 633234803
    0x6051c0912080408160c0305010c18260715110607050f1812011a090f040209040c0f09061d040312150b0c0a0303061d07052a0a020f0409 60
    0x5642070503002d0400d80d03511320284040c9140d55044003203207030b07214040e219084a45107903103003190075500700180394400c01100850080702081110b5401d000c1d2140303031080c13070369a11070395441c500e5510b403000d52418a480303105000201c00e10810070500c10046265228140c00c0301c01d050701ba9a0750019100e010005c1d200304042d100745000c1101030500301813141900c4102161050000e68805500045000b0340d075968006000c55841c0350066008c000d9041c0d61850b0b452511402c061440840140080d0251807140b0002d810450f00c0000b25000d044250580a149601c03185d000001b02034a00540d40c9080f04c181c0480f819031b0700c61208610559040c0d84a01955a1400340348020b07000f801c04c1029100c0d1510070214181c2c941d03d01034584440740c940108035040b500d080c000e0547d4460b502c8210040002010f40b250403110310383d55503012a043c00e1096541d0000d482d2100c00305107114103d0140c0c140441003074a034044c0400e030300c2500d5008035032004001000400704170845602140c0109a485204aa = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 633237275 1250 633236025 633236027
    0x903030e0928050114030f06040204020d0b0d03050a08010f1809060e070b07020a0b0309060705030709050d03030911100903140a14060103030f0e0f1c05010606051c0912 74
    0x1a00c2d400103100c00826950085404a0b40880500c405400c03a0540c94000510a403614402c910b40b41c580304900900100b49034040054031641d001e0406030080e5000141496112704607007041030958009000e4201a1490b0f00300140301760042541c2900280d00b903000014a43c1b440d508480681300a4124140007094691000d80100007499080300c02940303030f1000444640083c4001c400600450001940c1d81000e44108030589030150000c41e403141c010f20034044840000a03840d036101c03505040069507511000d000392000703042c6030300c1194410034050949013019403640200203607070320440211350b81c19031000801204404c0320307206100140020304200041800f0b1603601c43e010107a0820780c0c410245680700c400d80100401e0100c4900d601000c0108201a401600c04481503064540320200d640c6400002c0d03500b00e269030285e0700c0744107085c000250140d4a0906071102e10b80c007800030084c59540e000c001c3d10715003280c030038000f40c20b001140365a04642c26019440885902c88140c0801140500b0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 633238525 1250 633237275 633237289
    0x6060f091b0c031c140106110a05032a0114130809030607020127020f0d21120605090c1b03070807030801032d1712010311030606010903030e 62
    0x4002800d455038508066150380c0e9210080000303401e41400303103560341310600011004041c0c0d503004100043c503214038042c01d404444c01440c10745109150441d4901c24400101d071400100d410060a00e010001c3c1c0b0602408018100401c50442117001c4281d0308804007007a800c90302605255021ba02c451000034106038081d6100c00d104620401400f41005015400b10f46018011035035907001d80e6468903442e6969407400300424003816a81c4c407581d0b480c40940c3c082407000074002489030281c1400400e810810241c0400d101200070400500e003040509100d0061048600b0309140d100c6500e01000441e150420f00d0009100c3c03a91582a030b440c1000b00040d000d10700d1500c4c040075000740401c0c002c0c070001890207030003003404a01a581d60001075041d4140340030451040003520a0100311894601d0b1549041111050b13416001005030816041d0071039101a80e1042c02c0702080d004440310004801c018100090048007007040d01229466030f078440054504802500020340807075000b03400d1031454034000b0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 633239775 1250 633238525 633238531
    0xf06090a0b0f13031b0f0807031b0e0f06040516050711010c020316060305010b0c1c030b060c1b0414150a03060608010f0f0218090c040302060c03031806060f09 70
    0x40b081d2400e04040c245401e64003d54004070741806010401440da40008804074000e04008200e0000c0740785000d010302e640b05103e120080080001c0c00700c10400c440700d0041d00004000b52100c0f0041032501c000c09091401048805a100301d183c18007180490b84a03026000030500e0a07180c080c60310b04203441c1d000403502c91104242c1048000c8904c01c0040c0c03400c0c04003640e1103201900e00103040c1e05018001e420340340160001c080c2504140483c42e9168070005250240070001c2495010a203500307601103014110004821380c00250020702079041d50000120380040303200391050800065505400c01c02a50044c0d4003c600741003e0101050301c4004901e806254284000c0510048981d20303500c25058512aa20a000596480c8143d4034036401500480d4101c110f07000c801c501e0600c3d0801207030080024098140d001743c2c60400003c0c002c6a0007030481d0b01170b54000304115203880103400b5841d40c82d81f088800040501142c207150404800000f009801881c0040600161035240001d10407850401 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 633241025 1250 633239775 633239797
    0x10030807080408011107051504020105040b13051e01030b030613020918161e053001060b09030d080903030408090d02120f0c010804050c24040902090f06090a0b 70
    0x4000000d010f000034819403000807443c401003510b84100382080341c100785809580100f04148a4100801030b82e2101c01c482c1500e51003130a446e03c501c1400c0400060201ca0307040b4a40103e4100301080300c00507247c0c4d6070b221806099070140040c1070310005054954000340c0342c3c000036200c10714000300189400c00714603a00090702d0303030300900354030b4280c4006103801c50034401c011030b0030001d8000303018008403010045c001e44d445081c6542081d14040108414100821009184001d1151445500e048085080384d80e81b40c044000e00c01c1d1500c03801210000d030701000b56107109215810880030351a01038180d203071003a499240514115500c68590707802a91201c1c16241e4060718130000480141c0e5081804c0d0b00b00061440100074142c810f2410520f00100e10860b076050003540c10810000860010b011035051405488486d45480c0305c480e5110b90108441043d0400140030034040341c110120f5003d041c10a80844070284002d09520a10416106225569070003840c3d241083c8040c0f915000146400c000c9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 633242275 1250 633241025 633241027
    0x1009030c0501020703090e010b0c06180106050d1b0503070b0403080a12050915010602150612120315010807031406010e0a0f060207031110091404061d09010c081003080708 75
    0x1407a07880500326400040103d003c2490354406001a08208003a035000d441d590b22180e18110b09084401d5550400808e1544401304148004418000c203401c404018140902403240505d1345c0d113086110006a0a044031517040860070006d554600020b521003121403c007010303403600d802d58640c0001a40844403860134403461b055441002c261511425200c1c404010150142c0190f8141c641200c0748181d00400c2150310549803010106a481c5010390071013411604082e40c101386507902820183e101a4022011501004000000c0b800754041802e0302c8090ba1214402d544801003078044424280442210620100001d9520350040608400e0558010300c590b203810780c2d886810030082c40c3da401640050f00051410010025a4440d0500c0ca440444010012020300803005142d5a41d521034105c11804119140100b91102c1e441031001d03002410405a0282c107100354011014401e5640803001c0d032034180341000061041c200304d0f00507103503400b029490b2840c2d51140841900400c50940701204 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 633243525 1250 633242275 633242297
    0x10050f09060703050715110d021605030a1119170306120304090906060f05060306090411030601031406160813061407031d0f060415020d060810110c100903 68
    0x1881c0c0e4007502040f0310030740d02c00d50745140703602d40004603401041d10302c60003d0900b02c03010b04019060055907001c9404120041e1100402c4007440c5503504102030140c00c500000038580312040c1d002e041c90240c40c1029040720070f180710041840440100602002d401007080d00d034090101c0e40e6440003150400c03001440030014010b40300c0040e095600990000c5001d0350350700569020400280140ca0040068103207092940d881d01e0041a4103200c01403001d440f400034200000c041180d1100100491200a000c480345ca603103d02d0110f8a584940158030554800c1d00d00103480c480e0fa02e20304807001d20855440316016180c040b9040c40c1ca210b00ad004607075664644050341844295480c04602c0340c001d40e40e0202e49003e00e0984850002c8a0901d01e62007030704055a400c61507180000d40c1608140e2185100030452100c1450700d00a009d07143e80e01d454241400e600003030100700010444084048040c0c04c102c04001280c04c00040c0c450722106180b00d81012041e080c00403400d40c04a0031040c06810b0451400d9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 633244775 1250 633243525 633243529
    0x30c020d1202061006021908031909240e0d0f0210051e01050a03110d5c06070f1205180607051015090c020f1b10050f09 53
    0x5412000d030100183e10150400c03032202250b0088000a01300340c000707440401070754881640194540540234103441e400001041988007005003210407200701d900700b004050110b150a41441842c0c00c0303003454502071110888582c01d0180b00f1f921090b0840c00080040419106054a0000c50000e42600b980181040032403004142d002d510e100b4640e40503903920001110061100400c01a00036034025100e144060001442d06114800c1d200c2d000c0b604011200d1041c500110b516100c280c0005900b03803a144060320400442d00c2c1d40c40301c221078160003a100790b0000c3c02c00682c000c581a01c0246403040c081701110500b0302000404503280214540e0781504956121803000006942c6c2550010b940000c1107600f0100c99822030a400c80b04480c4580303459950388a142d55480c000c0303d1168850340d41c0f0668083c00c00d00d6070303421000f4542d03420300f841403103a1060041d4488900f002c08803441c0c0140f0100c03280840142c4251820b0361002061581c241060480c11901c07600111000e0009290400600300c040d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 633246025 1250 633244775 633244793
    0x9040c110a030504170a0503030a05090a021008070306140d060216021c0c0504060609170a0c06051b010204050d031101140f06130b0604050d03021518070602030309030304030c020d 79
    0x1490183c0c4410750355510f0300141d80000341d5008440a0304c0d80100c03134a400007460105c201c1c2d0b0800f14050010400d0b40712440030358285080020001d5000344112009031780103402801062140310651401c0151f20b40e078440070032031070491664040e170101204011500041d00769002d030440d0044d42c0318540c1c424240381e000c42c402d058000080c00412a540300440d00304060941c0d01e001810003960144100351900002a100440d0350003140c0120300c40d2407484002c07440030410403099035001a13094400a54801020380103074001e60700d1504590400360741161030a0305008880c01c4440180c0000e00310300c01600c0441d540e40346550901925500c03030343d51541340e0010008481c01281003d200303407003a041020402c08100182040d000913141002e0300e0744040e41c2c480056030304850058030325421041161400300d04040c0320580c24580b4004500c24440b4108101c0d8107031a03050041c1044400694480038281c2c0c2c0c03800101c500b08411782c010000100001c3c072548182c2001480904a44011a6241d03106448 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 633247275 1250 633246025 633246043
    0xd090902070f151d0c030c042d0c020d02030403020603010e06060409060e1603092013020c030405150301080c0409020d0f0501330e0403021609020a0e0406050609040c11 74
    0x11611141c10010802e13182020700d40ca420003a004090300528100032030f455900d04044140314a030b0301d40c0c00d605081454060080b6041c841c0100c0713050740505034400c50041091b000c0040051040116009038240000115000d13a80c00910940c1141e28200302d090244800605c1aa0824424040040c0405560141e20040d01c1c06074400c08207841c103852100c4010030b902c0608401c041c240b841440108089240f20705070fa500004003000f0f500380903400329020348150315581e4032041c13000901c401403400200190055640071211700125560f4003501e40a240428043c1080a8004c0106204545000e5003c1c00e08144040c180141103199501d880c410020454010354190f51070304601204041008104181e0300308840f40c411601d052946031a035100401d0107005060788019000c10185402000011b0b1180842c50032421001c0c1c4402864020350032801d00c10f00840c0e0484c602408916090003203d00360340016004608100b03503803081101501d00c2c04040ca05028000c3c400400c1c40100740314460b1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 633248525 1250 633247275 633247313
    0x1150905100215070905090a0b0316080c100f02030d09020103060312030c080a0203090d1202040504050c0d111905180a06050c150402010f0c110307060c03110d090902070f 75
    0x107030703c00790307143e01071080800030600b00400501e8a810700c0250f441c84801900500c50b1f034000920004240c0c040382c9428214420840c2d404e103d08400a004480080c08a50584044d41c070f01c0d450104070300060360010780c2d1450000250300b041c410156950b03520307484040e482e8014540452820303502d0320385256021038004100001b0740c07680c124031501c0e0340100845d03070010305001e011461498080119519506c42d1052482081285601c0c5548614240c040e01c0103880014010005810700810031170a942c0150746102001e030410400c4034806510b03d040d2184a42c1e00600801901500581101d040d03000810655070410b82c002c0e0019a500d071550041c2c05040240c0b60b07955103480030103000386000a0865130a40c0941c9d42d8040100507644a081041c40501a091034402800f19140203290b014440108a42600c10a04001001d1b035000441600c00d078000d0719285410b10800044030340315281c4a0141000c00d0b00507074104960412940107054050040b0003103180f40005a990b10144507410000c19 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 633249775 1250 633248525 633248533
    0x40b090f030f1b0609041104180504120f05120c0d1a0609011b050a061a0103140c0c071815050306150f04090213060807080312011509051002 62
    0x80450619842400000104400802c101e400d2016080d41e142c4114282c041205044010708540d510784205480c032180004005015690101c4416602504144200050a1456080744460400328820b0502454001034015010f0000c82400c5d50303926007840740c100c01c00500f0411000b680c0c001020140c05403210741010356546e002008000251950051042c40036104207400b90710036070340c078030071208050000e00380030101d10300140b401c000d402d010f002d014102e401101101020050284d1003041491008071840a2603040e110045003201c460003030307184065811501141c642e8940720301502101c0700c0310040310720712920741c0f8150355040750450703000040356201e107030242c0b04ea0400741545c400303400c0c140c00401c42490b049290040580304101c05034011207154500300d01a44890308a003105e540c002d032000d10088603502d40c401c020101c1e4402c0c0700c007900646002041440000c011a1070340380d400400b020b5103034200001d010302d00c3c2d0301c80c0c10f0005201d580e800000e510380385c035020003c019100341c000e4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 633251025 1250 633249775 633249787
    0xc030203070501091d04050a0b01090f0524040504111c0b0108010b03030a2105071d010e0609090a1b090905070311040b132303120906070224040b 64
    0xc14507090094010905000c1c0b100010b22205100e4403c0f00b000d10000c0b040b00c1d0079a01c90741495810b01d6100e040152111149100106c0d00280c04d0300090792146203018200410380e02e6206006202c045810400024114000d8201540c42e242e0006a04980503040b440619444007000a1a00340003500e220300c1020700300f100c54144040c1040303c9005200440080c00300d0545200040d499200b500c000b0f10511040317403011000c03000d140c1810100300c40031100030000360804660180100308a524002e51203005014503030321030b5102d95070301500348102a00b007504100c0030008108910100600d10000140d079400010b50039000044125400344007900d0765100300341002d40305c4080e200c000f407410307040c50700301142210881c1e6014105c038100d903109498a91201780189090440c04681d90080404008290000c031140a0f65100d01e8600402142120310800c01c10400f94090302808032440e40c003400520003000503080492460307041d07503220742e02080008600800c0490346e4006400c898441d0b400410742e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 633252275 1250 633251025 633251029
    0x40f0515040b03061b0d020d06090e0d0f140705011517101b0f1806050d0e01050103170a12110d06060509030703120c021c0c0b1306080712090c0302 65
    0xb46044124194064500340c076040c40c0c034090392084a505840000070004083c40c000302258156110b8058811041c42070603602d40142000c0c084d43c42051219000b00e070200c0045500a18041100e02c08540701c1c510341c07418100c0124a81c0c0c10625055656548440102000191001140028141c5d06070b2050b40b83d0300e07228038203150801c00b20701040c06914040e01d00d4408004441c3c4801d140b081c603d0b000080140800041780d403043ca00201c0b84000084440200e1607a4020000d01b54040600c1410000c104409969500369002840050040700c00d60b428134540e10700000003008010480d00f000000405040110303402c40d054104100030100d004544480001c00c01e01800340205400d2500d1802c06800000198035801c0382d00c0b0040800b0701d10603046880783e0060540343c00294000b0310602d5542e0005c802d40c1c00101400d102124090303180a000b00c1d51a03141b0080c0c2c0c0d003015690350401815030a00c0029600d051001c0c0c410350074441100d006012083c100e0041c02000340c440c100f9107031420310b5441 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 633253525 1250 633252275 633252281
    0x12030108030a080c0f070206030a09060e0a020306070e010903080d06081f0b04020906120711190b070804081801020c1e0a060e0105092101020f1c06060903020906040f051504 76
    0x20854113082d4081000441c5020510199178000350110b40d019030f41d46603034519000600355072800511a900780815102c591b100810760a941e18029001e03120290307100c0e50122014401d104001d070104010360814004600341c03c01906100383e07103200c00203243e911444054a0a2070309034a060304201550201441c650b2240107603100d81000342c03415410104040c0002e01d1703034003508540105002118002a02041c0305000c00014035210000b030b50342d120b02100c800209911960790690303110002c0c0022a032468413900c110351166400c08615402c242030011080d40065808107100e04505c246101d152541e030302c0c2240c04d0601d00c030442124a408100c0b03401c0c040c0041d506d902070403e004034001501c0d202d9800c0030484803001e10803502408481078810528080a0070520b40440300d600c0400e0842c003000304603008100c61194074100d619190290b82c0400f041d13503503d014080c00101070030030810042c10217640c0b954000300300070b0010a141250361620740459004030780c0034204242e403415013141803c1a01c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 633254775 1250 633253525 633253531
    0x8030a030f05040b0604020705120a03020a08100608131109010b0d0f110405130906090605010618060f0f020316110a09090209040209070c060606032307080a0b010212030108030a08 79
    0x14100340400d2425454181303131114000c1145010f00d400103000401c10034207020300e910b0b860201030b8054451408842c010000d401050f2440040740143c0c005c90803400c481313100c2d00304940f16075440e01030941d20010860030040c80b0300021140c03103180f01240501d81e650380580c14042c00c3d81c0e202c21902c0314004e515040035100941e240fa82d280307150080e0540c10700210070884041e1401907880940b010348180402c0c0003002c0c8044054039031850490f04070104162900024103c40c05544d0b1060002c80c00e403542125250540300c2d100c0407544008801d01094010f030f00a00101c01c0a00640741401c240d9400f034a40c00b00080c9080f1804c41d4540030080052030050201c0015008170001006620107070350103d200000090701c082d2103240040d0014800620400c0304c4804a42d201000307105080c0c3e50580540544010418007640303c40b00f2590400c0f0030754502c6014460101966880915154081000d00514089100b0741c1180108501d00c000020b40e05c1c02903009149100c001c6036200700c80310000744a50006 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 633256025 1250 633254775 633254801
    0x20c061807090c181509030219030602070c0f05010912031826010e07051c050c19050a150e041d0a08031902090d150b0a03050c090702030c15190608030a03 68
    0x403a05c0d1034040d0b07400303482c00c4103580d41a00e0304d40d8190862015580404140d6200802c002d000158000400c00030040240c102d86c01c1025051400d82c0352030041d201501c840c0110b54024802d0149500401d22610034103840b41c145c0d030b039000c40c21911001d240350f805101384c0b482c0705501e903106e440303842000091007909143c1402601a0103080e06090014946d08140c4800702307681d210f41e01c1c03280244141848240d10381080149a100600c0c088a449101100148100362240460040028070710540007000c070a2034919503114080840000c0402c00180140200a8905d408400b03c01802400401881c10440d00032440a03445c0d280c0a140710440030001104480d50a006001040c4980c4403414085030041e8044c40381d03030000340b01c5090b95000b003148280142d88207003c1800041405004a18240240c1003903e880031079030b40c1c6510a9a8a01c0340380303080250340d440098100c2016001e55569078116070951002e1a0b5140285800703400d884064000c4081a0400640c51080d0f60300f51007826403000007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 633257275 1250 633256025 633256049
    0xe0a05091501050319060f0905150a031214031305010e2116050d030e0114250c02030a05060906010603140a090303140c040f09020c061807090c18 64
    0x40c4522804188010700c0c00d506000c00800451950766600300302d580340e00261501001220759840400b100718450303210b5411007503c0c000200c1c144440c1a2910b2480540c013070044d581c000d25584d600c0b030010101c080b10100700b10000350740b04000d01c070060003140103000d008526113143d10203080c90b80c00c4800d802859901c1d070780030418000d400c080e1000d14403e40305490450b00d4a03018100240c61031030004150041c078070b0042d04082c0e115190198000f0041c20300c00d40c000c0042203d00b003040700f01c001007030b1813074040c04a403c0c2c100484401030410380c0100e81e003980340169200d40ca40e80840d182c10038152045915803c1b040401001075410081d443c01002c440c60207101c000041e60440212080c05040540c2c402d868803041d1003890f000740c001c0d0713071400602558040345141c210310803032041d0058003640c280102ca03554001843c1c00140280e94400c001080602000d8580070f0581c0d510b0480e0100e035208074020710900042d1011240b0400a6802c450340b5120b5043d8140c8060791020130080d0015000d03d20 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 633258525 1250 633257275 633257281
    0x1e0501140303031b031807080a06050901230c0f07080a17040b010312050408150105010e15030c090f090708071b050a1403130b220b07150b0d030e0a0509 67
    0x2c41c0300890588040342089580e51106e180b00c802c41414008980d22911507482d0010f090800001d40003402801001c04111607123806a10038280e07008440c04c1400a9003411001010b603604072100c80c0c210061084d45464600000e660940c941c00035107050b6203401c00452449403c680003040c0f41d4000d00c2c124140c0c00d2919182e0307a4500003540c1804090481d114400e40011001d0041d0300b1107000d8540101103403062002110202d084031400d008027800100445414007007414002581151040d20075507250950743ca4101c860300fa600030381d0080d40d0001c1e180114192544407041c0d8503000c1c0c40f465a40410714648584090501c61025408120b200d10801d4618007049000c5110035556038051210000680f090100b00d20314007a01c50041c00342d54512400051805a400040000c000d101d40d0009070440c1a09112071a01e84510038482102410403401c4001195202c400d8582d00740894006003d802060120b242c510401808501143e241500c2e07100515014a13404002c0c14101c40d8090146 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 633259775 1250 633258525 633258541
    0x60c03050301030618060e1b19060e0301020904151d0606121506040f0314030f04150201111201170f030405060c010905010912090b090a0b09041e050114030303 70
    0x100c070510024000c0303651541c51000c1c5180c29912620281c1e00f003078040c0a030003c1c01c2c000d10307107503200b1680700329051b9154082811541080c0121000c41105c154040a40c0c0385080c00c25283d54610894803907155508108900c01c5a889105000c612202d09c10400c103013a00704811300c00e0f28540550004805100307142000119501c0d0790031142d8041d255045408641c03202010080e4030380d844203803d43d02601c0402c000c14003c1514a5800c02c4034011007070482c41700c1456501e9510707803092840d6510a002c0c100803c2c854115a8148020b00b9040c0c0d100005081e210802c4406058000710711098000e0307506801000889007030b5410300c075181d02d8140580000b29040c8007042c0c0e43d104a200b0a030103244081101062440c003940311038241a04613000f03004102c606d01d0880a11104100100040384074075101094004004081e10101070001d0280c403d510306140024481d5000b0411842e03000e03445903003461805114102c81410340e4500c020100f00c1e035050072101d140800441c1e0b0020b00030740c418401c00c4258 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 633261025 1250 633259775 633259777
    0xe240d560a060302100c0614040602180d05060106140412050c0a0b1201060e01110616030c0c030207140409052a01020c0a0506030a020705120a0305070f0f03050901240906060c0305 79
    0xc0d45d61428803109242d400c0c9080005841030a03c1000e040c140d583c104814000150024440d96141043e08e070030380301191082207165103030100051310399030040c4d00508c1034900404031441011400c0e456542000da0340d030b01c2a001440381720000c0f034254012400400d00384c01d0045c810800f034010040042d06145101c0b16143c02094144506402c2181c02c070010038450340107041001d030b05c0703c00d03d00f0b0b03540510b01110b4010000205a001c60f00191a01f141140300510070046102d131540d155010700480c500c0d107207901c404806100c4406a020741c1d11248240011020484600300c10a01546861989800402c90060800b0074502a0543d080f403802c01100341da4109075842526070071142d00c1d4403030300c0c2e0841c204024000c40e44010024400c038a501c401407040702028041038075650754184500d03913420070700700c0d44249020b030140d003c10700340981040814000e80066074132000a40000079000f80709000c81c407611901c1c40c80d802445a00c42c009008e042d4032030054101811403403c20b91140c0b801c50741c00400d5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 633262275 1250 633261025 633261049
    0x801030201051e0d0f0b1504030510090501020f0d0905060c03150631241d0d021c0308220f05070e240d560a060302 51
    0x500460303800f0004102a40600b0b40b0081031211008120850795840700c100101001305125115100d0308141040c0c6451050803070782565441001b8080e2900e0f102c4410000d0070019408895654083c170030f12004c03425400140155004c003200220786400241040c0b0f003007040151402c1d40c00c500410801510101d5041ca0b2102140103407803290340c1300624051580c0c0000c0c1500e08800c02842140c10007010301d0080c002205440c050700e83c24115a1409041c03a2481c4414584000410011540c50542d01d505649101c011031016041c0341440555600282d01c00c007290710141030980c0c280c004c150905030b211688540c0500c50b210f111807a0100c0c07040c03c0003803c00358000207004a42e002d500702c040180c140400c10080031051070040090900000c4140182c04407100c1d0072450103000710b42001e0b0300d00100c40c2802a030300049030004841c0d520800008041d101d01694202c6070305450404a04103590045889000c00250300050074000c510900c03000030380181400c24414242581031000da5950004054 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 633263525 1250 633262275 633262297
    0x1803012f090d080a14070b04060209060c070f081203060d0f0f2f0105090a060503181b010201050601090e0a0c0e0319030e01020a171e07031d01080103020105 69
    0x2600d9446039410204510400880a8001d11802c04080410101c1c201411005816450711405031010700c41c0d24005000d07800c40540004c6624001c41d0104040342d004041410020b00054030f044900e042c0285403ca440d405107041c42c0c903900d4100000402800351840402c8020009451420030f078000030569201d20402800260000282c0d44c200140d4450803a129540102d04403801c819441e200314078085020100c50309240c0300c0050b502c4541c861422107146550003460f4a8203d801c1280468064000034444000c1011540384091400001c000f007402c142034080076004000c01f40b400090949101078021814040705003c00d000c100c411700380d05540003d8005c5d0004001032101c4040380c09806140d051074240c001c0d07003d09007900440c000040072040c00f0b6202c10a22035004001240c0c0c403800c0b594080e0046410820007001529810000c00c40301c41041c01d03180391800c40e02c11030329103071f40b00070022800f1446040691610118003401131045981c2400c00c400a50725540003c3e140e4450720f20a14 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 633264775 1250 633263525 633263591
    0x1008011a1201150c151a0901150305100b0d0605040f02040e0106030c1b1101090602030307211b200102041202240d06140301020f19050717180301 64
    0xf155244035002d106921500040d51180c0c03842c0009003d00142588009045070912031400100703d4240b0102c0075048803011001010900e003961400c80080c5400703025062489214a00020041204005081000303001c1000003903962820081008480540b03860340e1545d40107200810000708800220750448000c2e050224210b952018116100300141e5008000031045c41d6840c401d0000e8000141c0d14481c2c2a2a4405510740310041642c2c0ca0004560700340c0024410140e00302e818104a480d501d01020b625000300341c1c2a403041210314250f202c0c0c4800400507088a8813061117082042c6649400c0503180e0085103400d041821801c00f40c801040d001c2d024034000ca070750020481c0d03102c205c0411040e0b00150305464215a99405028044a1045c0d0000d122108501f025915040c400c503007603010028001850f05400c0441140342040f90b0040d0703803d1090038001400454030621820303580604140d64a5542d500703110340100c00d095001025070080c1e14000400f00300c000c003c1580c95500e842c2c240e8207 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 633266025 1250 633264775 633264809
    0x9070914030c010203220810021902010b030c0d05100c08092404080924130f120f14010e010204090e010203070c06020f0c0a0c0e0702030c0a031d1008011a1201 70
    0x58918818940c8400d54621503092440174055290340501008ae0032103843e04c4090701451005ca01381d510300c80307000c4c2d455080105104103a00e40035400c40c0440d80300724140d890b40307880380210f41e045130b10f1403806402095103002081642e103c113200701500400b907403c84a2a92046004000300080005c0c03000304041c40020b65440d0594518440101caa1901490071190420032070b0240c0e4140c000002403070090103800000b103134a01619a9110a071200c20300c20000510980d151000c00e000e54007000d60303400c580d8400c0750701c8038182802070500e240c81d20340016964501e055402c004403901c2509021a03a48180140700c0d02a0340710121103c0680c000d17401503214043c0180042c054030402c4265000c9108030301d6410104454003062030215404c240441d02c82ea03880803000c0e0707203a1140c4640c1440030f40041c020740e00040d01801c01d450030115641c00b02d8030101076400110300c008801c3c2c05c0307000100f004040104071a080800c0000802c580c4001d1060410f607591042d0283c01c1818007403a40440210030203 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 633267275 1250 633266025 633266077
    0x1b050304030905040518010e0c0123160c1e060f050a1b0302030408101a030d0807080702070e0c0c060109060f29130810050f2409070914030c010203 65
    0xa401c03543d521500030803200000c440007a5603418852272442c0468031811074500c42a241100043c04010460f42003441c1100041800e040c0301c4420204030707281d020021001c901c0750036402a9038940d015288603005101c0c10304401900024807000b550080050404c21486281c2d408008107480c450714402d03200c2c220185240980c11400b6580240c0c207203100d1108942c5003180282c22140c0c0d02c1a242e00d04203030010f42c85003032680318040501c405010403081400b01c2c0280b4415040113502c0090761055400c2d15494905c03660003044140d80188500c0c8001c5141c08070210180122401007031600f500700099480c1c0041703148400141d1103181c4d82011950b400a071441c41001e8140461050901a2680d80d40d81824910020510703014109452181107204403091820344645d40c000c2099403881c5c0190783d40c540030420040e4107500310075800160070000207103549402900a019071034a841c0c50000b9424000617440c5000b440090521960000b03201c11400d98004c400c40d0780e81e5840310703544010709008d051 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 633268525 1250 633267275 633267301
    0x21516240c1d28061e0203040302011b0602040608060f09011802070c0f0617070503060a03150b040c030e2104171e1006050409020f0f01030e07091b0503040309050405 73
    0x8441a50304203c072220600c00003400c80040c2500c080e9140d04200daa00c07044c0555804d1140c403491310141c4d00400081c0007640c06110000c00c910034a411481403021180c3d1039500366086544240e0201e440c5800740083c03490419280e00307103808280c1d012484c1e589007140c034114480d81e03544400c031080d50005650051056241c454806000240703104410340d6a40d1800502c140348502c15060000105404145814400c0040340e008a100030b1003001c0060464490800a0401500000005564480c0f5011540700e501503280498a40e4a001850240d2211080d09100216410050005d84001074901d2812620309540590741d00748803d03188003000f40745092030446c00808840e00e41510700360301b000284d4006403268108465420a010305941e071028002a507107541c00095000c80c1d0000c021241d0300b84590740c2c0004010500d00800c00c0c0703040350303241410451140c1048080a40380d481a6100c50504c4a644540701020300d40a440e506e0070751802001d05016008807481152a0703800300f40e001941071 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 633269775 1250 633268525 633268549
    0x4020403051f0516020a02011206030204090f020a0f0b0f030a0605060301090f0c050306181902070501060503010513080d050417040b030906071407021516240c1d 71
    0xa03088511400040d80c1d1042c41e407080784900342c0c440382850001100c00000807812031420140d0b40007409805402e500566005507104818985a56560000009640d0341d01650342803e0140e400c826001c016170050001700c0600e03030009241503404080812850b0350341c40885604902544085403a40c4403160038001a246640c0030340d0344010007100201c3c80c2d0030903078841e00c22116042001c102c0040903003001c1d2818041103620550050805800006061a103444190301c038032800d4047d42000070421900e4201d0300180c00c1695260b645180c284000e0800f4032035030790400352030303001aa1049441d40d030b0071015204060400050355165800300d010846c0002e0005100040d070b130b81864445454900103983c0360011140541c25114440205020380d000d0300481038082050981d840c0f9103110b680a215000c040007014402e841e41c10854144000400c2020040040c421903084030b040108059034803010760140980140b051034a000d00010b1030b0440090501d07441d1a400640240d05105c0006039140714034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 633271025 1250 633269775 633269783
    0x6130302060c0f010b0a0608180120090306220f0512030f060f0f0102060c1803030a02030a1706030309040908070f03090f0602070b0a080c041a090a3204020403 70
    0x100d495590b00c10007160b01000d440c450402002042110410031420141c144608808107200e4404518003024420401c1c0e07000e000580007280494100e039424000c0354268000e030810100104201e005c40c80d062241581044c4008486691028030591244200c0c4174100000d0113404e8505c480401c00106000c80060700c240c20005030340b2803a10501d00380309640100d5440703200c0c4c0140c0100c030310545040039242450385410390040c49242d03240000c1c1714140e8090241040086d40044400360380d0344c0c1c10002003a40500c0e40e4003450704e4072100c40c00136018120803000180316030700c1c10040052a840000c2501d42c00182210041020803481c00e00c8503c1340b04041019200e100740064120903d9009901c0c90100c03005041c901b5440d55440100720b0300c60a180c06205841c9104119103c1d001d480b80d41072079044010101345c0c5203010369804082d0034013528803501010928005c038000103189030041c10a001000600f4541207688507561050081079145183ca000c0d0075081c0b00d400e0030070341302d41d81078502660380 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 633272275 1250 633271025 633271027
    0x101116080709230c03040209070503090c1903170406031b0c0b100b2b270302071e180603050c040c0e0d03030203010806150919090812190e0c0613030206 67
    0xc107101401c05d0b07008850990141c0c4045021402542c499001c4034807601c601c001422025641100b040a41d40d2407015906c008180064003201041c04030f02c0d00c110680103200880d40e124604003026040d6001a040c8002c02e60048100740c1465070080c81101c0313481d90200c4108016569600d804200c1c070042e804c010a14400822092000c8520a2005248840c0b1441010072083c1c4450302c1c4045e1400891140c8a07840d12084200000800741507004031284240140da00c081e0b1162880041ca4040082c030b00f00750750351a0340c10480c0c2e4200004420905445e84024001c80d4199126141c0d540388842e101e40c040c550360790300c092840e803246900b6000b15000601004107041c0c42e0500a0194100380190401c5000c1e46000c0b48441e13890702400d03108111302802000280d681d4038070156800001103010441d80d5110741c103600c0000d0b01c55000782160071050384825210b0130b10041e11201c40d000c03060100225403030140c10001403000002c032320b50702d4007086030815a5642200304031071402c1c0495100070341002e4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 633273381 1106 633272275 633272281
    0x204061b060b2d0d081c111308060c0c120a11030a0305010815070909091103060f04150605010c1e0210111608070923 52
    0x20250800103403010075032010079203a01084140c40c4551442c201d1003059942c21002c00554003c054801c5502c040b00c0760f07900485840354441d040d41180640c80100c8000c0515044040d9001454004585843e0b01390942c005030b41071270080b40c1c00c070b000b20000a098031660405807504c8000010040c14035000e583c00200380340c1d01c40840e84041100c081c542040001c410401000f500c0825a0b00183d00d615100300d9504000c4034000081c02207581e80140000d265001a50700280c800a0038000f840700d017a40b0301200c02e251011a07030740d0540103440400104180c0720f16002e00c500c0c014078010494000c04030114048a034140100b9020074003442c3e91001140304026104400e0344074020240c04e203140c2d5000030b0307501d81e00c0e02203203400500300200e90342c02e151041c080e0300d80c220b5030100d0081c1c140b4180405c45840d8459030154507040d5680d0280c50881c1582c002c0076001e00170f808001004981 = true := by decide +kernel

theorem cover : BRFrame.Cov 633093525 633273381 := by
  have h0 := BRFrame.cov_init 633093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 633093525 ≤ n) (h2 : n < 633273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
