-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4702
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:28:01.572789+00:00
-- url     : https://prove2.me/submissions/969bb50d-c4b9-4275-a554-12a0408feadc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 845503597 ≤ n < 845683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 845504847 1250 845503597 845503627
    0xa060b09010f080603031303111f0c06180b100e012108160b010f0614280201110a0f0f0c0c050d0c03151b0e10030504052d0106050f06 59
    0x240c2415018801880403200000c0e03007941f58005580110b20306500780a0341d031f041081c0400e90208250401300c90011540c04c09801c82c082054141d072011700412070b203048142c00b070304060000c0000751070320700b03d40c041c403117080340d0350121900342c80d001e4400c240039a807249540c00700b00808801d545032540d20b49440324003140c5040e01500248590714007810301907490b40c51310040303414280c100c1c1d811240d00301c03003c21074150000042c50040a1080c0c0d42820080300313080150000901501401c040034a28400941c164400e5111100c880d06c055030942e05c42c22144001429015015407074000b02c0c3d50300904401030740c085c440300d18034a940840c6041043d070500c000d110b501041746004841710003076410080000350140351030302103410460000041011502c0b170034030300c80400100700c5e00611140008003100d5440e0907800703088440725800c0104030354696241c014900a50700109090300f5501c2440d24035a1440b01040a089920040c02444181d07100c8041281c031000c012407050b4080420030103655811140 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 845506097 1250 845504847 845504851
    0x5040b0a0203160809011d0f040e030c0715080f04111c0b0f07090e1006050f0705250b0a0504150e0a06080a1a0603042a0b030a060b09010f08 62
    0x41c810780b0704100d200b4089444076030b011102150103c0340802d05080e1303541c2c02004444c480407660100003400c05480086080c8101c003400c2c80d0b004948412080c8130702d500030000c51b0404a120b404540003e40c1d90030020b08480c1c0d6081944001540c04404101000350524004d401030703400040c02001802258100b0010342c1c2c80402c890881380c500c2c0f41c0107000ca030340c108513640b04030b0188076004c3d03140c030386808028002182d68000c403034401080e0b400d2100580742009800300791640c504100e5521600d42001000134001d00c003008000744100700c9810001008032034400b2186844c4204041e060781c4842c81e001d02d074000c40c1081c1c400500c00380130400065001501c90090341501c0e040411044090750b010540000440d0030800215408509100d24801785100fa105424040c0c82a09100c510b00000200c540c4000361014141c50707a0b0740742003030041460f03140c00c2c5c07058034203d45407008180d0750f0580d4400603001161040d41903881c0102c00141551201c1c120b941c40c2030305035a101c07101141d00e5801e541b46500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 845507347 1250 845506097 845506117
    0x90a05061809030d20040f090e01020c030304080a030603020909031b071a0912060c180307050607020d02030f0d0c0b090106030b1314011a12011e090f08030a141605040b 74
    0x14000f000200440da000a00103403c5000c4208046408c0c80001400c0c0c40580c0310764000b0b40e03c10060310403100340100a0704d41165010050a44d60380310500102c0c080d008e60341010750701040c00130a00c100f881c4000001c0032541c107860036069108424140c100e0720b46406224040708440345118410300d40a00c20000c1c40d021000a20081d03601812114240c5044012221010001d000085045011180005400d860342c804c600501c4043d0170a4003140e0180a00300c0020b004041c00729502045690520004001403250b20449414928032580100500448002656241010408a10a00018090f2605070f07900207506400d50307150b0034410418000e400c0020358454107104410800c0400072f0249003030015a10511002c19200e034010009042840390141c1d209a1401c0c0d6221114869055541405ea001000001c2c8c0c0500f1401c000c0c0c10b00c800c0910050036841e0002c10022560f1003070703126030410090586604016a00c410401003150107075020540440c005000070030550200e03038010000c0060b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 845508597 1250 845507347 845507381
    0x906040b040906230a060b0409050702010f051f08010b240d09211701050f01110102070b0a050106081b07030e131e020901120903030b090a05061809030d 67
    0x3003180c4480f811a030416141e08044020307003080280e1250b0600496070010042103040018a1500c4aa0801c40c0b19a104080c4050b0729000000c0b41c1a000394820348030b00c10281f90500644c54182500f03084001004918000741401c0203001c200071005104120381d103000601034844408662100311a5501850440d45540c4c00070852002c1d01d03110707406103012a034407428000203420900c002c004080400200202d01300151441d000c41d24810507110917044903c1603540c452804912001200c03241901084c20625600008566081082c2640030300d10480c1ca412003004603036200d11003100c041405440400e80303000c0e8065080c0d0941c3c0c00b4001800f03698880c1c14444021191000851040d505640c403038042e01f40d80c1c00c40c0804800c0c2444038042d10080401045140901140000e031505411f05400904141d46207140010103000e41c3c0402c031401c0008051598034501450250090801201c4003801546801c0b00000317910241d5036118002c6004402075030802240d44926001031034055070324401c00c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 845509847 1250 845508597 845508611
    0x3010b0711031b040b01030e0615040f111801030e0307031103040e15090f0601140c0c04020712021504110909071e14060703050417030d0c03050412030b0906040b04 72
    0x2039400c0014081400202c0c2040c040001500c04000403a15445c015030306143c00c2208100300803601040d82c652146180d4101250042078602140c001c1450112051460345030414030a50035600c08003900c204c4036440c00c480c410225a00045040c2c510a000e000c540b039009000f1440002e00275280c5251b03011001003240d0501d0760342d0411621491007070300d5500f207075203540c016030900d410b110403d80ea1140340c0284440307282c204440000c1640070300d104c0419003128049118900d0f00418003c070703040b1210041040d07448003a5414882a00b4a43d1450b6802600c21a1016801072041001d00c0d48504d4101e400d43c900880924107110031500014051203070703406403000c0414007030581891001108440000d0840c0d90781845484400d0b007001d005c8003441121f043c02804002548141200c0555800350038190303200c660040350b00c0c030b0f500503408007819036814100031030140c0380d05a010900c0b450094250402c2e82c1d8040c0f10039021954042c2170a40c201100c4800107107141041d0b00140500c4001900c002121 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 845511097 1250 845509847 845509849
    0x5030c1803010504060b211009050a0209070f0809070b07080c160e1006020708061512030d1a0d0201120519020309010506091e01030f140f07050910080303010b0711 72
    0x640c3c08550448449540b0001d200090401c0451100d181200314034002c202103140780107541c0c42050250951241e92201c40f81802c0003400c2c007030001d80350fa02500251840c02c00010140044c100750403003100040b03d51000600c000c1c0f00148a108032503221070140d141c51182c1e1101450780c1c0c40350070050703900c0c82240401e02084020002d250010032100c0365603003d034280905400030100695000b4011581320940038044414013043d295044403260750500d0840070030341c0110710b02d4804110b00241c1808046146800903916820144901003450002050141100108080d03070051003c0a0f00003071b02c2248104001d000381c0e000b9030b0000d4100d07950006c0181d03545070300e10981e030045545681d165115000e01c4114107203003000941003801c0811b040d515114091045101c0003051001070034030040e41003a00180846000d225001c0103030001514031000c000007007181e58001c40d1245138065618203000443c2c2d00901c0244005030b4403010065032460f40307032205c1040a03400c220029144803074601108400c0d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 845512347 1250 845511097 845511101
    0x8040305030c0c0f1018020307090b0307050612061f0c0303150803130e07090b1603050706020307051206090105033a1806030506060f03040f021e030f0304030305030c180301 76
    0x16800a48001c0c6640c2170413a5082058032902001180e207071000e0360002c0c0040c1c2d401700f06401900e1500b00001080310540d80001e1030924564041c0360013650006441100c0c5240022852240806880d240780700020518060155280e040750b03000029550710307410300068440e4001003c000c100d8000034800e5603c2c2c0441c14107682c4114174030f54500290140410002000c80130f00d550240282c01e100e540b540c54516841900c1c4501e50031a000013500404100c10180070382e0a0701c00c035541084086440386001c0c1800780c00c5d680140c030311110742c100000000e075079440c0c48005981a1140580942100c0b4029211188480b0540034414000c202e0700941e81c040e042c6c8244058034801d0780e6a0b881070381782440c0030505103200564008004240c2800100080e40c0c071071604980b80b4030410400d080d0b0341d650b20304116003508180f020080d4440c0d40d644e034001c2c4c1c1c04200d01e07120101f60750840603540039a076885005582c9128512006022a0061000031a4000103502518840c2d9410303031071039006d07a00000007900b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 845513597 1250 845512347 845512363
    0xa050402010309060e0d1103130b0d180308040b0a050408090f010c05060f1f03120522090e0106050303130302090c070c081b06130b0d0b0d06050105180708040305030c0c 74
    0x45c00d030f100c00c0c80410150391240004004000c0f00c80034515106507076102001000107400340c0e20146200244408003940d40307600501c00300b0740348502d104102003180340041070017400b920240d03056212070010075540f01c480e10499000d598007045207442c040c02901807102d002b001c000d845051043d601c00c924041681444074030710031107142c011200140b520040c4c641100d1541c2c500341c0d090340d4002100380001062122181114003c03400e11070748800c40b6800401c04003030500922401e400d950341d400599080d140d009400804802402030127070715103e4040c140d40b4060392020301910070301040104054104208002d0700300b10b800c00401c0c50f10364213454a202d02100365200c01e0345a8081c0ca51040a01d210b408281c10440c0110b072030302e113400060412100700102c42d0050b0003070100000ba031040a014540d02004280001074090813491150307041038401414244100c500035207145000c11481103141005a20900058446401d1500c581c1c904684c0d03034100a0002030314000402034400081d2040002c91 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 845514847 1250 845513597 845513621
    0x30708100c3f0b090c0910230315130903090909030813140313030507050a1d09010e0a05070f06050702030a0834030f0311120a020708160c0503070e0a05040201030906 73
    0x640e86c40340c00e401d0190300341d1058444420410250b80c00f1841c10303514010610380d890801005504e80e00d0351017030103400b11210100281d2011407040542440034a41d044404860b0094071400360352642c601c140d50969107090301c010b000610a0002961000f086030346e6403c013038000e98060140d900d0307001c0c200d80f840d407001e2544608403d07254410000c1010800041c005400140ca100359260b26146884d03c00c11512040050031040700c400140d8003c01c25030104000900c00e80c1100e0841401c0e0500980301ca81034011a06e4200c00124041103841c01103040781c8180307034068000c107402502074407070b01d032940c0000000d0b40f88902c0303411069821203900c1c0c00120200c8403c440c5c1c11810100c51802074500c0d07810f40d5030542414100200f402e0504121400d540440300e00c00ca01048aa0f24006104000c1c840d26100808862021a405e88000c4903100c01c42c50341342c85250b8614042e6211800c155031843c0a00c03030410403445901c00075800d8200c0390040d5400500c103050100e03100ca01d070341c0e5520513151a00800 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 845516097 1250 845514847 845514871
    0xe010e070308030f09072102121006060e09010f1e1a03090105090c100f11010c030b01110c0f011d0d08030a2403020d02030708100c3f0b09 61
    0x4001c4110344d550480d50010560002440340d217281030030788118101080044a40340041300712000654942000510118903000c0a0303402034007007035151900030003581c010380c800180342c0880e54400c1c0c1410121641a00e40c188404080d0364a0310050102e020300c020203c0583c1c40c0d940b080001d03190b00b14820031380800841444143c0341c2c82e0800d0398900311174008206e00d41c19488540e21081b15201c880c0d110401c604c00703240c0030340c61b80040e0b0f0060710030004407a004070380e541c42e04044d40c00c1c559041d44864a20b04007613890220241d03011072a1a0303507044801080703a02c10f907001e55151096004000700301554100041c40303004a01c07490001a44c0301000e08050710500000401c114916455114018000c5800c44258411100e10120781e55804040d002c0207000d0840d0042010965400b0014903005100a500f10391076286041000c1000e480408a00008694205150013000c0d25580d40500e040c0c1c9080340040d190015402d4048640c90494070071291603544080d140d20903112014514410740901c482 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 845517347 1250 845516097 845516101
    0xb0412021e0109171e0a020c030f0c040c08010f0e070c051005092e02071a180c0402030c090112110c03180604120809011e120501081603060e010e07030803 68
    0xd0400e445081000d04c1ea0b40708100009030b0703080407014080403840c00c100041a202c40f1071040a81c500004941219414812801c00c60300d00140014a01410074058600780519003e83d8016100d82c102800f846145203c000d10601c841480100541c0e031110041c034200f110314036151140d506201c64982441c94050b1140d08129694404100308011040400078903d50110880f10b07420700740c0f5200400100c000d400140c0c540501207902c00c0522410788040341c0b01d009091003210400003650480c542406401948000706040c81c281c0300366485078469201d164030f06220200115003205da90500c00715180d40da00440d0940000030006071056504004c025941c84400003902c1c0350003921241c01a2050004001c10301807918402c00c00401d003940b02c20000c0d180c070880300050741c41c1c461002042d10f80004100410800650040c0c40456415811104000707507601c0310041c9844103510f411228118a105e1002c00003e801175208101c4007501200010340380d03036410012070030100700e640107460507030300842 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 845518597 1250 845517347 845517353
    0x150901260d05120603121b0d0503040f0f14011a121c180b070f021002010504021e1503090604020a0f123002030309010c0305040b0412021e0109 63
    0x189181900c19210010012600032a4008120303120306032100f5450542040810010b80342007085d910058082214a5207600e60700102c480c03000025060f44a05104032035920b50054000c00480307000d140c20a020500390340b866155040c0045818008903401000c10700940c0c0c0f03000c001c3c460300d1208030903035a0b004a100c1c01282000158104a00d005480d500900401c0040c40a41c0384088a08102802c00e0341042074080ba1004102400fa480200065000075000042140c000b1110107224421500d410340d40d4a031100c201d080710f6003140c00039001030071451309049144940924042c84200244135424400c0500c1113200e4940041d0740e0f0810b00d070302c040309100031842d1008510000d00418098950352900d491002003d11a2009001c1c00c1e002c4035038040803000001c0c0d80d5a2024401000d84064458440da1000350785e580222040d10340740d46414880d0101078440c1c091a405940c0103a060405074580751034100c14062100d60344400d5204000903030b8100c05000d81c9409000a03d90700014010050341 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 845519847 1250 845518597 845518649
    0x50a08241315140901091820090f040c05061b1005010305120304030504090f14070207050a1d061309051603051c23090301090f050c01030903080708150901 68
    0x2402c1100807800e01401d0b1043c0d40c0300c06541c281102c901c0080400c0040d0801d2003800707020b008034405800b1a01c038180118030903001100e801000305007074401401a90b601d4030b4408a2000c1030340d0090240360b940108010700c0c5800c43c00342403082c1004090280c4000344209007444e100c0c90240b1201d6003519a401002070000038065100141d0485003c0e51441c90700d65001001446940120070342c0342d0355050401140040d540c1f00011107480080030301104d01300303d14040c0d41c0e04001d2084500c0380305100c00c08250a01e1020707134071801c1c60140c0c1c0b100c160341d1909000c001c1c010200c2914100465984c0f5140305c00300d6400c112003400f0381808050f20791284d00350700382142040c1d035480004603841d10764030f0041000303980290a00c0310f4505408411003e01c100c000150002c1c42040b841991640c00c000e400c200f1b001030700029410582c420340c00c840840c51541c0064003910440304010300440e01070f00010340c4440c0103804160703201d552950401100220f18000640040c403e0b00403107001100303c182c43e43c2e009098 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 845521097 1250 845519847 845519849
    0x5210d0302120103120e0405040302031909080c010c060e011d1605181b0c0d0230030a020c120d0f0902061e040504090302031207050a08241315 63
    0x103140a40c50551008900c001008041c4001011071040c8101c109110f40714501901046500520911a500301818000d50700d8000d101040c654210b0402485105401440d000045a071b804000d08922000040159046021210700782c071101e80311050b90101c8a030a21580084012010b4203618031554040c1311072401004200b20045100300d698188801e68501c0104111152201442c009a41e1000c800481144014551240182000c60320100508004c42c28940c500029802c94044188020303198070050b00301d000d4408040302e00d41e149070308020804002c40d030040740070802510705000d00840501c3d0944500c0005a40003000c01d25503a0249075000d14903001001d02003c0c0845840c50300092003600c540c030440d20040d900c4e80710004c800c2914070b09680c02000c0c020410040c4241c10300780070751a90b010a1030003052030520b8002688113030040044d41e884440c2555802c00a6030740c1c003690040c4600354060254100444009851141c0c1c0d0040802040b04d11038034040f4001841c01c140c101e09140c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 845522347 1250 845521097 845521123
    0x120f0d020a05040f06030b060405040b0d0b01151206030c05120f030703080402040605060903100f090c080304290f0a2f07060306230d0b010816090e0d0311040521 71
    0x410f00754801030340d52381099500b83c030802c07103000902c08420400907034489c05c4540000c01110f024000040c5248000007441084a0350303032640000361340c0b031050342421143c00307020050982540410520140c2442400c0d540c0710402c81c0100d406910b0554072446c13558100110032000039842a00b0801107041501420f00100b900703580c03c50034401ca0400003910f030007034540020815551207481c1c140400766908910700003608845140b807030b41c0c1c0351003802e40c2744c0e0321038040c0c0103140c0410410640065011051080743c04280b02c0b01ca410410102c41001070381d4845900300b070401c09240c080d10074041000a04504a03c400507240041c03108540e601802c01140d0380c004800d0500c1d1410800541c90040844003400000500021400d201c000020315812405200a0710500c202c00c0003191194000071801c05054811505c1400da40d075542c140029900b415404032959000b0240100c0150300a0300b00080300d80701281c0e40303410540c0741c40200f04214151480c54034101c404e540200d103141e0060010b41c04403d5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 845523597 1250 845522347 845522351
    0x6050a050102060601030b0f0a08030c120a09030f080714011e0203090a06020309070305010603200a05010e060309071a0a080c041a13090c0c030807090503120f0d020a05040f0603 78
    0x100d0200041d4035800001c14160600d51a031060301c5032542c039043c29000d000b1008200300c82d11900e5504007a0b89400c210000095071151040407924078400c20b043c1c400400c00340c0c0e540c00403141166640012003c41000403940d002090000e9000110340340c4039440441400000050002c80c4100001e00e07111400074580503151040081c40362410303005c6043e0300c01c0d6400a6003d82d81e6111444818030340f200e9580046d0495103803070700210811500c61540032107030019100c0f000d110842001002401344061080a011030701a40d905807590900c8005598040c000701c0035610000e6640d0103034400c1c07051340160858050800503c0644450308844910780020008841300d04107414604012404096610344c4d44481c0004070340c140003d120b0543c1c9001404e0a110709100c070020021002d0400d818842c0210003007040d090001e8405449002040e040701d078018010809c043d03001c010758035070798072806280c1d6129200300710341c1e03000403058001040119a95039a403903036680703804140114543c454020104046c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 845524847 1250 845523597 845523599
    0x106031a10030c050f0a080708250605030109090f02040c020d12150501110a120c0210020f0604080a02240708010b03090c0603060f1f0e041e110c1f06050a 68
    0x6048500c444013503907010380340003403840c00d2180010209451035204072070600c1121008a80610b010500c15001e40c85441c40280500404140c032909010502554000900510040000a0701c6e41c102d000b41c540190140481c2044c17980102e0260344003401103d0240e4132210704262803560009980d9900c65000108000340301e0344060701000131b40588070300707810040209014280b00006008200303c865005045020040510201400440a051041e0710032003070011003601c581d0011918010b0558240054040e135940d40c4c4c0c80800a800000035a02140300e0845800d11081110301c0d840c59152154000c9495072400c580b000f0641c11058100b13143c4000c040c0203001000d94009905c11000300704840303694403507907a600458155105903140f243d2001c661100c1d48a00c4810582102c0c0d043d140e0358030080301c8081c010600050b0742d2134891508081c102e12844004140169020034100720105480c245411521441d0929202500207480c41484940d14801d829810341d20650005190581d00c1c1080300d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 845526097 1250 845524847 845524853
    0x30903140d0e0d0302031b01060f062f0c15190903020102031606110a030b03060f012907020405091006122d080c070509062e020a050106031a1003 64
    0x4804a40e441030080c480883c20904042c024802d440c10207030110090110092072101880c0640803501c22005412540b90020030f88910420b40c1c140340b20181681101c5d032510003045900c00c000351007407280701800b65024124196440ca0340342d80c01d03141160303007651701e48100f0202e00608100248a50050000e145001c10040c1d0b0048183e400c0d02400f051080351508084c10300ca005800c1c0d0056034041c0f01000585c050104c5e41640c012401490b050342100d00d90782d1130401c101d800701c6080c05200b40340e030045c3c4084000030354001c0710062108001c90b190343c1001c1082c0e0102d020340c2c0098403100c3e1b254101c1d010b180c0080f03200e4481c000003400c4045c1c240441e041c0e59215900c2c403001c8503244880000310f007a000500b907042035262440150744401e402c1d9030342c9400606142c440d0510b0064500c41e491303050210320a4602a200070154034518404031081100c2980509811061412032600b507008000350040803840030711a280065005a081e94061100e1031039901d00c0c031000504101d207040c0081818804 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 845527347 1250 845526097 845526107
    0xe04020a17061c022701060801080d02150a022203140609070522090f0302061e10050d02010c171e0a0e0405060d0b04080406020105010803070b0a0b1507030903140d 72
    0x94040e51940c004520135202024142c4010550050b19540c00c1c0000906a40c080d88e124103c40c00d413800d6a44040710044103e844059003d5108041403102000c610030141d954010090001c0000d80020381e0510501914580e900d0307540b084c0c580322500d56054083c600284244c0e039114031071001602c5070900340782c001414413600c18410360f05a9400b0000c0b00201040e548601c500f04e4000c0c026511600b520301d8000e6441e501113502c210560110164050f0000d50071041a004046895506c074605040c007003805010b0b044281c040c0d040008004403440460301c8911040300c082c20820209688082881c04a1219046091a800e40080c20409503001c40e1b030010418406030300441d030200d2182c443c0e50000c5c1e13095040c034901500400c0000180030411803110000c0049645c60b400900c002d07a81c40d90540d44a00403c84058400001c4e1400101000c203070741c0c4480da601d24000c0212181c02d0b00058a0419500101707001c80129169201c14030901035021204401a603002d40101070b400c15030100209 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 845528597 1250 845527347 845527399
    0x4031106090a03082805040606060903020a0b2a16060e010507020d050c040c0201050a0b120607050d0f020f0903060c0c0a0609140604030807080c03040b13030e04020a1706 75
    0x300101138010601c4140d849a032141c100900384078910707035000c0d48201d00004180640b800c44007107180503000100203000300f6449044035001815203040c03a1404080d0001580980468030185081c06c0426059100050030002c0d0481c18000410801d070100d0003a078400030b0b00350096018414070100343c40490ba8810212a0000c4e41640c41c9409540d951a001c0e2800c403500070310740d611500b040125281240c0c15803004d880345040c10402e005e076046100910094104171915202d00390450b0001520b628050030040c00380081c00d940000f0040a1100100c089070040d405502d2040d01c00100012185010010030350813034030741c4420038a000c1411444c0c0c3c6d030f5102504070007418540c0300e40004041c01085210101018000700c10b568081c038061400800400d000c965000108000f50f000c1050030f2450000d69109036480150518a6190300c00040c901800081040b42008a0120070006c1c40e107490018083c0d209407034981c2c0c1d89170950162034054034940240898040c2c2d07002c0f00c11900e81164505600 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 845529847 1250 845528597 845528603
    0x29030106050d09081b0c0405010b0a08150d0f060c110304150509060408010e0f0a02101d0406060e13141303090819030f050903060105060f0d0e0604031106090a 70
    0x907680c440380b0100101419400300c01501280c404610380c81d4003042100c034240203620400c103841d035200c0644200000c5034000e0040740746844043c003103880c2c0709000e02c92441e04418101181c0a1140d103050005400104040046920b103001020400410049002d441d8005815003040e01441c582489626a6800b4512440f01c0c0100074a103a010900e01850440f120b10700701030b284c5a5120b0300c0c1c6601c0b5011f003140c55081031031482609000440100049406441d00794000d20030907041640300b000316191000b403200c0e03aa501c2040b0001c011507684171302c91040181000e4454410094450341041110b015211103509079906000320005040c0c2c034041c0c801d81c051031074a0306021956050078101c528400381e400103801ca10560b45110482d596081c40b01500c51b21a954001c0b00e03171414403040f5100e0050428198241d4007810050020b8581784001e1719500910300300d8103042c10b451000030001e842c80c000c4280e400c1e4001e0400d0205143e400700d660306a18403080010310f9542058001642c0c0c2d000d12500107 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 845531097 1250 845529847 845529857
    0x8070f050d0f06030b091b130b03010507020a03031803170a0209150c060a11070f2f10090f0603050705070210021b0307050307060c0516080729030106 66
    0x928194040c0c0c00340c0c0d5250400303801c1044412156074100c0001c04590009030b0742c0c824510009071089200160030304131308044481089802d00244207001d4603502020060b50b8a946402001f252a2000d01c10980318540d254001c0c10f50300001d080182c111060341c00c1d00c007008062203099002190300060a50064108000c0c00701007541c400a94030700902503105041e85c003000c403080384084242580040c0c25948103880980b401525401104000c452050070fa1344d855802c1803001001180c0d418071600f05a6001d51069082e1401c00382d40c080c00420303500c908421040c07005000c1020b83c240344041c0810750f601400d0a00c4500c1c01d050f45400c000d410f91081c0b00402d5103c40c0003c500368171900030b8550700c0b0740c00750001d00060303482c0401070744500200304081c0140c1d0b03241c00304d10558600001e1020072070320094003400d00c850074105c0441d10b21141600580342413040c400441d91031400122484020912100640300041c200304c19942900400e01144039080d040c4042d02c4d6032182d80c131003102d04540580c181 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 845532347 1250 845531097 845531117
    0xf0919151815020d08010e060d020d05011508071805040c0314071503480905060304060207020913050c0d1506180c0203030c120c070b041a070c030807 66
    0x40d0a044050540050b00c140840310384004074550000380c0240c1c4c0611365116010185c0c1c03130344802a1100c20440742c555001c0303400000b540c00341c00d003480c03000c074880d0290002080401030a403411070b89030350640c881d50300f40d0301039941007241c015490608003200c0c040b008140480c4c01d150302c45c0244541c84d4040075081c061030004e0388402e010200403240c000c11001102203c00d8298500143c028001c0702000c10304d0641d4580b9480608441d06c08504a040b285410600034108a1201c481e0b0140400441000d211a0301008916903503070001640c412485458003607916500c62050202d001e601070301d0880036810009015000500104401220b2903041c0c508070221080c3d81000d0070002401494204200c2c9040c8000c100c01c8000020a03464035542c00040c420380f45603110899581c4030841d045030400d0014031488040d0380d512410583c00510380c001003420045a51a140fa092200b40d60803a010182c92080040d902050341415a1007016401e24087d80015902d0181100e04014440420001039640d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 845533597 1250 845532347 845532377
    0x304151b0b0c120c030a11130b030903130905010305190c031e020603040b0103050d14031302030f0303010f321003060924080d0c060209150f091915 65
    0x400d450120011140301c0310b40b8109506113a40030f07481542e8000c0c3d0203041149041844001004681c0ea0590035440d0760f25080c9080c2c40f182080c2c101070021419408200002e00f002010001503001810406000040551452425a18221382441c02c03841400d00c41040c58049144800f8000490f60840466105400413200c00c9109a02d28400254407107008400e00043c040f20110b00c0381a43d20580403514030340c4005a094906008040c540c3e100e8480403c00a0b412814801c44214000d10250440c0c084011024450382517400982110020a00458040009000024010404c0940120f02900e205400070619203030843e070404581c003581e0112415a82903100380e0000c0c000744042c00b01042a0119040d0b9050f0a10319494400e04a04086d14041480302d8045091180580c0a44038462007040503a0380c58082d400601040c0d60110705100e070070010461003801045203844c450341c504d6440300502c00300090500c4040909d801580520b03009c2c000740001c0350880c1000344690030040c502e081c1c482 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 845534847 1250 845533597 845533621
    0x203030418050402010305150f040b1f0503070e040b1008100e1614030106020a140f010515131e09050c0a0608070f0c0f020d05100c020304151b0b 64
    0x5031150340300c41108200724854a8040c0d00c01070140d4406d903001c0c05070352581100134800415140c03440ea171203030003034610503c540390a5218403411000a00015103800310800b2000340d4410b020000004501d0010800800d9035100341800f80e500c2c2d0440f810458022228041405141e101c0c80c1c90082c021381801088070082c81020300001001e090000f500c00e03240010a810040c000704040f0404620a0070351050815100380590341655900d500520780c1c00896121a41d580301c44450100390b90141c00c500032010142070080f1071058000304920340340703107108009002501d80030620314050140780564241c15107030441c0d10f00740809103403a000300344182142446800c01074071000d4150700002c3d8003000140d40f40c0040083d4480c02d06c60311040940c5680364001d88804140308001400c00c042020558010700d801403204030414011070441d514203035400c60110071034414403030020240e0720100301040f4291080f6842d044201c001d14040025400c00d50104840080801c3c0003800100c2e91000a12010000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 845536097 1250 845534847 845534849
    0x8041502070c0306020a0318110d030c05160e090d0206070e121f0501150c0f060204090c09080105090d091a0702030a0317010b032701060b131509180902030304 70
    0x40109040b81682c1d03454000004d6000389220404682400b0b000b11421003d04a00c080c203d40005800c5a4031a2034810800070800b102011000d1118882c03900001c03c03010000c060442c0c020040b252080350a141054070700a0000780101b410380c0c0700445003001c45a001c5100da401900074140068400300e204001500000d020500d120308d44079180c0b0700ba000c01c1c0c180b40276440e1814249401c208503600c65100380c050b120030000050208075418a524006100b105c80b05a400b802413500608144e102d0040400ba20b0581081c140010050001840034880a00c981c5401c900004002c040c2c40e82d08c00c4000c0c2201016120b000111100c440c1050009149103044580d402d5009007511444102440c014000704040142c008200705180f0010542e941c005c400c40b40221400d00b14011070303038203c104c00841009907c41c03c4086548501e00001c0160b0000c01070005c5d90300b81d050802c000d509140041480091350920a820401c00400030400c50005c44554041c0311107544011401500314000f2034030f035101d2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 845537347 1250 845536097 845536103
    0x106051219111203091c020d2406030303050f15031f020705030408072408040602030907080601060e04140c120a0e1b1c0804050d020301090515060319030804150207 72
    0x2918440c0f10100c001c00101407004048400346052400b480303481c034100006040013904080240000d00c003055403151800343e0308940c84400000e45031403110800c141c0c2d007603a0041f0080703915a0f0501482c000f480641542c0030505105124050640d0f4000a94584440481c5403541d502c0c03240a2910010540440f0009600a012070b9540c5640d0403946654000038400c002001c0110012441310a1100804d038a0011155458206c00d0321541c840d50025800981000c259105240340000c071010300f0702403217000348025156020003d6404d42032200f6100090f106c00700b0242c40400b0040312500403170640b0380f917801c0e510a0781419500e03002d4100c018641c0d481c098456200300344880420302101c102460142409552840a0240c484940c40034940c0c1240000c1c13101c0402e200c14009400c1076003c60054600040010501070110f0f1105800c140410400384062030040040000ea030800b001011108520101780c1d0001d000140c070b00a007265801b4100031302d65149003000303c0240d50150103407500aa0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 845538597 1250 845537347 845537359
    0x50c18030a08041202010f02070612020306040b0d062003040b0106201605120f0a060c02011104090506090906010305060601050a0c1b080c0a060c0f02010c17040602010605121911 78
    0x180710302980311880d40c5050700328002103269440c08001440410210200d2b1195220741081d003030310241d0703c800f940004100301e40055852040c45040e035240c031400510b6030701038600064401c01c2c010000c42d400000413000064a2810414000010a07582e856811031300c8038508a4106110320000400c03010f40c1c2c07400d490441c401d0040c0c204043d010082d5890840d042200c1042054803160119511600940544042600319684000214203903400c45038841400e0b1000080003144030050400580103030b0080e45015546104101c40d50501e242125005032702e03080100442d40c515543d071903542034000c0c900ca0400c80080383d440200390060354400030075540601459075070580c0c501503c00320a0140324041c50362180040090141c1882c14404003680e0050380c903103114401030340300e06403001c030120000c07070420680035001c60201e8114107010520030064001c081d03466203845c90007802d4808940010380720f050716844103002c0003000506140020500b41d0f40c19120051820405000001d2040c00c0340c00407 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 845539847 1250 845538597 845538599
    0xa09050a0b0919080a0f021306121704030203070b070c0e1801051b0a03021b06040c09050f070c0213061a040e13030f21090308041104050c18030a0804 66
    0x40c9581c805019105070980d605051020034140702444100d05120b00846070304500e5052001ca9140440020102e001414010149580002c943c0417151264044200745000141c0141000001c19100c8450810900b841d405d1508540009458107424032810200b0b80300080c03000304000e815191103004203c0245500c40c0b914010188081d00c01b4101d06851b0154070b0b00000400c0d0032030040a503a4203a1013030501c941071040c00032040c1c00039403094004024903211200059070010040000d94840c07489541510802441c120001d019a0300103403110044c01c125104100c000c0b0b48c403004026020360110b41c2013030f6039240c40780c82d20300801d2190080026446450f101400d10803100c4000c108407400c421455003282d0701d55014403448200410003d0011740a64202012179100f4260a098440642d00c582c4905500040200c1140c1443d0004c0b03000c01c0c400c000300028003a1684090041c014261000c0c4203515210b060190b19201c0c0d100c1141c0140c00c4500400c0301d90704e0030041141101e0b84000d402da51a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 845541097 1250 845539847 845539859
    0x2001060b0d050601111204050d15052e050d06021c0524040b06090603180a1217060a060810031407090b0d080909060616061506020c010905060a09050a 66
    0x9400300f100d045001c14558143c16901c40c0c800110501142c0d90090f0f0b80b030800782450100034290840f01c01c290f1b58240b4034140c0a11405251040900a2400d8000e051414400945a41604020305a03100c60040070310300c10801e44e200e080e007807920706912402c016030340da07501c1210303503008920602503217034480c40d120421403030120303403e610122800c041d8094038803030b00101e0803c001e40c0c0d03916500700c0c0c10200c18400660b00d810014007664208103e00c00300068a801001030318942480e440003030741e0324000b11010288882e00301070360400d1200c06054141c45440c1030000f090103044107108a108200e0640d000541080309000b8034405158400d8104840d10070045a0300c1e544c0040c1d0003454140c51a00210303800524010009420307055000c1001400c1c01c8000c01000148000203040507009002004055410342000d06980c01b400d01c94040003071108103504003400569601d82100040d540b010001d00c3c00303a0f0700f10f0881011580111a44e030b659403020241128420303a241e20064200c22140008582 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 845542347 1250 845541097 845541101
    0x4030b07020c03070b090f121f09030801141c031b031d0105070c090e01140a0c0807091206050603030405060f0a083418090e0601090c2001060b0d 64
    0x15208030200c541c0b00e40ca804141c00b4620a4481550340f184080480c09181d0034000c1c404002c1c23191075003c0e2414a02c400c88100c1c421802511003d500f02d0b90703180344004041c4c018800c540034001c986031210fa01040e52022501c030b000c0100c1c0500524403400d0340c0f102050300c120b0b4002014090515082e411180b00e184c0907041145d0001d050300a61655545100d00354410420740d00d060b41c200320341500d054503144c04800240100001500a5500c2d0741c1e8503441c4020000426008001410001480d1b07107280100a045950140100007084110481004488084201c035130f100d03604100001341c44e886850000c0d00c1c502c151b502643e00181c01040c207034031002d41040503000a130043d40f04c4000c9030341ca81c003440200c1a09481c032001c0c80d034000d0980c5132030708020035041c0200e51290b040100c80066596034441881c41ea0b640120310f40754441507101020103060001c14010302c0141814030401403120005842e02c0030f00084800c0e1200b15900051002c0400d400c010014101001c80e203a6801c40e030249030340 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 845543597 1250 845542347 845542363
    0x90c0509030601140109030f15020304230c031b0414040605070212091012092001020c040b03030d050403210f0506031f0c120203090102030114101b0804030b0702 71
    0x221900500c0b00000b0f9440101e50980100003050f901c5d405500d00b5561021505404001d05841403002c0100c680e9070690507200450007580241728040004042500ca050207160034007019005c3e4001c00074421954900242c58071800011560b0000304010030130208008000040c1800502400e010a001c00d02059500003030140f00c05e5070980c1c0c44a003900c49007541a21a040c444e981001e14403005440581c0300d1451400812a850000b05807055140c6a29a80202c4d9503500b00c01000d1507040780000d581c04224071281c2c500c0586091245404000c0005d4490207041c1c004041d141d100c90004081500c190305d00d009440311a41c02d24038008104110030006c10345e0001442d0303500c0c90031000c11003d26000030071118400048610005138003010354080060004000c10000f0b001c0311400080d00c01c1c01c180051482444850b0005031a50f1500f2200d020002c80340485034001c0c2c1d000100403240781e500007050507004000101401d008119807802e500a840349520103403003491100c080c0010300361302141c020 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 845544847 1250 845543597 845543599
    0x30303160801081204050d080d0e0106082509052706010e0c03040506150402040b07050c0a0501050405090114033c070f12060e06070507061b0f1107090c0509 69
    0xc1c140ea00c914030541d0769401e102c006002000d0502007005645030420744a213800780310380d200f582410031051102003611409003220003165181d0314244083c810422001c05030120114024001041c054500c0048641c40c1c029007102e1629900084c80b6074003000d80c840d0106100345450703c0c804070090042070b12a102070054421954022002c250203070710102c1034900542c0c005009d001603854600c036014441c42c3e4800140d410540a000000e030782007054000c3c16425010764050802c810b00c240c100603500106410040c184074046c03006100c640c54001ca12415510b070030302c0384500c403601d81000030326040020304005101c03005100460341c4488014010140301c06070300800c0c0f101c50241c00c0d01d10307103510302030041c4058804010340400c41d4034542e10fa0103105a0244100055480450b4840c42c104801140c0380d0011400002d9010100f241070700c035040d194003802c5050042c40703106003002000e4203e140149000c00c48444c0e50364a030824140010ba00400e101c2d07070100820301d4502c0d4041c0203034000071886 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 845546097 1250 845544847 845544857
    0xa0605070c0b0a080a0906060b19090807080a141018050c041b260115320d1407080a11070f02090705040f12021f020a0b0603010b03030316 61
    0x14070319400c907083da82c580941c0e03180c0301d0141c1d03101d20b401c000034030350520203030360b000c0c3c0782c07400015044c0e642001803180c030b21650320f40d4007048498200500b03452a0b9902c80c4100e80d01090b0100304981001c60190000742d40040e01210580341200e045141070300c48407280c0056841c1c01c100c0c4800c1140c00c0f02c446517440c4102d0a58500c00503030001c0008845403a951030303400d6426020040d22091142c104012258081d01804029651200c40c0c1043d40c6000d810200704043d403400e401e164640c00c01c2844400d00016025002c1e0800c211710b00e210901894a10b0068558012986a400b058990492110342580c000809614606840d0040c68441c0c2503910b0001545890b45061801103c403040f02c542617088400c03810080d54a0b03080c0401c81d100104180f0030030100b4400401c59019250600e001823240f01a14910005c003401046510201280d8007203034a155540854803094000c10700500294000240540b01e5541c031000c00e025100c0710f00303641d50601000042100d40c15084d01c1041d0002d99950f96 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 845547347 1250 845546097 845546099
    0x304260a0921030c060c03060308070803010603050f0112240912030c2d0512040506070e090103030f0f030b03030f0714010c120f06170a021306060516020d020a0605070c 74
    0x202e28007039001d1840940025544004907001c558940c01c00400203640c1e16000030b00d1a07407515003c102d500300900031108000000300412045906000b00d40e041074184d1200035442d407401d02400d42800407003500416540701d40c04032030311078881c07d0b100c1c90400080d543c5c01e000c40e51703040c9000c0c26144a02c1e420700002c01d00e004580203c0030302c01d03d558a4806641ca5100546a240d1510140381a044004400800c802004942111008204591b000713504c2140141a0707400d1030704029104941c008482c4d4001d0b481030f00100701207035020303089007036048050800c12003404846108070054140f802d40d543e050312000614841c0320542c00d004110090040c1c001c0d65600c6041c8101d14240c54008034085c0005460034214142c807112a40143c48205809a001803100d944401c013015014000c2c00e00b49550f000f220511003581041c0d016551859a41c0100304182d50802001810300c0c014a1020243c04001c0040c2c031701151036008201a142da0001d0510440303658644004091b940b101204a41a004a6030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 845548597 1250 845547347 845547389
    0x312070302010c0f05040602101802041509060b070308280e0304170109050c100c0210080105030c0d020109140301020409050c030615040b03220b04050606030c0f060304260a09 77
    0xc11b480030b844603580a001201c00c1c041c00100544555126540c2402200c180d000041c2e40e284038035000005a500c40d00c403510720b003400800454500c0d174003901010008002030740009600070aa0fa5000840100741e2840c0b44186001d5002c031150601d403010200e01d048030080c44848004040c1007107980308003841405107100f695a50030307520120302c02000303540807441e4000185001d045071107410b100d40c50f0001c03650096800003048441146094001b29800400504c01810207000ba1701030440c0a4610b82003500b5142d0008003803084a00c540348041071074915052a59a0a4040350000c0c206100d0501150802449032805a0b005440c11b41c8034405120b51003000c0340c82001600d0440314140c06180c1180c1d920707581c40c802d02609101e01d002e15100c40410400090b000f0305001d000351b002c0c1c801001e0350315002c01030500c0c28000000d01c2c0e210300f0040700c8840d07039580c4e1142140c0d4032961201803074035003105180c105102080601c07001c03000d5040c003095041505520070018821201c00400e0446c1d41c101c541 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 845549847 1250 845548597 845548607
    0x7051515060c0a1403220e011d221b0518040c05010e061b07090509012a1715010201050a1404060905121b0f0c100e0312070302010c0f 59
    0xe00c14110390002c00e8a400400c0f007040c5284000014981600d207030120704c0650314500c541c0e084040c0d0507006c0c5c60005000d61a1050710f024003400f50f10004004080a402e041c5251600003000e80024617450002c0783c00460418031480c41442e4080d030301c00c07410340c410b5810003503003501802811302514100343e4120708603440c0c80c1c00760b01032a04151101d0544e41010011035030f00c1745001d03132076400040800442d6070500c0140713001c403615444040900881814181200203032078000e840c441c01030307041c80c8940032001c003040185171601841d901e4000303c51a40301001d464045a018414051142200400809010410800c0e05941003640200804c1da0fa00c1900f02c11142446208550003414400080002d1032503805070b4401402503040383c0215244000b07295095010040003100c8e08620820707207681a1003080714009500c01c0002030040000c415020030b0f102300507012030b8000c000f41c1a8a0b10740b10b80f4107010030303c0300d0381d02c000030035581d01440e081c064040c00144c0c54000005107400300400655104d4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 845551097 1250 845549847 845549857
    0xd021b0606181018050f0106140d1e090812091c1101061502010c110105011208070609060207081b01050603430e010e060105030f040303020705151506 66
    0x340390b40c005680071911184200c1c0002c15000c21102c45500c007040304150220941010a90300d507001c1200d107410100c0e604220810307804070f4180300c0c40110703a59035070003040d0540301d54000030100050260081e004001c09021500e07191000185002c40038400c5c00312040041c09541598000b980890b20b4182056983d003400c1c03403150182c075201100051500d0320031010250f4480300c040000c00c2c46601c504059544100e00140e05000d0b039900c00300c1014558104100725041110180200a652305d0156024070390b98185100816174040055510708220043c1c0c04100c502d42c00c00c4e81191140f8540c03030300c0c0909501046801802c82d0103c400852000c00501403140302d003801030003070600803465109901032440c03452100e80c01d491300d2100300024140412060910000b041c2100116540b400d02c50701589603040c1c0010782429690720400c040da98222045980210301ea40c00d000c00c40e0740d03a0030103c0003402118802895030161390001c0c0350ad0310419843c1806000300903030301901c1e88890b1041050700e10074 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 845552347 1250 845551097 845551099
    0x1030503040504020a050c06070216121115130801020307030506030a030f080c07061401051008070503152b11060a0815041508010c020601050d030203090405060112020d021b0606 78
    0x300014402d60a2580191100380054284142495110b6100303505001003161480010381c04140c0c800100d14418040c80014404440f85960900b042c0d101d039022041083c3c416801100444070992404000c0e104845500740d281c102012844e88441c1d4081c041e40c001d81d0300d440080e042c100840da0302c9c503021941d100041c0e41600c6002e8441100402038502c4000141152991a01404400e0110782c160140d826424054101042a503042104001441c0c5d10281081d04002581080150880e001412030307400561807884000c4d4034500c10001429090710700b4100058104d02451506450210031622001900c2140140c1d10580c05409000142c0521010a00050f10380c10201d68400810000451030180c0a8001b0440034100c102e4540c00110381e40c00000d0303581d56a40b51346016981070250a000d080122076240900c519528020365900400b558540301c4d81d034940c0800c90302ea00a603124040c0c007c0c014000c5d51240f0a42d5024002501714000707140682e9201c010103604814049103c602c15a8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 845553597 1250 845552347 845552353
    0x1a010f050a0627051c060e010c0207031b030c09020c2127040905060a0b01081006030c020705030d020a050c0f0d1509080d292d060a0f080c03010305 65
    0x1807103405000f034070007842140c2002980c1d41c10003040e15260750202e0007864a40950300c1c402e070301c002c1c501407084401084003d00141d01d0050604492340c1d002c544402240c0e00300103200da956965a664905150706580000c20f100d40658001030320116680283c00f8840510082d244030b021403082c010202c10f1500c3c0a82c0c4204070401100303006107650080ca0324240712190002846442241c0481c00710396440f5820343d100da224400708103112040303000e517513480307442840c06101ca400d00ca102c110400da0280203940c10f15844805031800b5a10810000c0003d01d4000c1c21641c2281c1c1383d2102944031400014143c8260140070584c60050900300700e1440c881402400018515080e5102d940b00d07485800090b40c803c41d1200c1e28400800c5602000c1c2007a0b48940c0310004c3d1240b5035150701c0346c1000100448211205c0c80c0400d41c4590b944401c46860049140c0b410030030100c1801c200341c0c01160007900c0c40c552003100403402d0b8460726800400000382d01c0c00358a5441540c2c481480d4202140001d00c0000d040b68 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 845554847 1250 845553597 845553617
    0x5030307050d090b040605240d02040504030e03062a0309030a0e060d0f0b1e030a02130b030327010206010807120c0b0c100f0905060f04030c1a010f050a06 68
    0x2407180008205600342c0600004520280d640c90080022060394241d4503d621007052006642070200c0c21880e01011004000184402c080410100303c1c0701c5201a104507a01c400240c14180a03802030301c80840010f080e24214500b5035006000410408007502c0f818030030740c0c104a2300590b803004413030040406000940c20441c142c0421903e540300800b140750012002c0c0301c408401d14441c05030040880e01d0440114950f401a030500c140403052900311205004d900d00ca10f2031030b80f408030f0001a42c60301903820041c0b4080c2010501d000c0c0012000300d81d01440005800801d5250f4011462001151015201c64061060004a0780c495003801341c11b105030000a4100a803110008000c00510320481c60105c0040c2d9580f44111190001384041c0140e0b000801100782c1080148242140c00012903020003c110603500c41664a4030002c15144103264100d001c502498040d1602c00c81c41036004410380880060303989101400030013032080080b4071840034070200b09880c3c11504031003910b16a5460700e90034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 845556097 1250 845554847 845554861
    0xc03070b28080603120421240e070602070e0a0c0e060705010e06160e0609040b0d080703020c011b03031d0708010605012006010b0c0102090a1d060a03050303 69
    0x90744041c1590804031150260090498050560300c1039184694552208500c0c24500f41805c0411505e811004424108403e0041298030b2400304030900b001c10741250f04000390f240c8941441c480900c90507103100582040d14036003025030004c4543c11654000e5031581c0ba40c1c0c01007682e032000c072800390318142c1c1d000000041c0034903055446102111030f145412042341c0c614078046221940a50001e40b501d9441303104400401c41c04100f15504080000704140d0401d9080e500140350817001e515140c0b141100042c1c0780c5013903540ea00420794014008040f404000d51503d4074880030f5000c40d60890141c0035180c00d40ca0590300800020005506030705000c41d551249a40071402000001030a0b80a45050740d80c0c240d00360740410039440500510400007940600701700003d40815450b00484000019050b40c407107400a01103103250440b054180f81070b40b11282004a14068004c50740c0581c0c014240402c0041e07900f061804200c0b101921000f44001c1e034884006101003140503000c064510342c4200041109 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 845557347 1250 845556097 845556119
    0x151c060e100302040e0106141306031b081c120b0a03060204091b0306060c02060a0201150e011a0405060d0507091802030105011d0a0302090601141305040b0a06080c07020a0b03040b0103050c030c0307 87
    0x2880240340c9c001400d0361250b6403580380c0c0850b42c08564900c002c1083c00e01285404000102c913180a85c0c061110300200d09c2002402c1a05400b003580106407201c2142046840d0f12200030069540a401551606e403104608802055804036107080304100c800320b4464a03011344a00390036100307540d0310740020710455001c0c400c181d0301c0410344d10300710341da42c2c2c4421002003095046400940300030009021194980f091400083d90864801c0494000c00c01007041a55a03205c21a298050107410110711680c0d026000d98003c10168003004a603540c40c02c145480040540c015410b0752800d0702d07803c60400c00c030041850071030001105190082c1c64121b051000d490040100c6030301100524001810319608a0341031803503004041110018042c26105019900c0c2c5801141000741058070041900c0b0326003000203110305006012070110010014401d8195214003441201800c0d484410b155681800d107001e00e00840248001d80350750289419004081c030300429940202c0c100280282200f60501c0c0948071 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 845558597 1250 845557347 845557369
    0xc080405150d02030403021b0a0806061908030f0a0801090b060313060e01020c010b0a0e040213051012050c150306060702130b030114070e151c060e100302040e010614 73
    0x20300740700140500c1d0091042400214850352103907015101c070b0483d010400c0c1c10003401c020304034071a0250722028071064100280c901c0c0e00c51000c407114003190303400c400c030000400010b42280003235002c0082d106a56a044500924120074613545c0d4042c03903aa01c000e100700326400c2c00447d40d4004001c1011640c1d2680c4000c0c0e82c12524051440091203150410400303003207074884003014060303035102c1d81300400501d03000d04e2110003000e20741440601740c90194002002d41d2040310b015840356664101182011081011081c041d100e2803400396031000e1141002a96001840400e034451030040c403400329206140010b44c5d02a54000c0c0c8100e0030518207508100c0a00100210300d40b030640e1700c00600d400b645d002d002c0d4040c801c01180340c51540b030500c0c00d4028030704045000800c5c010110a141c654011403000e04a414440141401da1042c0001405000181200354030042c4203c2c440d4044c082208400003141044a208171800c00c901da24105602c0d003a01c81c144280303a60000c100081090605140342654 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 845559847 1250 845558597 845558629
    0x190306120602130e01171b011418061b0c0f03030d0903020120090102060c03060102060604051312020303090f0703110d03120608060a050601021615091d160c080405 72
    0x11203d0b03901c0702101031042800f6804136800308400303501c1146030310040c40709611400300302e00c0e248401c00c08080080c1884001c91010080710b070340010001c000e00c80002e0068015a00104182e0342c403600c13110f0f2040400f481d031803000c0c000e0003201d000249902c6c02c42c14603000900c000e000b0703504260500b540d5200510580c0b0041c0c095540b1403010050f80010b01d28203a00007416108017644501103000020310341103004001158410081080c01000e03030b000100c0c1a48150100c8012520742c1e25050f1901030344140070401412881d00010780060507401101441c4140314141c110707640141c600700c505603609480e01c000b400403d07e045107036200c0c4c10003501800401c4e010b81051100c0900c0044441e0031100c2c079600102183d0066001d201d24078165002e004d400503024801841c2e246081071200844840c1c1e0305c03e4003ca5102c0c8a400300c1c005010340c0c00040200310180103c240700d003003480340d402030300c6084602d0035140075500c2da240e0070380e40120f440c64502d075080981c240c102403c040130f100e41c00f90030038416 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 845561097 1250 845559847 845559877
    0x304060b0904260c06043008010b0a1106070809190f060e03090a1203030f0501210201020c040f09110909060f0403141801030501080714040908040317190306120602 72
    0x10601d03c000304605c90165120b0218803501410b5864080b641d03400306404444e040c504c5400109045601070407460650ba06080c1d90703a41d420324140150342c0c1b0708003902d90707c140b80105420401e4052300f1005482c421b04900041d5050b03a242c20000240d80c41d070050f401400c402200b40c2c0d06003c1900d135400004084074a0080300c4c0fa0502490004041e0205a4468603081501001e00b07810558540514180b11001c00d005101a5050410781e0490004215960340c0d00741c20054400156842006900314035480170703108010700035907c12000e024180e0030384141d41c0f240ca0300c2a4041c2600b0400021489999514050041e684401a44128490f4003070000d07410810b0340c040887c0443e048000600003040c44810f5a02c420790104005026034405030320914140d080400100000d1801f074140d140506812140003c00c0c034580d1074102d141c0d0140b500043e08401e00b001d514404280d02e1802803104000041d5200340906140300e0440946010703018016030800d171140c03681c00040700740d000703010703c003c440100d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 845562347 1250 845561097 845561107
    0x2060c0a0e030a0b0c04090b06070c12171305210c210d030204060e0d050709020a0315090902031605030d0c06020d0c0201060611070812090a09060b0304060b090426 72
    0x3113100e0050169010b0600717080028040103c3e190f50310501ca154007040e61001c1c105a801d032503503001c001142c440d0809102c4054540e204120307010812820000c2c4001a070798840c001c18180c0c2d0901c0401d4000c49008040307650032307552040e24480120890101c24401801c8035404402072107107084110035040341c0400c1d444c81d10b00e100b090a010b090884032003554010b0700c1da844c0c003070010075617007444000500418425844101140c3d0100e5441c050f10448240541d0b00c00c0c0d100c070700f00e0040422a100070340c03494103003802090a804980140c24041c0c003c808455001d108040e298100403044e20030654160f100c40c204002d0940a11102840c0c18020340c4018200b42c03101ca10003003980c2010341c2040043c2d55800d020301001e03411009042408548500505a9506111032141e840c0ba02c05e55958440c00c02241b2044036944802c45000505031150342402202c0d907a60000074182c0040e9401c4610f282440c0310030316142440603e0b07511075908201f10f001380d016500401d5000c07903104140145566001c000b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 845563597 1250 845562347 845562353
    0xe0109150806070f1e12020a0e0307030501060302270406050c070602030708090f0102270f0a080304091802010e130209030a0302211303150605040f050402090702060c0a0e030a 77
    0x2c9070303c5075503075854408010340c803000010410b15030769407407400080082010300c5c40301380c0c404004503442c0742d00741c001170341c03516010025600280c5980d440b0341e00d445010700200800c02c0c19004030088034030940e41e21980c201d2020130700f002c00030040841c00c003603500240094085841900701503040b010140c0594030b000d1040e00c904099070710866040300803400c03d4007844001e040801280e80d082260400850410180c40301c4060000460002c10003400300c9601c02800da03a690801d00041032500074914001c880e42c2d106503545980040c824034100524180da0b01210310315142501d01d51640c140e44901408032071808100303000841aa04903483e40e42442044030589003005079442c140d000e80c00400c0d4140101f169546001e80c40420000c1e6907206000b00400d01035500c02100903280d2207440d5a542c01d1250040300020105540603d92042c10114081c04958084d4402c0e400f8074002da8040b10241ea0b00703101030340d5030701d0240d95001c4e01520800c40b604400303100e00305044961800034259103110207551 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 845564847 1250 845563597 845563603
    0x10317090a051206073510080105090f010c02070f050105070614070518040c02060403200319030b040b09060f040e030c1c030b130903050d110c0d0503010e01091508 72
    0x101c040c1055201340c00b4029040d0304403e4500c818039040e00781e6580c1441400400c11905600388100e14205c410740c010949900a41c41240c003c1c140c007070001c202500d00b4510460369448040d0302c40e42d0551074002914035561002c20500700ba2100196101880c525100045a160b440700760195140d582e00e24680144104020801303010721803903592503448245201442c42041d6064144a00c2107103464104028260045000b503403146d01401d003240b070b0242102c80c102012401200191b5140400100c0440c941034240400b0450307002070b502008010090010b0104541281104651190950000600c149840b804116403500b014002241090003121000e00d03503008120150302c590051040d6a0b0a801c29888a9101416902c0d003030060790310043c045500f2000b09801c694000742ca420201041c5800b440c22070300d80724001c0200300b1154400c0d2010b681142c008407141400381c050080b82580292042c02960705a481c07007070300a0f4159190030441c01c0140716a0344011441907802100040081c000c2c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 845566097 1250 845564847 845564869
    0x20a0203010903210213090c110a060c0e03030c0c0919050a063209060d0f050d02100c09050609010309081c0c0311073002150f010317090a05 62
    0xb91135484000b10003c1d101302c9191654030028046501c180f001195003507580204204442c00c1c0b540c001400d00001c2000c55110f03a460840321010320801d1800d00401000707510203000070302c01c1d581c0d4801503985417003055241c0c49050300880859100a044001e54074201c01d02035004000c4500040c42d00030403d64040c00c2c1c51084640340384080d0360380000c210b10b100c1001c02e1450110a040e1605e900b504951103c0c07280030960803c18002c824020000b100c645503500326600498100703507900044070052401d50b94861065410200501600f42000c0c0c501c0024020a1404a001d0321401c81060601c410300c81190040a0765070304140d240d40c0d0b210003280449009084d2010880f89074101c1d504044403950a64062440780c00426260200c8090140c0115007a80d602c190302400c00f10002000c0c00002010303103054800d4580361003815003003818058001414500244080c14a021150759584441d01619800d106c0070f842030b02942c19000d0020000030081c4003549000700301a000c0e548443c040f8581d0801 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 845567347 1250 845566097 845566103
    0x200304120909090b1b21070302130b0c010c050306030d0c0503040e100321050f0d06051c032309121c0905090f1b0f070f030e0109121a0601020a02030109 67
    0x5403003413084024a9481c02c401c1d0b80c05a00445241c80001840d21844900c544610188106c502000c12841031080d01200c041d03543c00c00701d403102c0755222140013406901c40c1080350019840c006211f0713201401034040e03910035000140601500403640b04c00341c60107001404121010f020800011410344507124016000b000707407444600c0d040f411441c0000542803100141c0101015400d9244003095101d801c44524466095000703440c0c0201044400103060b40c1c2c0c119651089520103c28440c4040050f1303141401e000341d44d80c2120701c3e85100c1c040ca80d88030f039200303503081000d0403c001c2c0a40d003403200f08010b501a40320102e4180281d228000128589400c040c3d00014000b1a020006407508a1400b81c00101c0082d1010013810070b25420b04044401d03180c03c010100c80441e0714041e41c8016015622036982100d458100c0c3d803a903140060220715000340f51400b242da140e0022510303480d081c0c41490000e521400744000701c1550048500c10400c01441d4504504c1045620401a2005c0c0150803036944 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 845568597 1250 845567347 845567363
    0x1508060919111b070603050108030f18030f10060b120109021303050106060203090411120a0e010e15180303090c0402070611191b020d11010c02090c0c0120030412090909 74
    0x2071469180d41413001aa0000040508040050190358804001c0b910300d12401d90003240d03207075009009034400c0034006030700036403502a9440b07800590b000840c0030400c2440e034200400c001615101d01c0d05442c010414044c031404a441c00520080e907040e0300520200340712064138410150b482c0e0f100340c00c1d125130b608028010703003001c100d49450b402c1078041c0040440c0c80b076152500307080400700d07000c11801c030081409143c2c540b80c1992403003401e4294042d00504020701c1c2940c42c094815103044100074020749461048080f442004054a6404410340e1b01a10803940a01080341c1ca40e020000650024030b001d944803a900d43c51080c0349040d050041110b4100360003541c0c0d60000300903015000042c06002141d800c40ca0780c04a5005907034000d02400b0013a03000c45040c070f4241107000101c980d00719003a4001d410511440c00e1115070500140078212058112000340b0143c440c9540f1407502400c447e40e4401107010500118001070fa0240e91084c294080745422210030b9910070780c40c0d050b500e1000b42522001c2e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 845569847 1250 845568597 845568637
    0xa0305030d0b09010e0f06060c07140a06020a030503181005190c140a11010609060f08062d07210603051b060f0a0e040606030501150806091911 63
    0x30024040c005580e0740840d500d06076036141140200381a02d00a0464038407030406c0001804564440b025501002a20401c60342d003a03480741200c0510342e19030300d074680c855a061100001c1c51440010b40301e0f400d503031542e00c25007107844011041c8452140311854651600807161000340c000220304c12603207d0105a1090b000360300d10754491000b241e65281d4032800300110360070000b828044600417252000c00616002c1039400c0580600390040440e40c00c080905810311a00190030017401e039000040da10700c00162022500c1d01826040216005614203843d4101051110500496941550352181c83c508100300d800c062420001d031124105c400120400386d8603c0c05005000003000382d619020380f015080d016481d24600011000d009002902040310300020322a03180b1840340702c00c0b0b4803168010f041400b5040e00c0d5803000c0c001e03003024040c00c4840944c0500d4042c09030300c6040100e0013420301030820b0030b844e111b00070321200c81d00103050b4480003661190301c8626420000c800401d04103080203000c002d00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 845571097 1250 845569847 845569867
    0xc0c031106040302191a09030a0f1107060c05010e010603080c010b030c06030a0203040c0b16150b0d081608041203030c1e031e02070c0501090512070302060f090a030503 74
    0x210010520021107920000400000a4000440c2041010700951540a100040c602100d1203503171380180c24080c0280c081441f025290020161108605944848280c03426441c1c00b110031f50542ca45000c0307a548030000400560b1700803d190315449020f10000b04a005000c183d141c02c5d24504c1d8421034440c8000903204070882001e210f400d103502d008070060044000d146001072860f0001070000003000e1b0740000443e0801c03103074122500040004555a0745c543c0b14034141c03841e2851800d481610418450310388000007003654070030005080001080001692216240c00e00b072508074030076000700d413a807542485000c9486540500020800c20000920b0f64a2901e0010156120a0181e0080c480082a9090001e20704000b60a840380d25140001d0095886001900509012401020a1880000c010080c0503081583c401541c0081e00d1b80e101d5660b0710b10621031001440c00040d912504400020310041c5016402404030102000700203007011a51030020301c1040c0c0c00e03441122240d000141103178072 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 845572347 1250 845571097 845571107
    0x17131b0e15031b0105030406020f1e03090d030605010c0f05010b030a050c15031902070305070206031f15052a0f100506090f040201050c010f060f051302070c060f120c0c03 75
    0x54284100010f12140d46060010f011070001070002416180c0100e6800c8020705c2e450305444990721181c0b040391242401c0c1213442e03040d91040d28071551034020821200c0465000340070f4001100d6042e52548803140542d2100b454038102c00200719819525003c4284440d6000c1054005444c01000a0080c5084c0d2030208a0718484409608403448014420004602c502c0d54500210310000b082c0540d40d60800d26003112148540e29000798032080c044180a0f8140c0c0205981050414144012130400d40311603040c25006181082100041d40030045009000060342e20346041480119407600e2141c00c4a404905121080c24031111561207802c400a420016005070780e0000000c1c3c0301441c99040a1060480c031540080c0040e05201c800500e1192000c000d6010413044415403030300b00030a036200c0c4050310034080c1c24444c05103da032100d07184004100c81392003160406036012402e00c4000e482d00e203050781c0c0696006004424411103098020103c1994080c01c0301c07001c91580d498060100b1440c1c054a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 845573597 1250 845572347 845572363
    0x8031f0b0d1d06160c080f0711030a12050d0e0304030501051609060903082b0b0102010b01140d0902031603230d0c02090a020f13050117131b0e1503 65
    0x101d04014010b0074a21200214095401000c00d6a0110350603900b4081590039042c000002481040c00090300e11850b00000b001c0e00403c4e04c110407004030018807c00b01952000d00d128083c041072104d150b5070494034080d90003403001c4145c805000c104898000c0003035007103030481d44c8151001e135150340810640a40001a9541e411100e007849807029003070040040421301c140c000144480f500090302001102000e14403070100c8041840c108000000d00e0350b00c03015101c608901d0b4099800d00c00c1c08800c560041030800c0c41c0ba0200070764207050030b100100b00000303000d2450b01179130540180c0f12880d00c0c12088013040300145001c0c1c4c00401d030001c5803141c0001e441c0d005070b001200f0ba81000310201c548a911001c1c031404c0680450303558596031030710140c10000303101c1d00c078841680103000035241e2440d052244a202c2255004d894031001403026040818000c90b048401201d140c0c1c07560310900c001080340000e408001c41007503034501c04646402c0c12000200d815108007484050701c5c4094440c0d0300d001c000c041 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 845574847 1250 845573597 845573621
    0x922050606011e0e1908010e160501031a0409020103090503070602071a010302060a140c030d0f0f18062004061d03030f12090102190f080c04030f08031f0b0d 69
    0x141c68943c09802000036280c4282180310b000040307400c8206075070401c1c400f00904450ba000b08a28010304005503520b801202c041a07000c650074200095942c004e03c50b040340030b80110450042507450030100b1008000d0301c034003241403695440042d408030740100302030301c4040c2c490765005035034201da428801525140c034011034410402d0722005100686400c0243d6020300c0b502c1c22f081c2d1780c01e0844100303d032036800f40c0d04001d0158480402d05001d40002508a1599045440010814040d81204081c151203800c8941d519418001003210b002038456408040300c011586001e0840403580d03000c0541d0f582c05039101100141c0b241466151b00910300075640d01e1004100c00542c50200300840c2d45055000f242000b070480c41c02c1c000000e0320008213404a600548081624050809038980090503441000c0d140e1070020f01028001407100001030103d60582c0d40161100380b000c1480d584051039030748020501c0c000b04601034540c006500400400030b0103029240504cd441d032103a022501d088a040d03403040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 845576097 1250 845574847 845574887
    0xe01030c0305070e0103080d020307030b12030d050a050105330d0b1f021e070308041520190201031b030516020a020906060304030923120c010e092205060601 69
    0x1080011555008c80f23030745052140d80542c40e40d540207416030081912071030040c0c0240c54510ba403c07e60310f01000801e45186000020000b0303440722505602120001d02070039801a802d00b00303c440000c00b40f02481005001451070000c40000e00d200300c145904440c070080d94042e1601e5210386189448022000c11400402510413200307001d0000a540e034075011a030b4003035440d140304072001d100c2091004c103000d0358210000c02daa569840e5881e80c40e82140462004c001040b000e43d17103071031984000070143c0c14070804005012078805484810100902d00c5422814195940d901c40b00e24040000f0011a620040d00c0024191404642c0340145490844400085400c5040b80c40e0050742d85111444e0808003c0e02c080751642c0d00c5103401d0b80e25040c070303801c030784206c1c1c42e0780c065100040943c0c24501c10380d400981b00300e000b0090b803031030241e40c81101150a81c04140d48550311030050070540c0b82d241d40054080c1d401422201d0301414803407036400030407083d66036030070840401009580020b40980400700e00500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 845577347 1250 845576097 845576099
    0x20706020a030c081b030703020c0f2803090608072001050f060406030209011404020c03070b01081e0316020102030d0c030b180610030e0a060e0c011206050a140301060e01030c0305070e01 82
    0x102290940f541c0c00e100e001101001203001140709a0588260301d0400c021502101c00b2024000d681da06040400031001410b10078cc1611151450721882d401941902c51207062401c004054519050090446080090384a100f007224030303d00780b50710703001507090000207410f060624600741610030083c00d06000303904001e402c20058494200460440e0315034802141d54014810018000c1c0c0300d1a40080e50912003c40d801061040406845040780c220070201c030b07001c0c005c907811505081e0005c451104a0f07041406480c4000c8400103250764018414811380749002d0105142c0c03011140001c0300003000039621100e4040505010310010180c0300d22202d40012842d0040005480e41d0003011036404040d210f82c14180145000c020300c2508950098041c08101c1c00110483e83d074040900080340001c01010303480040c1304c00c5100c1e41095401c044e00c1d1580c4071f81029088485200e0050304260950b603501d400059100403c042e42c0c2c040c41c8540c0c4183e4845240d810002e1a102607030b0010420b581c0d140740 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 845578597 1250 845577347 845577361
    0x6060609060904090501060b04030b0f0105090402090103030e24250803011211040c03050601030c17130c0e0703060303390609051005061819050c0409020706020a030c08 74
    0x401e90300e000c102250042040f030800d1a1950241c447c030b0780596058040810301104000c80c1000c441d02c24604002d030707070301c0d13580e038401c02c02000d10010307100a90800840310043c00824400c1200d9051248040c040360f180c0e80303078132620300c60402602e0b0000e840c109001c103115030095508640788207076220006950b8100e08454417010310602c01131045400ea00700e0030a04a08111301021480300c0070000610400080040c034001a02400c070880c1c0650000385410724040300c00e8040c040300a6001c40c407007403005141d903602044070b0f004851078001303503142c50302140b0000d203e001080d140c5104000540d004141030746580780180403808a5460b0036000610042c2c001200540000c504211402d44415490f02401d507060441c0107111404d40a4581d001d41040d03256400c941d90402409075400b03a4052101c00d140c80043c20006000b950041008086004c4070f07500300150341c1040390000441c20b80d65160a948010200807640310b24400c0301c083d600818282c10740c1f905842040c6891103142408086460565 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 845579847 1250 845578597 845578609
    0x4060b07021302090109031718011701061b081b07050a1a0a09051807110a0201021203070e0306040b06130b01122d050402030c0a05011407030309021804030206060609 73
    0x1000040d01940d000c6451404e582c8a80030710713001940c0102c60199054503591410b0441d0303004c005110403401d2540f543d4011544120300881d400300881c0c1341686c10340d0074031208460040806191071190b00c001c4440d4030110700901d004080850700105161088002001d100e800c00b6a03640c0900d00c10095200204003203410440031110b07081c0803182c1d055491080580560340c0740030a17001382e6005030f00c44030581320309c01000b11018019007103620354649a100120800381e41d02c1e500e80c40207005030013a64150301105882405150401003e042c6507144600d000b001c42d00c0e10108030b41c00d4442003000400d0100c01c2c04c3c031259040203003204d00400d1060688102c00a803007600301141d00c40000d60790b005154074199951401ea40031740c0500f019403901c107502604a401a12054030103920070b0043c0d511a04c0a40b0302a10401e003140d00684079001602c034404400d40b159003000c4816014191904103400041c1c2d51181001071650700c050b03105019040c83d0038020300d130081c01030555014090030000b07102151f03214 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 845581097 1250 845579847 845579869
    0x513050604060929180a050a1b120203100b0c0604140312040f0516060906030e1501030b041103151501080108210d0e0307020909011e02030c091203040504060b0702 72
    0x280c074880c0c120f6481c510101e511110f4200c85c07003032520443e40034044451415084140a08001c1d8802d005030400494443c1c040d12038080c441010038189c00c10114200d100d03801442c3d109140d200c40200841c3d507000d154a2a5000c0b0724030740d0250f00000c081104008444010b4000ca207403001c011818001507a501180d8020040d1001d072100350240030090400c9010020854407018142d9540303012a0354031000341c0000301078010700011909100201c014600c0c00620145001c4030030311507681503403071516003441c0b4140c05001901c6101c1e003101c220f91540c40420082e92604032041c00f499062600749600000b40307001841a03810040c032200108040840059602251648809101d03001c4d0010048004a0312562010070781860814416591038003010003d4849103009840302050b541e00d00080e203081303507141e00a0105409290848a4414007654040c55000e4461301c44245058000000500300c0003d5001403032643d40001801c1c012801c150050000911044045500f013400e00e44c0021561000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 845582347 1250 845581097 845581151
    0xb04050a06030f020c010929090c090601020a060603082a0d1805030f1e0633040f0e19020310181b0f0b04150809010605130506040609 59
    0x1102c42c6030b01059010344c1100c80b1026804002c00c45843d880c40c26031801108c0e00822001001003040038046110754291640c07040d0401780103801c0c0c09941c0c2041000d10480902003504500c115900d000000d42d051081c00055406902080c1d12605c1e950a00900c0130000d4031001c16086e0610103000210710300040c4204441860f0802c0140c0d02420046240c03d1507007a88425411301c5103590081000034085500102c6581815515181141501005a441c002503403840641030302184039280c502c8807038400054a004807410031040c2003200c400a000c1d035010100100c0b101e55108100301c041c0800b00540e5460082e0b91195070751542407600000d4a540e550300c00a0070b80c6881d580c420300c6c4125910411200a0b80c8107542030301d83d851132406a180010f07079001da071030206001000442c00c00042001d83d41100c2140111820382d810301c20040704d10242c0900600c0b9150349a80c400b0810381d54112000004010640c4006102e02d040f00420007980c125a100c80403003407400214039540b00e82101b071074441102c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 845583597 1250 845582347 845582351
    0xb060f070f080d1e0e01150b2a0f0c1504090902041808070605010f03020d0204020c010f05010b130f050a0e07020f06040f030f08190f020409060602160b04050a0603 72
    0x410307420010300b00c1c42004070150125207001d80200010802e03070b0700b0b4444d010000808100d841c06050300315003203c0d26002002c4a0039404141040507110f21b000070b110b1004038041840f188201d5100500030f001d844a015080f07a0031241080c0400c00003041b04404a40b8100c40d224820707441c1d2051400e007441980118880c083c0c9402e000b8041d07450760380050540d0743c29104200b01030500b43c144503146800c041001c40d8280d081a00001e4541010044241aa5002455402c040c2e07079903401c200081d401041115140e548426065600302c01c40c0c411b00d0f000380780d05d0141c1c0769500e2110f400c06d003100c06103401149a40c03220500a00c41e03034650424080a449a80320300e44619206c002e01070380781468182d043d8030720348550f0040008000c001c03086c00d29258801c0d254081d207004103400c00d5030300800880360f40101100f003082035042c01800d9045094550311410b001854640c464844809446298102402580c00b40044400c000c968118100041090b246d0450500b414080000c45400091081c0c0003015 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 845584847 1250 845583597 845583623
    0x5070912060b1003150e04021518041508010c0513050f120607030b1e010c0809121507180b0403060203190219030608010c09090905031903020c010b060f07 68
    0x116450384085003201e07000b01802d100304049003004015002d41c0300d075050005c519102c0040c041d50166659401191b0040525100c94544814400f00750407008107114100e0712103a03913060750788461080e5a0030020212181c00502e0810500a080d9482e00507060200142044075085541072185800c0507241c0440700c41460111100c0002e10107038000c412145103028920500c0170550705980010741c0c8200c1500d40360148039501100c2c1c0051210207900364041046030155034002070910700240030208005210b0302d00c00420ba030025141282c0c10080c4080320801005101a00c2e4000e2004c0d46462206a40d8111250508107540c4241c0210b11000344041e40110105144030400343c01c001d420803d40200310340f138000302d0076521410342d04109800d01081c80c100e800709100da01070141e010960680c2c0c48000c0c0c481c1c5003100c2c3c3c034000c29a0711300c10b482c4d40c002841608144242c0c42d01d03112080d1100d54000d41c0390104030f00800d086484800c1054031800302040100c1a910b040c3d02550041a044104030b0580 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 845586097 1250 845584847 845584853
    0x30207060c0204110c1b0609180c1c2c0c360a0e1219052b1406240712091e15322203020307050907110318031005070912 53
    0xe409800f850180b0f48016a4bc5840d600c501944070b490041c4102c0c40b54104600f121b209000000d060104501c0c07150461940c00c041e03414045400181d10180c1308165203a95803201500d01181c80b1508050890882d03c81800800310041c02a044200000009409442d800100c20406841412100050030840d15540d200b0030b801a020b64403e004980030700b50b001101c1c01014014000303907007014100a03181c07071200c1c11114104981d030b502c034900c094990582141c0031541d580c1204200e8241c29941402040340d200099008a4801c0080030b01c4c0d110b00000c10700f0007400e002d03e80e401090000d011500c0c1c01e41007042c0d440b10326680c0050341250034204203080c0c5828280c6483d840708140701030022410410180003610040c01054501d5150341d44507141c07543c4544454079901c0d81c1c80041e51640c01110b081c0010b10305440c5290300b00c940b45c2069881801a6408642960426001765140b403002d02100d0b280d0b400c0134042907a05151100b030400c0740740f401c0100940603140344d025113100d0300c403d80000d0f010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 845587347 1250 845586097 845586121
    0x503040503070f06080703050f0604020f09060403060204030b0705090f0103050601110a140706030b0a05190f0305010b100c03120c0203071a1b0403030207060c0204110c1b060918 78
    0x1629001c0e090760442c0e0b0f280d040541d455481e07031113210002400b4100195802d440703441030310300030042d504404100782c50303003800c20001c2d4000306854030103008204042000d40d903514008200840c4100f40142e00d0721316504240440e03210042240007446000c01201055564002c00c03811032050034240052182c0ba0b40b00100d403503c1610200fa503151140100d048180040f0100404134104408100c030f940907216402103042e40c14040e1169002091903a09104600e49101071510f200d41c2940342044984e0748a44040780000590b00517200b40c0d54500643c1400c0c100050b0010240682d81028000b680059a009020181c080c00e0700000d5951001802c400070300c24021103030a5a00104200c5040303100726a03601d191002a100004901c4083e00000c0a0244250554040f2a0540c01900b4114582074040c0c071160300f150400c9900548d1051441649440c1e000907080480d280c500a1500e0a1030003101e519a43c840034850f0b00c41d00d0103001c100f5080d40c511410b908105240c00ca41c100540f181c0d407202d41 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 845588597 1250 845587347 845587349
    0x3040b01030303020f19030b1201060806010b0706140712060b0307080a050703111c0e0703030c120203040f08060601020105060916050912030301060807021002120708060d080f043f050304 82
    0x4120448000c400e24015407503003005823a10700490f01045802140319902e4200d40c9648a00c02450708440010020040c40002401600b0f00845000c80c5800e042c841ca032580f01c0301101c001001c10724005001072200098807c0e000503080c100746031171950505520203081120000c00720358101c2d4403080040c4a0902c80d4020006042058405684406a401000385040c82185110085904d000c82d1510140d00015442d011640c06440d0344c021013156807200140110301304d0450056120811000580340c2c4407254001c010700c40c4802070041400c3c400002800d40d1000740146206800c0d00040c0710004c1c0300401c4400080e40d5505085a88a00344000309902d4400c0c8684500c4500020000140803034205034400d101e91b046500742c0d0107503580d280c2d00204a0041c610000ac00107103c80c0054602ca008207010f0381c0110000740515904507543d500d8041a600a1b031200c10092804501007152006514074410001c1020020010000ca0199820705400202080d0700e0320010b40a81001449800e0003214 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 845589847 1250 845588597 845588617
    0x4032603010b0702030c030102090f0d06060e0c19080603030904020a0c06050408040f08010504080703110307050a23031e09060408010608010c110c1e1201180c050603040b01030303020f 81
    0x3a200d41c1d40d482035044903000201c00b40e010b4018015070141e1343c503040c402c640c0c6901006249600400c0f00006200400c1e61000382110107030703a12075010410b80d0380c0d0305105d48226107140005560710491322900315a903900000307190901816100f885604d0790701109075805030000766801a110303400442c1c02c481405044034080c105034640303420710050050b0f101c020025220a0203d0f0b56016035280306290888404980241c60540300b0b22880300042c0c41440c40400a4200d402201d0030456a503e4103800c001d030b01c202c11603545070707860888641803841c0d101090404982c1c5000d1418400303421603400740f6a1082c5010180080b0016100c140e66071000e050382c001c2d101c0301008001168a0305001d500030306004a41201041c00419100800c4030001501081002d01801440c0c0a0700b6150003880203689034401c203503005d04841d41141505030241f003003071111000c8260a0046010b0381c100000c0c490080c0c0c01c03160181404000b000003103801c903071400d030440e64103181c01a9201d04051152030300d801035408030703 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 845591097 1250 845589847 845589923
    0xc0b0a06051c02010305010b070308010e2d060906190b031f29090f2e020a02090a0c08010611070306060303030b04050a0618112124060403 61
    0xe500121141201040c40030310070780b0700300326503601e4a00d80481030203041c27401000030b80c050005011180030807030b0081d000040c076000090948d031004200e0141407024549020842c031208104902c6113003010320150010380a0300e80302c14040201e0814000e4103031a00602031202000404940c10032118440c80c12104c0050807a40d0032a515003940d01c5400103032003401c0d141c10a00c0401c824001e8408001c40b21103200041c0344071194800c0c0303406d000098102290703291031a0300c00c140003215020b180c0c80050082c8601d0307014052096440c810458042c40150440d240b403840c09850707a0310180c10600c024199202404c0406a80c0c81024078507180603800d8100400301401c0c410700008150301600301022280080f2424005940c0d8269044200c031118819025542a079a2088450907802c1d4480840f00d807d0852281c0f40074550510241124004405581c81c0ca4442d4104034500d4444d0b283e2484400c80c0c801c00103140700483e40090024000d600000d081ca1544400d1149082541c1801d03a040020003510 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 845592347 1250 845591097 845591119
    0x3070314030316090b070308041506080f010e0c01170c07020d0605090105090a05070504020d0f02030f0906090309030d0e0102100609050a0e0c130b06120c03070e03010b010c0b0a0605 80
    0x104644a8100340d0790141e602252940060f506402901e40d1000c0e91604003000b8145200740d2022909885d010303101307a5403036802c042c05507122181c90058070041c06a4200504400915406d0642102c403c42c00c000340c55040301c2002102c90307901040080e1590440c000700d004c141ca41740610f030854441c440000358407c951a49032403c1140d65004284241c030040020056a40d43d01c001a48800210364001c1c441d4010340b00520440c6090fa02410850f040710500042c007083c00010542264002c0e2016118203802d1000c01039600070070000389500141c46005075041500000c08660394010072403404003484442d10200103a40d100b0001c5900150358007005103e42c075a111041c100803c01929030040283c2400c45013440b81100241003484260054850300b001681c038403803500180400c3d0141e60340045d040003003600f5074125080f51030040310780744051662424140700c05050f00941941103030099040103040700c045d81c0c01c0f00085070040d070402c000c02007913500c0d81d50500052041741c002950004503444 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 845593597 1250 845592347 845592383
    0x1b060b030312151008131e062a09030503030103110f030105151c0305091c02031b18071205060307120503070c06021c0e150d020304060c1b020906030703 67
    0x21402a080381c003644c07400c06401c201002111204012a0178043e645200075029001a1a682c01014024026101501c1d040308554030102947c680007460003902d00442c10100c0c4010310300d00880120b00082c2440e08010b85199901a1a40014071029004000c0360006804544401540a00c5810018020401454481c41c1c10702d051503074060881c081c40c0307e031100d0285104501c80c04032105030580c40c0c00e81800905400c101d001e0107000107491603010310540c00001614204002d03400301860441c0e0102034507004050142e0a924008c050703404080410030700c04455000031074004401400034000c2941d82c0c0c0d20b8042445e10ec00d075406080200050460242802004409400c1c210310506800c400c05584000c200d903180f81410516038460f05400104400c18011501c20865510103814004480c20715120502d458200d001244032140d000410001000002d2160308204161401c18240084018602c10700c290850b050003805500b112000c9030840c1e41c20086200151792102c502200c5910000b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 845594847 1250 845593597 845593621
    0x40806071101020f0d18020409140c0105071109060d020901270b100503040c03080d09061b051b010f06030302011e050403050a03020a1704060e0d1b060b030312 70
    0x100c1050004121070000c1590110600031901121034580c041c07070502c0019204d8400a24020600800040c055884000140c071a409035910300303400780b85240c800001c00a05507040c50040c148140c10458100701c0903000401c3c0710b040c0e40303400d0f0301921451515603170003010512140c001d0f070003c0d42c0004200000980d0002c220340211940503c0d8111601041c070440030310058a44054009600641203c101300c1036034802c101560340075006150402d1704541e240c485036403690200300d40003496612401c100041c070006018611204c0c01801d04030003411038468000f04580142030813202d00500208100340782010940080e1510b4004580421030241e4074038003c1e000700720b2100100494902081000341d100d400c2e00c5654490742e007544800e807402140240480c029407062401400744100f603840090b009180052a40c803031441035100086000d00c0b1035a00c2d241200c2e00c0e01400c108100c10500c448c0d0325244440940d00143e000401007125040500068194041c001501030020a510104030b005070b142c6c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 845596097 1250 845594847 845594851
    0x507060318170406120e030d1814070f0608090714030304051c020411041212050c0a120306080115030f02010212070308060a050609010c0f170c01053c1b040806 70
    0x95191480000b203100011011b541d41030464103990b410501c00f0101020701d90300400042c404015218003000c0c540e9482c070265106801d0900c2255008520602c2805044041034000e00210306260381241340107400308d41e491760140181480021a0420101c1c60b4070f040050b1406824002c0c40150010641a20384401188100040c1c6c412400c2032140085641c8180131102507500f4851012200255515034503040c0900b1010642040410408522011014003001c04000d200d580504480100d244009040e0b030100d400c00c608591406c0d41b00c204004010858030704032070340b1952000210102d800181e0920030800032451640800082e10701c201a4091505c40c82210100c40b2600140d8607030301444164012180a940421084898400410407002c02e510f59144107e40400848128150728049a00452503c03403941e1f450b0014810115105507030303041130609441800c0b0b0b01d540301707001880e146041c1e0361f20a8032441000001c102240c0c40301c0118080080c45d070b20415134840e5110074469480c0e40c2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 845597347 1250 845596097 845596109
    0xc02060d11130504090b070e010c08030712143702041712030615031b041e05090702150c0c0601120203012306040b0a030b0c0712050705070603181704 66
    0x40c030101182d1860184103004a5035002614800360366687d4000340e400030004d4038044d060089600c6d4260006404100952252907107603a0340c050308a80501c290140c038013040d1980120364408040103849500b403401c1102032902c860a1000032056290240c04100c07207803d003101401e0001402285441e1448184001940c080d4225448000784584107401c40c0420358003180c0c00050340f516003e12610301c40c080c603040b28595100803041c03402c0201d500c800ba400395005207030002011800c00d6220b20030080710b01c014001543c0c4640b1a140140000391140ca1010b040918404144041080002140d081d500020040407ca403403030f5071114000500b00902010880c820340c2001002255400308540c1150207021030900f0ba007194555404020152255101d05a00120504000400300782611032090050031035000e500d540320283c1c10300030448101d0481075410310800f04041c000188000440c0740454203030340b50000314000b18012141c241d02070a0805001e104c0400e01c10919041c4220040c0300f00c0f06 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 845598597 1250 845597347 845597377
    0x60d0c080906071805010806010e0307062102070b070522030f0b0a020c1b03150406061a040317071e03020f07050a080709050705041a03100e04050309010c02060d11 72
    0x10b9650401c41e445030b07038070403140c4e0450311040c8100f190b54020841e650700010141841c03500b07031191101091801580d9030001c800141c03010088a000950144c542c0b008011220082d80740001e640c44103202680003425000c1006000507000b130700c80e0040040f4040182c05130318003403900e559a0511411a10110000f504e9900d220804036020407107510844141c0390001c000303002e1680001080784001c8070500328641d09030051000d00000344a040f40e90600c641e11880d40007440c6410105400c04420801d02ea2031002d0508000600204101c480440f0b6190400030110380d81d0329440c40d200480d4a0340364420aa801044100d001c209600030a110780c10403800001c880d81150340c0c1041081c0d00745982306180c03503600445000d229050040e004268007031854200946071507510b0864a4200b14941410300658001005110801c1c6891056030000e1105014204c02828507440e0640c492248182d02030500c81c502a0300011904d55009594036800d582c00300704220b10344000407040a82c0b010703d807001500303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 845599847 1250 845598597 845598601
    0xd0501020a031104050108070c14031b070603020f040905040c0302150702121603060e030c120a020f060c1911030d0f1404030206070f09050415080c0d1e02060d0c080906 74
    0xb0300e420944d41200c105a440c09010307101c0344025203008202500a40c3c0c01c0010742e4500c010700d05c081000700781c40e1b1000c2001d003408070417140b030b02804e001d003e40100b02014010011350505854441c103860640c0c41d004400116900c40d0f1901810542403907200070b4018280c1c1c4602e010501c24000035011290080d10300c0d003036000c05048400c1c3c54400e60144900c0c040701446090000c142183e00107030000e00400e04681c50203101c0d0042d01d28000c0026181c60190800080d010aa00d6041c0001c40d80c0e550290000e1429007000005101c2502802608600b4020045160383d40d4610448490740301e042d4207415666503020142d003201c060829494800c10403803c3c0504a050084c1601005110300d0b099400f80c901d07500d0390a011211416140f0a0100b005012540481c0d00c1d035440c1309030260744900329242068540342403051410600000392462003580403c003090085101a04c1c42c54242080c0e0f800c18003010f02c40e100151807809441c00c3c1c115840e180140710a442c5400c04e031068040c14803802156565 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 845601097 1250 845599847 845599871
    0x20f04050702030a1107330f0210021c0f05090115080c1216081606110705040213030b0405030307020c0904110405100801090b060a0503030c0307020d0807020d0501020a03 75
    0x2940e81916441c0c0180d2040000001c40341c41001e42a0031444a501941c0030343d40d59103a210120000201c030781c6040850702c801c11940d0040820010404e40c25401c0808054400c2200a510f420401034450718042e000506101c031449480070100304500c1c01c1e541044181407400344c003c0100811543c0050315860b14200308185e28050401201b1980c601c2c0082c5040110001407142e000c01030000000948030314100b60000c100a04645800b4004043c002c2800c2d1b07a100104c03900c60403280c3e000c1414403254800401c00e4000219103603040e10400e9401696950710348000719031880b100c1c0c1c0040c3c64002d10307105120803c203000c8015405241360341e0071104003620440400c65011010744008120b0314049422101d80c0c10103400030340c0d02c401c00140e2060004d5507141640c1c03c0d5040c294080f00c0e240d0980b02008018648200300001414040d00194100303c031805005980384070700301c0003a00c0f4840b0074514404016402c0116000294007800d00c0c3c5581140b03140c442d000c2d42080107000c02090034620b40c103840d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 845602347 1250 845601097 845601101
    0x30d020304032a0f0902070201090e0112020d170d0f0e03040f231027230303130b04061d09040b251701050301020a050306010513030f060504020f04 65
    0x180c903041109901c9403038041c01c07407052002403100f0846100c00041c0380001c0c0821450a0f40b0001c010400f409a500c140301c3c4001088503803103401000c8102480300c014414488070b8180000c4040d07059800c0200149681425240004521070120507010000781030202c0c0840c941206a6080d1860030038085a895003500c0d43d120702450082000c40d245041040140010040e05200400aa80024192030341600d000c074031140031071520407000c294a08469901d01100e5031100740311120b802001c1a400e824180b10400780842804c0031b07620521110b43d00341d1940e0301030080315012580c0c2e00108000640e074800380c070284e0300700384501e00100301c40100019801950590f2114840030060804405540360b5403140018000505220b41c0c5003819242003288008002065450340041c2d1104440c880c4408001000c0070070580255000380d00512a070070700345400c4001d581e04036809080c41a1101c00702d002c401e10b240882d0f0f00107040e0321040c1103640b041c0216548803600480c02905c0051800025500b8001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 845603597 1250 845602347 845602349
    0x7090801053904050306042907050a03020703110d020106030302070801050403020c13020706050a0e010608150a1e09081305010345051506010c03210905010f0b030d020304 75
    0x4850000700c00300381c541c0340c2e01100007120b0909110581019110404245048011941190400d98450003080c11010600c004111440b2549a600351407600c8400109203003d010400d030185a004035424040600031084200f0342182101203403441c00c1d414170004e028294074070050300035024416000c121114103020340c82c40f55030980c00524525807003c00344411800310205218800740d0038030056000074410300a032802444c001b0408244000662007080c2151041d0b4003504030b550000e9480b08082c05034070405a88480740c00c50020b40c941c40788817840c03c5c4052401c03501880030320b80300404d41040800340251004c0f100c1d40d06207004240e22100158105c501c80e4001c81e40c004c1c03011001304e04044a03c1058402c1d03000c48407007448007801e00340011090b910b1211084800350804000b81c2c24104c8040341c00d943c4581c0920301905400100d82340608800141b4a1038400704908030160348100c40560420000b041d072010081008000381b004d648018004032010510901420003a400c80601c0081520 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 845604847 1250 845603597 845603641
    0x919230d020a0209100b030405070e060102072103020a120206090d050903031b0c0402072103060e0117012306090106111002070c03020a0806010f120308010e130b0709080105 76
    0x2440030695001c221a0104c000c040c20711280004a001c03418aa6103030146010304d200340010300d002400c01020020b0100010074150455010800401030107000c88100403112800e0802141c948074203040c2207085c5007540304064041c10300b049442c0301d8107034001210b611881e59141990310800d000d80701201c80348289080d0580c96030040c401c01e090403013022000840000080d003203c25000205011506a812440c01680c03005d51448403d05180038400700320034090514a010813460741041d102041940707060003080403141c000d0400101d030800c250300c05000481a03c0485412510803500d0000452085503201c1c082c0c45103400000b0031074083d8010407040205a800340900c2048400154025008030400303881d261610000040541c941084290103408850050211036040c010700300c1c42034085500901e030710080c21720001c004ca5032049006040d82c3c3e01d80c420346120380341c0f0020105a200c3c1c00a0180110452405112169400c18000d40889100d40300a1106948940c150720700d8400c0c85082c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 845606097 1250 845604847 845604853
    0xb041214060f06210709020d05010b040b1c0b0a0f030327060e060f0c060108062809060209041a0102010b0d0506160203041a1b06060a0501080919230d02 67
    0x7041c2c0320300d0000c03200d100e101c1ca0a01404c0c0381041c01c0807218542040c41c0d101c506800c0e80001c0c9801860b81c40c2c0203003030140070482c25140c070349440e0900704400b500c2400101200d8180500d00e400340f41c0c0107a04043c142c124011728680c00c040c2c0ba0456042c01540610003140400d16000050401d1416030901407102075030320319400d10390707864004142c580c1c3c0b24507084554400c80c20030544040c030b43c08002400b003421000000340f017a5030400d2507040c6822400b4264950349032160042c5210b4501c0606108841703040310b440401d903d2050b02d1702002034000c421007958400d09000386070180d213500306407001e40c44000364003c0c0510103c400502007103c7c20744a016019820081c0000d040b0003003562030200b8265640b048070718040d514451f501c0c1c2c40101c10b41301802101c0001c2d07080c0c141d5041030400122405220080c0000c1d06181001135030941f5148980c1d414403410400240444105002020308250a007020349108080c51500700d6088170000c0001803420111050107280c0b40c03000071072000200e003980007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 845607347 1250 845606097 845606101
    0x20709060e1b0c01020c0a0c0806060d05030d0b0f120a02011407050615060c250501110c0f0f040c23031e0a15060c050f120a050906040b041214060f 65
    0x2105040764010f524024a940d020400c600d24440100074043c4020b004a01c804400e5041002c0c5504001c40a802c59104902a04841c0042040417003201d00319004100d00007450130100e00401e038071020640055902052400405540c960046201e8070304a1007680c0b10b0900315030341d401e1901c090188181c00b07020760b801031340029442810b528010001d110000c2c185800c0c100c1e014203003440d140c02e5400b80d50703581c1070380240d107444031246030342d45000b84c282420808202102103805e1540c6111000083d44101000420301145480300782d101c90702d1220103402402901c1d80600007078500348030f200b1202026101101040440801001600c1c007841d01e06000c0400724980d4901100b034007001030f00c0c060402c0d540b0200252990b20031a51440204096120700c1d41e9003001e030a0081c00d0540c100c0010b0515046203036020b4050b0f40c2c0c0300881e120602542400354a03039100b0030200e5503c0c0990303044140100d07000240403820001c0c1c0c050054625108546500203882225000c5869030415584545c150101c000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 845608597 1250 845607347 845607391
    0x708070912080706091b0f0603020f070b130501050a0c080a090302070308030c0d06030b01080c240a050705030d020912030c190f0228080a0f0b1e0106020709060e 71
    0x50031014052913001c01c00503134503100d0f402d2958292031340e02c24130300d01c0c0501080010303103540050b00200300c0c03402c2c110300b0142100001d4806101d680b030010300314100400054400034500f469084400c3d0000c00030440ba1410781d0a01006210515210012620b1a00080c41c2d4450f0b5014484019500d45d02402c8020303d199500c0402c1e40000d00314070f03030740c0b0814031141c0300078400c41c450030b0000d60141c0c03400a10340d40342c0484070b4145107074842554002d08056010a00213001c4d01020910106880c440755524110050200d80d98062018024060302000501c000e80540355000f80454543c1100c0307400030a810b210205540380302e042c10310710b016004000d1101d0720003280901c1d1000f007801021004a09031480d80003601ca80d00445401406104850114040d0602040c110014200d403400604c40039007191108200c3c2c030129440100542029000140810a12031001000860003500d22440b075840c1c400280d2900028060310b0b80d0306150001c0010f00d25008160b16000e1462010b2404000c14041 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 845609847 1250 845608597 845608613
    0x501090e0c0706020a020a4d10050d02222304111207090f0f030c0311010c0209040b06040f1b140c0d0908060a020304051506010207050a030b0708070912 67
    0x4e1001815805122001c1010039940c0808c85800322a00c204001003180f0b941b211040c81d9010300d1004803c1051020305002c07102d1060006160400c02c60b82401d10700e24501c03040301c0e035100d54000781c00300c94000704540100540c40b443da420351410b02041002e044d03071200101060000c10340d46010303c100319000d1005a6040c40d40c0b040b01c122103402c1000e4980804421201c0502e1801d561000018100e00740410105c1c2c912a041c030301801c1c2951580001a180d500e900850f0b6201d40009044101c88040c8015540e004059185003640d0190900701075103850301b00085403900460711140903a042000d00b44840c042c500c10010b20f945002c60b00038800a0842040f5906c10a064000e100300c1c4042156000c01441040385d204400c0703290b0741f124590303402c0010701410908003428001d02d00b80140144070003c0e2003c101000d109802444115082c1d98a0004034500301d5140d10042d0003605840c0040144940c40b4052481441e40d519000c80648030031508981941c0c19200f5007007141000105100011400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 845611097 1250 845609847 845609857
    0x130e15130f0c030b0906090d0203040602120d0906050f0a0f0603031e0909061404060803030c1e0d2901080c0a210507031d01090b040b071b0c0501090e0c070602 70
    0x2801100400c0b80d16503840c1e141c20750b01075440a2940c0d004504000c8480b4080100840c1c04100c0e00c007640c1864545030020f951a00032100a14200740040b8001ca0480040d610002c10990010b2091001e810029504001d107a030a41e001c48840e810404440440c2c51319019070021260306079035002880d50203000070100b0b03003011f44405040113561180092001c0320f600807503015107401c04c0c600c0f0160b40d5403000c00c41142c4183d4080f00443d0024000c00860175200c00a42c0d241d55006110300304c440694400782542d40c400d82ca100581c6d5882c084611015490420301102010b55664400c4041c4903000015200200212000b8132929010007503140e51610074070062010416a9040400c00384ca960f58880980300105c5480000036035503881d40300294850140072a8200000c002005000019260350056210007080901560a8100401c01c4076110b00c0705200415a00481c10a402c0b0040c0340c00d00c0701d16560322401e0b00103a99104080b8000301c103010607500818000140500d004204e43d1010b000c0e40017 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 845612347 1250 845611097 845611103
    0x8010e0c031909060c0e0d080a0804050307080c07060e041e0b030304030515251430010f06171807081203010f0f030201020d0c020f130e15130f 63
    0x140c4403444a007039490380600f244484c4100e20100e280038642e00004e0001002903101031045501c200210081242c900864400c01418a4090b0032546c0b182051491845446d00c02003001c280040e8200300b0311001b0845c081900c02c02d580d00d8242c03448180410003030703503003c0400700b14180d0340780e0307030009504d2041d44440d009010107401c0d40d04040d0380351601c0d814400101c22001e880901e11040050343e6418a8100e5a0754009203e400c081d042d03885070040094507017807290207101600040310041c0d02c580391240b0820702d280250004103040d0102c03c45402010a101e10001c10410400200e20345000e564071f180a000101e4002c04507540b816080a4903002d691140703500e0b401006408924501e00b0f011b040c051405110701c85c1c0c0c2d43c3d4540318600d140306010364028a0130220030141400140c0c1d0200d00400c006219281c40002101140002241a46002401079000052513a03170b0f4030740c0c4040c0d08130000010100042d42d0380d41411144460a4405c116441920300500030799410001d440500481c840d180 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 845613597 1250 845612347 845612371
    0xf080307120e2d0d200120070609080a0201150b0f090d020d1a10051903140115090902190e01030213090209040f0b1b18010507060c11070608010e0c03 66
    0x43c907404144c0c100040d07001040005241190740c506450a03841c03004500d40e05a100030801940b940302a000034800703220790304203240400a148420300940380c1010800580000311140d0740d0f03210040103030091620001d012b444007140742c00080c00c1d00020007a01c030400e81c85810940b400d04000100071034900c0600049074010403040744800400e1710380242120505035401c030480c01d41040701103500103c4903a8820b5220b030642428440740314a003d195403080381c2e805844940f0300702006020703c2c090b15404028404440c006400022440d00c1078006400441c020340d0b04228010008250400700c21807030090481c0d00320803500400040c02c0c000c1d101540072000040008d103d0a0a034009413584805079070130341c3d150120000c50024032000329102178000d00c1880d81c03c103030032071080d0301440e0314000c840300e4030040703039403030040b1000e07170b40180304850740c05a0000003000118400e001c050808040d03940800094412031001150890080d00000e05940894000b0a19641e03402110761843d4002813806510135 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 845614847 1250 845613597 845613673
    0x3070c030309080d150801020405130c0c050f031e090603340914010503131e0b0103060c0305060102061302040f09080c070306050606160204090f0f080307120e 70
    0xf0f20b20b9000d04019003402601151009010101c50f0395640203400600645e48100800c011650f2410121508603071100f0000c078a000ea000c500742c400001a9402034814050500741c411848804001040d070351620903d14103101000400c030400c107008590f18a500301c0030401c0859440c070601c5120001e407198005440590703500a941c40c1c6901103640c0101c2c80450700c107030024402e100000f901d10981c040c0a10780241140341c001500d03a41060b448030082d0601d41c01d0a000760700b50b02c210300b002c01510b810080e080b0080d41d5a1403c80d0007001d43d5890600081c1c9440c010461030b61010404a01038081d15603524042d020135000c101c010503003503405100e1241c1e101100340c0020845d201074502240420f020303224007881c50800c2c1c030030b441005010a02c9038004002d400082c3c140302807a000099016200003d014503185002c0d520362001000c040d29000d1148a500e04010814004610451030ba907603410402d4480d41c020320a4400f80c546d8000c0c035402c121203480c903010108880c40c0c481c800030200b240c028 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 845616097 1250 845614847 845614853
    0x3110412260f0301090f0903021b0f1210050601020f0601030b090327032517030d090f031803031e02010f0c050903071707231905010f1403070c030309 66
    0x65440034007519000b9030003200411052841d4030880c1000c54441c00b0074080c1c848244e40083d00c2d2112854030310542d000380b90380b216554550160342180b40b00003900000030350009060039030351106e490024004460400d00007640b81d5102190140c7c0e6882c0c26001000184d08580d51a420540024404c0449210a210480d1308000304031100c1003000c20600340d0a0b2460b9641d091504190424480e2180380b81d003842000104007400744690100c4141c0c4146034440c44000700d41600f18807a1007413030b0600604000c0f030174023440700684103e404503110340c40314202c14441704400000c48100c0d02c0080d021032010703080515040e68400381054500901d1000151403041c02c0742034405c49c1d003816026000108041461201800e080059074054515121210301061844020503079801d80d42c0180070340000c103008038802c0040848014034110380024280c1100708200c402042e00b0760980d01c0b90900081030743d070910000d640111045032200c0e840d184c0741031644d915407805031907044d0170300c5c005c8080556031030045000c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 845617347 1250 845616097 845616173
    0x91e02030c01210c0806031005152101150518010815061f110c1203160201050d05010902070b06060a1d0f03010504080a0f050a3009050a0303110412 65
    0x600d5030b69442c5c050f040d00303014080c1840c00c0322442051401c1490241449840401c070f03800800306000844454490b50b0400c09c980e8281c4a4600e183c4c3c11030341c282032206100408414050080c0d900c1902c0701c001e1020b510a500030641c1c4203100b5010360303401c840d10b2150002c0c81d1088141d40500c1c050807507003c228138a804a4040c00d00c1d40c801000080b6540d00314064008140000500410100c464074402c4104140f00e035202e101d2480d900c0790030507143c40e6820469015038103903803002d03050141c1002590307511995607002e5408190225000d083c40d030000b0700507140c50803c0d10042017099541d140c0e101c00c0d144180c03000b0f507111480070fa4440c0301041103452039602402400c0c803541c42180d003581c583e080c6130b002904d5084031500c5101072120a000d46511b19902c51400140200d0b5034210800040a04d000a80c8454100407001949400c115101c810b2180000f107a84015110ba5810010800c00c406a540d035070095019124030000c0145d0000301061245115000f8130340d01c002c01c4030345031080c03104030f90f0303 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 845618597 1250 845617347 845617361
    0x8280507030f1d0306251727100e0c040c05090d11041e0606080106171306020c1f06050d030507060b0a0e040b0a05040b18011e091e02030c0121 63
    0x305500428400c802c407500ca07101d0301c2401c109410540c040c800e03010000c04130014010001344450b060313681c81040383c4000501e00b031042304125041d0ba596000c5403804c0c40c083d10340100031141d43e00c10701003800c9040c2043d100701c02061000c0d036150f50400d42110100081f100d0848010380c1c0d86040040110380f07590f210b118002c6562001c0010038010660b01e00c210301076500c2a4414028060b0380e0380100021508003440f00100c200d6500a010195190643c50800190201700500700520200702c45030044c40025030180d1503500f0740502d10004c8250b8000100391a85030041a07000305000c1400c5000034029000780940034070940e40030640c07821241c00f00d40e0700100d61303000d00320683e044024802407011600ac01e940145200f00300b44058035043d203604511120190041000c181c03c160b213000400000c0d4071040540c035010b800b40b00c0d2043d00007641d101500d551041a90806d0307100094020711200c4032004d1244aa0140203401022140d00040d20041c6000044815007542c01c019080a04c0071340c41000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 845619847 1250 845618597 845618611
    0x1a0a0e060c0c10121a220e0307030309140a031d061b06040215070506062b03020309040b040e06010603021b010f0203071707090b0a020a08280507030f1d0306 69
    0x101c81d400c000d4680c000341c2d8511081601c080f0885c074452030440e01d0328481ca454242d40c0c0c03840300808800c2007081030001d00a000202003103002c04180c030300c105941034001d002c0e514041e140310f00845200800054860b2608400100420b0a82210000c404c00e00c5100c1c0d803020784c0041505040080070280007800c24800301c42194640c104104000451a00860f00b052102c0c0c85050181008138543d10340365078010141150744207000b002404030580a014900c56014400c10b0811000340c2c2c1d4918000c0e540c2d40200e11035601c6142028000040782c1060710403c1c41401e00e140049c48030380d180450075802035020361682d11407000c0704003030381c80000310900840007001c4442c80d0060340c80c54a020010704508180710031102d504c00b90014001001d80c4126998252040801003da07035000480090385413810b21a4010070540f004241864810385104e250383c0b0105ca905200c440030002801c04450622071804010301190b0441c840a4400340b240d51460084007403100b07101e007840c0186d00000e00d448011141e172 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 845621097 1250 845619847 845619857
    0x305151002010204351b130b060703030e0d110a0b0c0403020a080a030807171819140d0206071d0d080f07020f0f0a050103110d05010308041a0a0e060c0c10 68
    0x1075061603007440e803c0480c0c5c4249005043c0c00500c01d503101604650512170316124112a41a00c0c0150320f480e48000030b8080c008010310f64815007460302030040c00c000c803843c0185000d00050305030428040c0180305024060031015104d801c100703a9a80e035441c40c015064080b070700c000780004001070304d0f00c60707220300604041c02c0107100c0745045150007425603000415080030451125109101e1207200d0462135009104070781201d2401d000d454901d450142c040c55003240c3c0c20300c504800c5042c003040340800e0035440c124500341c0e029542c00d58010f90ba43e80b020390383c017000101100b8103140110498180b1000c040300042510300d04058545810025401003e01c12120b240c00003070f004114a404103910b403180e0016103080c000d444141c0001041048c1603c1614141a1582200d0284015038001c491020308003020400455860b410582c5803074000d0f01030b1001045a031000d060352028400260346039204595100c24403680760030305100fa9508800c040102c1c0d44100340004005070b4401c90513250503856507440c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 845622347 1250 845621097 845621159
    0x415030c120b07030615030b0d080f040611060c16030c0c1805070c0b01051e10020a050d031401052e120621030c0503121609060305151002010204 64
    0x101d15032450b00070749424145440e1881c10072841c01d104072041e001138035034100056422044800b00d080030b448000d0040001800103007001d40241050701034406d40380103a5039410810049000380b0390791502a54041c045010a2062001d1402164a40ca038414802c4c60b003000c0300049075a07120f1038504a5080b0800301c038258404034805c2c2c9a28402c1d594081c0403890110004040742d00d9100c0d0300041801040c0c000d2180003e4000c2008801d4442c0c00200703000b9003460807011180303000075241c11840c07800712a603004490013071007411300c45d028841d041c140340c19005216901c0e1408200001003403441e240b80b6950504003482d09024611600141c500c040d480700d42c060100103000c00304448e0680c00020302000640d00b1661440351510804804691508020603840c1403400d00a01e0342c0140c640c8040c0c1039003101e0801000e02000c443c9a564518281c4a0041d05502e4800139400d840c000c6a485001420b00150800c0070b00c0c06076166858620580001881e040e00c503a210321110b0320768415800300d0541116 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 845623597 1250 845622347 845622353
    0x706090201030e0a0f08031f09090302070506040b09010e130c0c030e030a1a072106090f0218010c02061e041a040f0b0c01151d0105010206070e0415030c12 68
    0x45018800740400035100912280c0d503580b400d100000406803a4460100016803429503858a88c50501d0f892003d86030304580d1350030114041d01140404800601602d0000141c505000c001c0d9016541e46004050401c403480004555098419030041d60040ca203a0490403ca012403145442d440142c1d5034048030300b400780c100070300182e40c0756252034040d50141c01000046210200707100150004030319000340b2501c13200c000f158200d9408031411a61a0b05800c0e00102450a5200074115190760006020000081200308124028086040071940c80e50443e524190320410700417000520042005041141c2d55400c0c40c0341b250f5400206010000c00a000d20480140100e640b06142d07207042e6441c601410905145030400341442400409080851600c604400c20341000d104841e0b918080c4100716a52200100b40150302600c618a0040480010440d944041440c51044510380c882c40c40520a01091100518040900400043c0e6039003000c000214039894000c010310b0015601c800070740242c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 845624847 1250 845623597 845623601
    0xf1a0a14041202100e010507020409050703140601090b03070b25080307090503011401120201080901060b0a09030312050609270f1e010902010c080d0e1617010207020a090e12070609020103 82
    0x5048130a020464507588800c2e80c0c030200310b803179855040c0d40c04110481d00345042880c1407400d8000600002003c06210280880042c0c103a048402e00d840511200e403080341070540700d814038056004211410070400311400064881440250703060380720001d08400c503440d40ea12503041560302c0000184010020091484c1c00d0041031500810100500c205500d00050460401d861040c000e060103030b041e0004810700d402307600c0100241401c81c0816514907030b1460003051301100e40021404202061080b547c85001c40c8511842698040c261a100361140f040c40b18843e6403c88490210003130100310f04080407028444408034444c000000c18208103084e0070700480112140851685030701d0040b4403400760f80e0116607074101a40003140d03207568000d01e08040d8003800650070100d502d40708000001c018a8180e8031038000315000f41f032419404e038200030141400d0f449400006940b043c1ca03010103103c0810a0351101100380d0301d140c2191480072116003614065000440143c50311952404807034290350f094 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 845626097 1250 845624847 845624869
    0x6020405010f0806030304050d08130e010f092c0a0218270d0521090c0901090b0603160504050a0906030203101b18050a030503030108070f1a0a14041202 67
    0x1428443e01d20300e0041d0219549004511401d885564100000e0092060f444201c076040c500c1c01c40407034000e030b4503a0001d4628080a01c1850000c03c0d07a00b0f80000c3d02d40d114843e02a0f0b045012010f450360785044101104c26a0a0403507964483c0141560980141d0342d0000700ea12031000c3d032130100a00d140200c15a41c00801c12500040da21159003c070106080c00424002109059820030645a5948410400ca10214412000b801007000303000d2051007000011a000300b00012181c021460703885054810a9500ca80801c60f0019824404502040d4030701c010704d00c800e85c0610f081418155102c00048840d051a03002c0c12131a075031502d0a00940c10b007848410001c03121443d090020380c01c41c07208038644c080f10003241c0082180020790340c4030f02d0410744444001000c0003030101004685a0420507100c3e4400c0c803691480d0300c0f0f1060002085e1000c03154410880d0700000c66508a03041c4030a40c1115030b40700e03002440820803100c201131007129113038002e040505407290b50314904903420320502035403100d9 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 845627347 1250 845626097 845626127
    0x905010f03020604030f0c0506070b040209071b0f06140c270f040f06092904062904080d0f080907050f040b0d06020a030510060516060e030d06030602040501 69
    0x155440510250322040300704d400716903103e4001c200140081c10002c441004035000305500280c0022340c0c00c140f01c00a01510700983c000c55442c81161107a02c0281c942d13003041803185d203010100b0304044001c80c000c1c1e508881d265029002c0421071940c110008510f11303c04840450103020f0224181603141817422083d041c250544a00600c00f03000d540001d80c08070f2130041402e118584a20b80004816100e4118070010300750003e00740000341d101181c84101d040c1200740040c00c90410b80340944185018064482151403101d5000347c4505e081e91651000c254201003010303044020000000d00240820001e46c044c981d80c1e039001581e9244542c02400d50340050140201c960150106200964464405100c80c42045600103800c64084001c101c040041e1383c401f0f0304113803001c01e003504400e400d500400d00c40c0055181c0e1140903505d0b0041900c140c0207600d4417138240c4001450550011300c150380004204104041141d0510200003440400d88885420848400782c0210b0108955600000703002171010b0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 845628597 1250 845627347 845627369
    0x109140f0d050d0f150305010c140306060a030c2d031409061501030e0a0c0905010512060a0b010c02060705100b121c0302040b041d0c19080c04090603030306090501 72
    0x10070000003803103802415100d10f42030b607442d691081d60003510350007100c0c0b1180c050300031504143d690030458020301480c0031001c089040346845034101543e541c21207100d4a0010602d600740089841d0482c003c01510740b0020a101c02014000201000c0820441d06420040c1a8590724074051748020f0075514400c207005011107070b420030701c00720080101e01240c0c008420444030b41c01c400300a004030080d00300191808030781d0140e18080002d105c1501d070305105070f40c000c106c1440282d0740c6d6010310281e00c0010203210b20680100d0007080d903401640d040451800d0052501145100041c1c00140465011100c11141507226600f08031140034540503050480800721210030a800146000340d4994410801040e11091700240840d280c50103541610007801100380410380f0f0b16240c1d4000b02c405500c20005ccc1c2e40e26844840051340300059481261741d0f10b941e0060031540100d04e41000d90b0180c0c0e010304990909401844003280b02c101d12f200e03580041d40203540104000e480d080c2d503c000c6800603001099110 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 845629847 1250 845628597 845628613
    0x1090c050c0d14041706040218040b040807051e0c090a0b060702040f2a02070e010f0e060d060c030b04050606030907230303120105010f110601060c140109140f 70
    0x1030108050b462040d40f81001c1d50089040d2072803900700c3c0305a82012040102d41840142100c00c0003035100d104520a6417800b01c04840940840408003007118000c266561080c000340005513004050107005100341c0c2121b588400c160800c150700003480188403c0c5901c03510440342d0501d06241403d82040d658034007004144a00c5002c5209449050800781c06151140504010b80c51140d0100010350f60140b03003a0254503200d40f81103002c40b1100041001440b817420702103501c11205c0301c080e040f213846841a085045c5031248814a540b4020308560b801050403050f0b0002c078090380580c1000309043d9500082055802d030411040700c8002d0000c82c003528080c41000181c500004004080e42d110328514140740a40001841300044803000064240c00302203860004004400301075130580e60242c80300c412808002c1000c498020b0300c4403052030594401c000401c980c4d40214072504065014025074120400c0d1511480c2c05e545855a085603840b061448040c2444024480041120102c40c0901060 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 845631097 1250 845629847 845629867
    0x1150e04050708061507050d0c02130b0a050d0501200309071737030c03030509010203160e03031608040501110604050a03030515120c030c0102030f03040b27030301090c05 75
    0x151030084c0514001c0003039400c0749070351005e0b65040c0d41c07109620000b00c90b00c1090b0400010402802d1007001c90180c59000030000707201205008048407203601a002c21812440e0004001e018145100d0644481d5a601c02e01016214840c42022a0200030056680c0e00d0900030252860220b080d4021007a030100d0250f0a03138203900100c0c07503440c0e0801180303c60504102c03056900074203008050300c845101f101e640b0070004058000c0146a0100e01039101041195554040c041c241d1000312203201c0404600c500d15a445405245480708074003001d8200d1b82080346c0c00402c41d01d00c51030300b0000d640810020504005075070307000718a1403c480596000e02200e040c1a0750f455682e0b00c03603900040505454000045040e100006414401300c8000c107503990390820070b00000c0d200c64220407000c1c000d01868142c1406540008116036544a0f40648103155070342c1c58484d0400c0b174a0140400d20038000b550300044100e0300b5400b15111011880000c0c650b654940040c400444014400d41c40901c0014021102c44d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 845632347 1250 845631097 845631107
    0x5011401140412140307050f0606090118090309090222080d080a0b0102030702151308070501230702060a09080706030605060406050307020f030a030e1e061801110301150e040507 78
    0x200d50705043c024040240781d01e451000d440c030345100900140300210301e12050010000e040120314928606960301c0b51140c206000d00c1810902669080e02d208100c450008191640305081c454001e01c0c040940a440702c8072070b4141e034001036101c02240c5d01004d09089505110307100c40001c03c4a43d0041c4609401e40340050030500e0000e1603c004c555561a03101071a0340240220341c078841e401812a200d04005103140451504210881c40540c1c0600d07501041a010001d203610a42c3d0050b1904902020401c03100d01184007a0741071081c070740c00c09101c00c80c0180c40c2e247c068003e110b401c0d11003d084a013054a954a00071880c1d018008060900c10700f00a9900c880e01110191401e40c9000d0b6581d541da001c0580c0781c00c042d88450f100d54400054130080c01a41580510b000000ca035041d140741d6803a61840e49000c801c4001101003513040840443d1104180a9a828900000e01d0002c21106044140450660426032121a060240410038010241c0c03000040003090001c843c104944d003420300c0c0040c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 845633597 1250 845632347 845632349
    0xd08090319050c0a0209071706030114062407060501150c0317070e12011a0409021806010917010c030f02070c03110109030507031a0f01060c08070212010c03050114011404 75
    0xb401030009518852100034000d14140742d801511910882c10032400090050b15406449000d030350107080440c0591038180101f4501803890713686100c4c0c903150a401c0201c030300310860115030314883c6030100c4810811f0120140c100c16015141c002003a62500000844162030351406004004132400c10398000307500003500e910b528002840d050f01560362564203441c4200080305d041d5111402503104070b200b420540262080c042001ca1715010401c170601840140c895401000798000c06801e86200119070400c410b941c003100501d003030695669184280d181e0200303003079080c007044e9449000107101c1503014001d4030702030b0b180c4140851500c40380e80c68010403010769002c001e28110341d075642d40c1096849180018091074002054507000b6a0f2441c202030000f400d11180704149901900084841034041c42e414101c82d403d4803a22001c040d5541c030811a03a0010340202d03407281442c0c0b085901c01e82c007441108013132000342d02c000840d941001502c0c5907408c4480c120904100b0000aa0000c9a6111007958 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 845634847 1250 845633597 845633647
    0xf0d051b0105132d171204060b030714010e090402030120030601140924091c020307170613240b011e0504180209030f0709060506191d120d080903 64
    0x20f001d26a5011120031039106c0c500c05070401118181c20300c03051003681d038814030011504804549840c0c1e80c966101e81004040310340103020a4034000503610604242d1005035001e44010000510819014015003000b121080d00007a603c9012017007014a5801c00c0380103440e01944a0403d007042e28183c0000c00c1d000303808461040b01c013481114080c000c150b02040d00c00c0707110003c004400f00c117000000c401e040071418500b0f1303200388900c503000a0452420640f0500e01d01c0d404001d0155569000c200800f04010008111200c020324040d02c904d02403551050704140f030806070f0100702e480c0120001491106820219502d144115103000c07902500841100d0032107181010040e00005038090100090259500c01d030380500450b072208803510170210f110410349005203010003420b5124020302440b40540e20b00c0c401e84203580300c1a10321142c052210f4024400034900020408901c50700401d40c40010b11400e0021b0b41e20142400507444d400c0611160300002080c01903040c0305400100c46908000c1d88450307 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 845636097 1250 845634847 845634863
    0x9232124060a03020f280b0c01110f1e04120c090507020d080a0b010908100605090a112710080108151003020f0604080d0815030f0d051b0105132d 64
    0x282c041c0300b041d0032117206c49843c680c54907810140d450144c0c183c03a40c410305400300d0552802c440c508c080341082003540e1aa0f903c15174600c1c10003096150b4040c403441c185030191450311003440300080a001085035074000c0b0f0f106082c03e6126510300366221043c2e4102500b2542550071000c80c01340e03480d0b03010340c000b54404405200400c081d6a020300586d8100c5658102c1c81860045007082d0041c1904d50304610111107013940d40340345569440c00c429044642104a940082c81c080042481801c0800a0081c50058000c0410310103200040040c1c20b0101c1c11038503001052854004120000c0d043c072083c00c80160381d080c812002d2909002c44400740d00076000091007411840d546409588a450031344014200c680100c2d18242000e89014184003002c442c0d01042c800d000c6030740c42d00c50a003c580441400e01ca00020512203842800580d11504455100c0c0c4090003a1100d200102c07000340142030041800b81d401d40c0300554907040c00d041c20440e01c5803080c2c403c0b0400300000344c00401486504070241e004011 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 845637347 1250 845636097 845636119
    0x703111b1e130504050c0306040b01141f0c0204051b07120507050a030201051f0e180c030d030609060f0323100c0f09232124060a03020f 60
    0x5900e01d50310a18802942110030300603144030108065016038000ca0180c81103030300084005040542e900e0007254028000303d40c0d440100191340b000d40d00e858895000038003410050050701e6030450019a03007089540010320744492581075003418442c094002c0310314045a13401c0800a1518a0700b44103400008081d0a42c000c000901c0510030402c1d1002c1340c1c0d01000350368402d5110f0800038080c1800341c0b20001a00d550021003154840140c003550304868030756000307010036590294a4402c0d5100c00302c444044c0e0040c0754000c0c40c159003c0c4038010905013240c80025800d13050005910840f42d46800c1404066142201400402c0940041007501c02c0150340340321242402c1800141011540e11b10646014103101e60844032a03003000340b0000c10009507542d064095a1007401e038500c0700320b441014948480c860522882420052400003004218082c048000d00c181d03003e40345000c100c1501150340e950240d000c2c4100d6964444041d81080b0111881c41c0c00a0130354001500e058101d12a45108100e0461 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 845638597 1250 845637347 845637379
    0x60b18060c031b0f011116061a03070f170c18040c030204060f0305060a052202120d050403020a060203030615071a010803030603240a020703050c01020408030703111b 73
    0xb1034428440f40b1205403032040320051407513690101c0030404115075080c1385580381d0380d008074000d03200d0609004650340c128606548a07000207203080119119a01034111000d1032945081042c0e00052101c00b91100c4118500152040c141c1400c115911054000c0c94552405a07602d015903a141e0345c1500506140d40c0303036848c00d200d01c0c2c0350340d6000942240c01c1010004e500710000c4500400c40340900296030044c2d48642c0178104450007200e502d07141d190780140802c1600c10411802c44180c3c0301510359481d01e18084c050a152241e0344603040d000a500150a10460810304854001080c144c0019420350400c580000c080701000040039050b12404503c00c0d0a01c00703030f42d0200344000030802e1040c00030750f1120041502c82d402142c401e8024030410210300d5021081c840c00e008041c405030324154240c1c8582c0410b20286d4090380c003d40c10002c2c18000126030f1002031000b4030007400c14800a51340c5400c6803401800700c60002d100c120f40b641085517400c11140c54800e445d036030904200d5000710002c0341d0348 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 845639847 1250 845638597 845638603
    0x2070b0909010b0306010c0f0b0709060c0b041106072102120705060c03070c080c0a0605010b0c10020702030f1b041a061c2c1e030a0e030a1e06060b18060c 68
    0x7d0001d03008250695004080c025030305803403800345109a8072103121689500301607a106c06040001486c00c0b00d0600042c011511000c64050700381d10080445107440740c2c40d03c0f41ca000521114640320b016500000611400e42c040060070820590010010b080a81030344910351101300c02000e00c42040e000000003004140701303d011201150f40301c04816260b8030281501c80e501e400c6402d00300e0b0610b14144c0085002011401541c1c41c040000005000b207118030000f11700030b5044510126011b104142819581c02014072048002852240080500000890400c0151828195048104009007001740076940390101201c440c03071002210528030a400426841c000c0c034001d42268100914a003072311455411903041c021702000c1100c2100c6880301c0425540c41540c0600c8000ea0303256100b01f0442803068002c41300701640d0903004064849440072611407080c0c01e05d21040044242005065000030801c00340f041c500a880c0050013a41480a901141c0c07180403003242c00355100304404104644064010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 845641097 1250 845639847 845639867
    0x17010c170415020406020610090e07090b06090d050d020d030212070c0f0c090c021b2b05010603060b01112d0c060721030b0a0e0c0c0d0203090102070b0909010b030601 73
    0x4000115911356440c00020340320b036002d503003811009403240400103d80d40640114460410210060140d0a01e000b040c10300410001d807041c2d070003950500c50580e5969441c601c0b000580d000d05c0c040c01008101d4040282018020f4403044281441031100500d5806400d040d658064205d0409040b030005604122a40c0c9031101c2e0001c098905880f004911000c44d9007141c3e5041c5165000c58000c259515000320200d03c0c901a0650413010300ea09101c8c4603d0518400c1902071000c10803407c0100040d04d8450a4480a41094429039240c4140d0382c880d50384101e0720000700e40700d040501a0842241901c001c0d040e8140c1c5045444130b079620b0b40341c02500f03040c0200c18100c840180040e81ea48103070b1038044540020b010300c003c01c03600003800701007016000c2e005141140c2e00040480080300d050582100d98000e01800202d0b9040301809070f18503101d400c1182006182e000c1d0002e5448a000c000020714005158004000f00c0405108a103420f8541000e580e040d2540c0306009616980c400300101e402c1c03048 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 845642347 1250 845641097 845641133
    0x90b072c0f0d050d090e15040510030503030a0b1e010801060f030b09090d080705030c0301030204181e050d09120803090c09010909061a030d0305070212070c17010c1704 74
    0x30300d0704842c0400000080e0100801c426882e00e41d00740e40daa110601e01050204d40c100013030010b0340d4880307219241942c080d661042002c1200c5d41e482d03480342c03582d030301c0c68100f20f030056120350341e07201882070351700d85030111403a14000810400152a4a600001c0c000141071213000e00703200001d1502442240680c00c0782c203040c1b20181500d40c02e841d20b01121944c1712400c042c000b0104140b400800c404030712910403a07200c3d009415030356185910315428800204030410b00c600858510391028000105825030705080200c14040e8001c803103609052070703403c1402c1c0c64903039418881035402c01c007c6090800011500c260b04a98000c1e100e03541c9405060404641c400e8440c0d001d0700041c004100405030303500c81c518044c002c00c800c2000c51092098218025180c1c80b106505902c000448ea104e18465044194032214a1055035003414180644003416004200d044501992440d806d203c0031403008002d500210070038001b4881b0701c20140015107002860703a4500700184280000409202c1d1110746074007560f607 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 845643597 1250 845642347 845642359
    0x30e010c030e1003060923070e03071706100506131208040801050103031e031104180b041d060c040501080414030403080f1206030f03030c0d0608010609090b072c0f 72
    0x403d01402002007000d4012001024a4541c80103504c0008044034180004038000380d00c03c0e6240c801090750041100c11210364144145180481d01c602040c048000348070991004161500b01901c001c102404c0d181c1119000d241d007800000e072a45c00104584084074580b0301a03090b0722000c1c0c2030111042c49a500107421541c00d02d400001090307444040b204000c014804c4000301040c08075411402e440c0b040c00b44064a0000f03010500c20041c0204141c4c0e40c04000f07940c000b900401c640045002d841090018203a100c03501c40040042a60512002d684802804c8280c0e1031b060a00c0d0000e4221407018002404048140c000f03441642d47c104221009190419510740c1c890081c1410004a540042c1000c070004072240042201030030700140301c0b01d032050008040c6040d941c481d0509009034120b4001e5084540c0c40e4200042c00c1e00c028852030340506480f0001080c1882c950403c00d4244c00068070368002c02c0300b01c2050070440e483c0e28aa1019500100b100f01318902100000648800104491540e101d8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 845644847 1250 845643597 845643619
    0x6171320060705070e0f090d080f070c0c0e07021e03030115050d050f0a0e031e03060a0302130c031d150a091b050a230f03160303110613030e010c030e 66
    0x1170440792849440700000385d180503130328203030800d8403650b0384681c50002c51861008504c4111001943c542d100115203000561501a030300c8a904149655101035502108031080c02041d81c0c2c1444451803003030035030940c0205a600003840030340e00c6c4014482c0f43d0523015519000c50903a80728000320b8141041c19007051019092950310041c00c40000d83c2c250400354502411101c40180202c291007207043e8190445402c0865413030481c000c2d0b440100219800305040707101200582d24110f01c01d516420700240022510030907034010301103560b44500044c0c07e42c50b402030003038001400510b0003200c500c0361400c0c030700a4130b6583c20f18001d4000c0010080281c085100b20803021003081107008110364080707442da1209030b5101d04108840b00510b1107002031141c00c1002558a04107159050046d0070041c0840700f008200e5018142c4128698204a0029007041d0601064030410071403250005446000140c598046035000b4215500b42000681405241003069007803600400176545801d0300504411a85 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 845646097 1250 845644847 845644859
    0x7030b07020d1701030201020d030915020c0610081c140f0f0a08010f0b040e0408390606100305070e1c0204060f27020c03040617132006070507 63
    0x5500c2c080145400994442204000c18101e031000074101c1c0d0301038018200e5140485400c8010b001042002d842083d5065507101c2d60b1205840141409140000038101904102003040079908003540112190b500440d0307000b5800c856048030301c0c0c90345c12034203240340f16210649100c0000d025508079040c0f00f1001040b1422102c0e0300b90000c01c1498240d81d0f40401c80c1e0788404c614151108030780160808148248030a005000c0044100c50b040303801008500d040c4110101c11a4007140b0491034200700240010110441c04080f074001e8a00c189a030015000501d080d40101c1d010600d0524540101030b20780707011544c500d000740100c0024034006030000b11210683c5000034079803140c518023280a140740c0180090058074038030600080e96030340039030000c0000e591404896102c2c0c0001c0312001d041c2e4200301d07840c1000420002480200b00581f281d415214050803c001c100c10001c02040011481120400018085000b04644006111240703201900340a021450b54052004020484d2184040225031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 845647347 1250 845646097 845646103
    0x240301050f011d010f0510020c130209121c050304030e031c0f020105040206040306150f12170702010905010815030601030503030603060c190302070f020301230a0e0703020d020307030b0702 83
    0x10780300b600b11283c003000c80120121281490904ca90510101c07008001d00c510701e4004034440c0fa4a500344125034801130740c08006080500b4004001c0300261380014440c0050503d40b054461182166001c0e0010a280c420741e000c680d044441c04108201c07002000408050040845411160700a011250500076005910580b2000c82c02c0300d4010a5004415809051050250398821390327028040c942446d01e55502d4001038208180d00b13a507105513050340420940d441c0c4000100a04080c1780d840e100d000d9500f81900c207594843c80440035942c080101c000540d8101d80301400b140c40a1030324100c00d60302c5c0100c014501e010102a142d0500890000000380100000503600826080b0240d80a5480300360340401c6d079210b000094045500e8010004007a14043e0307000e810500d00a0388000d552041d6540001d0840e0300d00640642401c100e0150804001c51800131035a2240e0940d808105040982c4030042d680e02d501d110083c4900b403400f0003007045480a01c4103000440e0310601402080c10050030184d1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 845648597 1250 845647347 845647349
    0x1b0b03040b24030709050c1902030915030c2a0a0602120f04030c060209130c0f030b060340031e0201020403241b0c1a070503240301050f01 61
    0xb24100b00e220920522078a2981900c1036810090092043d1031900340d0703031405000010600110303a80d00340a1200c520918014803246540e0380d9020390342d214080001c004d180c080d40003800d010301b03005000b00901000200d00b1110400d1654009100c1210390307c81c0401c01000c945130101603070040d20510800c1010580151400200000758007425139582a0304807040c01d402c590160000b452101070a000c50010ba00800c107002019202d60390b100b0044c0254000d880c0000c480d040000c1c3d241c0e4a9801541e03051091400ac507404498003440d60400a0f04a0521045510900800b06650600f02c0c204185400300c11032120303030403c9000728042d117410041c0000300410403502040c0c1d40560310440c0c01d0320603c00c4070140ca40c8010f1240303050040d00440d925115a443d10001c00f0313643d42c9400e1a0416280800707000010959941d141c0c0465030b85400444090350490507901c8041c4601402031664001007580e502c080900900007840c0002c1c01c0040c482e6404d0f25046425510b404180401c03580900d0b8003074 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 845649847 1250 845648597 845648611
    0x40b030a082d09030d0f030608060c0a020c040e100e0c120114070c0f03080c090a180b06040b0f2802100b060304020a03020f0402070b0a0614010504060c1b0b03040b 72
    0x350b036021003002040394910504404551640161000240e45400fa070100c0910046510380099050784035003901c0e25004040e91020340000000c2415142107504006445070181d043d603041c04140a500d81d56982e80300961040b82159407109401110260104442c40c11907070f00801040d90a004140c4841c003c224076800c01d0300001000d000030743c00a01529080c0d400590014000244c00c1d4940c400303c0d0f0854011703082e98241d42042140d044566034222400015020f2107140407500c3e031581490401b102c10032281d5900680040c0010409518018251840d1850002010341d4030051004c20820000036000c2200f11009103900d03114280e5400105000460a0400200074030440e100400c80e50340011580203500c07001075602480141044500b55070400d20140c40036040802545d16698800000c440c501041682c9160410101d111700410061681d801c1c01c089260a040241c01054400d40302d501909018029000e603020f180380300c105100409003240710340d03103a04091809011014007079440d8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 845651097 1250 845649847 845649907
    0x121002130e01120c140d0204021b010615080a05071b05060a0f0e031605010b130b09062407020d082703010605031009051603050706030c0815040b030a08 67
    0x4503c000701107030025003c40e04290001051443c203103981d42400320004480d60090070400c038080058840e80041d01c14551040d404c0b0744c041c20309940c49402c5a02c00d9010803420b0308038455030b070101e9811403a655007164001c1c00115590356200d40541d81c109103d44005081d41a0203514028080c0110b1442d000e1440341c071043c0458440b5400c841e003035a80d0680300a03120f820401003105d044500d415450003244c4242e00214101041c240043c0c4100100c0c1c0c1440ea0642c2c64451860700c9117010050706034000d07130454205e107465200d0b9a00e0306a8080120a1001c1950300060700d0047d03560700c07800030402d00d502c100d1256a0390442d2550203250f00780072014854920b40726074041c60624044c041e400a441014000304403012000b221400075049180058495000e00f2541008112404058201540c02840100001854000c0041c200c50b03c1d5201d07407041101403401c1c00b100140180741045000022503001c515810301d0000039080c403101001c010864100007a051212409144a61100c81d81483d40 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 845652347 1250 845651097 845651099
    0x12110307052a15090f070b0a0503100b0f0903010612030e1c0f111e15070f02130c111504080304031101050f090c040e0303070819050108061504090c05121002130e01 72
    0x42a03901c146a00a901c407005081c031440a00c236101e100516031107204503070040e400c01e5840750750141503800803039040c000440005940d86141000d006d40c1c00201000c0c040303141c6180e86078400501d606501084030740300d4840b00c084191070040810704d52401640156209030001c1c850b00d400c280381c446180103940900d0502420380d608121843e4a4188000e02070401111080b031003c1c1882940e0001100f114000315411024026807903842c1d468402c015507203800140c0c002604806080c041c401000c074505030b40300300e8525411341c2003001641e070040d074010300b029125119403600340d480480003003060000750329017000c220f0074100c409503040c0205120019540a21000d0061001396404440c04a4240e441040410b01c00d6100314141a404840c082c8100c4400303140d00064819601e003a4010440c83e8000c8c1c0510003501001c6000c00540b40d0121010098104580d90341995482d15115041c818140d81010b08030194040c4080c04100340c03410411503030f8a001c5558013503001c130540142903800c00741b000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 845653597 1250 845652347 845652373
    0xc0a2604062307030b0102071a131212053f180606130b031009020a0504021c0e0304050d140618070b09010507080a12110307052a1509 59
    0x110b044403840311489141e4480d65424401d9016162103e000d60441c41203003030004214000d0f0f05040c0021030050101940c5030b01c10300d80e904801d00729404c01d080003003004d10303803c0010740c107146100c44214850800903299130301c980d20040036540401160901e20703040d03000e00300a191100c541086d281e444e401c520300c894071803041403010035800c1041c918544d844540410030b107103070050240c024109100c1003c1000c5d8140030100e42013042120300a58001d0b10f80d41c0d500114500001d10802034141942c0460402c0c05000390903601c4450390564030080f43d41c0d10390f401301c0c10105004540241c00040c101222052640ca850803c0d20080d035903840790b60052401094450140180a4041102000083c90b44504150b0364400a034041541541800300070440c000000311b485000e407030050303080d40701c4400845204400000390f402c000038605d41060100308010a82d9000b600780d0750902510b90398000e0900c100050004c0040d40504080c50f5881240800501c0451441c2900c1c4104541d005607050f46010f20 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 845654847 1250 845653597 845653631
    0x50112120f022d03070804171b1c020423060402130317040f15120c05160203010f0207080a1e0909050a0b1f0905090105090c0a260406 59
    0x4449000160000307014100081c0358940c0828040c200360128043c181810b448462456215000c201c94040c00441c1c208807080c102c4060741c7c1c9480d4440d0240001c00000745000011024a0640ca40f00f40701440300b030b4000c86045081c03060000da000d80304101c42d5038524525070111613261202110046a82c00107090390406000350b070fa8540550501d8002c1078110f81c0d5003007520458410b409020802800001070038840200200024a10080340209440400400500840c5403003031342c0406900f099010403081d035220080b50340da03a10418241c0310755100740c0300003805040d00c0212034000d0750000c9000d109100120f0007c020b4000c154480c00e10161050928840c0303985608910008130704182c0d402c2004000c207821240d449481d00d0800213080d41030500041680d124848088418503400300e900c15501d4000746003c0280c04200c40b40301456150a0001d010000c006044095420010400c018202d004203240070440054055644a4030030f4a5600d210b014411181510201d0800051402c02c00003a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 845656097 1250 845654847 845654867
    0x705041d060601081b1909120c0b030603011503111f120207030c020301091506080102091311041a21070c0f021f091409130b060a03020405011212 64
    0x900090140d99441d0710042d40e240b28001d28043d071405030389604d03817103003100c1100a1000e032665848a42810b20301d5807001300f80c030b1040d81064500c0100c0c2d010910208020300384807002c0b141035480321a500e64402c4003280c09042240140c03242c0d801c2c030100c00b00410942c905400d40303d4505480d4100c00402c4600082100e110500d00da00c0401c00c401c5260942c0d42441c1c00812000e8000d0078042c1d02002c0ea07130f02103030846109880c103542900f07604500c0d03c00240b1600400c401404254025800d0481040020b0306100c001d072034034015643d0f07404005110100d10415030f070040400040700c00041d182c540e445065603211801051780b0210b46050031044502c01a841070103001d01e652482400c0240e6a1007800814001c14280d074028001d03880112103902451001e55014a20b44d24012807078a41007030511036040d00786000780700c1c038081c1f01001210541251021007a9400007820400c136221301012070b1030210741da040070b5081401c00c40040b50001c01c1d0040702070840d03c07400c1134402c0140c060004445210304 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 845657347 1250 845656097 845656151
    0x9040c0e090a091b180c02010c27031b0306060f030309050f030709050108011d06070e0d030e030a03050a2c120c0409061b0207080d080702010b030f070504 68
    0x81c03640070448035200b90380200d500921403506124080d22403816040380e000d40f588540100810300b900303007841c5031090058010380c014600003409008003a45010f0503c445080d0781c08248240c04c031902ca4090351584440e401990483c90b0103880880c414450b4400304503901069510303904100340010002c502c5150101220382540d100c424560424081052000030b0442050b03140c442c0079000300e8420312600c101d50080500000000d25440203c1840c01d21060b580b080fa00d0030f07081002003041140d000641d040020000b1100c80c240145146420b8800c03080002c0140c3d0503102d0880781c6010540c2150040000360410f07218245040a0783c80b070080c041c3e6803480c0955101c0c00e0010001c0060030700401103441c501800083d161248102e5001c20f040b0359100c441614210341700c01001c2509050000001c03080314071440601f011030f0400103000d0b034414240700803404000d12030000034001072007035006065201d001400d4440e050304c14500c496032003015010342031184e4a0b00c2007100702c00000002d84a09000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 845658597 1250 845657347 845657359
    0x1205040b09241b070213022203020d0816120203031009051017010209040f0f05010509131101030b090f07030633021603290906060f060f0f09040c0e 65
    0x80e400c80b606040c03c1d00c8202c0c0c007444400c10310000c4010b0b076800c1c00c100740c4c0c1184040d0060319035901c009083d9050541040304450b01e20348640900260b102c2d0103224110781c0d04440f40b0307030380c507005034500036406480d101c1e01a1001c4240c05d00302c00c1043d8003100440c0a03446d100d03585810107031294034250807194240c80b2740c5000b043c58803003004400c8050b004041110382040c00141480d0380760022405503030316880221110b0303030fa4110f42c0d40f00580c07503c2000d0241c18103581f022114a08122900010401c40341c0251210104028017030142e03120f80c02070410000e02600000749400e00880c00301c0080b20075160302d0f022a0038210041601c80158441c240104442d0294046540460416000003020828540210b00540e00c04441d00407101096000852141115503c504c8070180c49183c0d50144c2041204003159850600201c0b030700009004c3d07004417040780d0f170b00c0b0780c0700b0014001181ba114212980440c80d501050f41c4510301117100117003426580a94080c4030800e50320504554081a100b40d280d8849 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 845659847 1250 845658597 845658601
    0xa080304060e100e18102d060e030a030309020a0f09020c061f0306090507050307060c0605060d030e041e0515120d09182403050d1404151205040b0924 66
    0x300c902100310b80100c0240d0604d4001c544441e81a4800e1f140d0303604021106240e517a0b045800c0a0308800d090003040a0300e4000c400314a080700098440c0d140800280815855414007400e560b2004a40401031001110b0020007540c1e40d0030000203034120b003415001034002d100c0003a01d59101ea1150404000c0206090010360b400c2d0703a03845008020344001a50315124125003c221910200b0411000d40f05546405001c03050701c4c0780000a652000f4592805401075548000c006034000700100e010070b41c03c41d00440d00b40e00030a2528581c9440840341d2200c2c604007824042b0f40c9252250380c071030510b01514100900e01c2d481a602d41c0e01c840c000c1510340003a1000300204000705034280c1c1c0300403586180c50003003007617400d4600e200007411840c4407281c40e030490b1560400410004108060120a103401e00da4840d1070b40005080741c40c001c40c8945030940d04c0790017401055a2050311010ba00c8055000c0404c910300f81802c10300d0002da4101c035201c003a0321400040407001100386000c4030322140c560a54400b03e13 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 845661097 1250 845659847 845659879
    0x20c0402031e10030c0b0f1603020a0c0b0406020c010311090a06120e010b13050403090b030c27131104030b10092301030f14010903030c0e0a0e01030f020a080304060e100e 75
    0x103030b0300c40c030350b03000c9580000c8c02010520340d61080d4900c401e5000390b000308681540d908100c2c00c100710310740c03080c0e0101030100000c0000e26000304000404410900340000d2499140a904085108035204d441e07010f00850800314180e40c000541c00101c0c2580c81e82001100e8542c1d0203603003240c0e2808041680100c003c0f800b50800365070380c0c2109511611a203804401d059a43c11742c408290030941c1e0641c10b07040d001c24401000541c0c1c001341e520412000b09041c074070404060101d802c1c01442101012080d40765005008e03145074210031100110392224041c1501e140c04d00400724102114042c1160719400c00085404105028540d13041c8004c07010005815a487c5030707100104187c88180480c0c1514a40c00480c2c2e00302c0003807040d0a402030081d00c010071095810720b001081e003480c0041e014403c8102400c14440300100c4458075056950200c401c141202c801c4c000a0b6210440c0d81c4200346d18400000c0110314564840e125403075408040d00d0ba00008480018280e81c9010700480030303600121315241c0c0d10f441c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 845662347 1250 845661097 845661119
    0xc03050f090f030601030302060f070806101d0a0305100506040c0519030f110712020f0307170408070803130b160308060409051b030601170d0c03020c0402031e10030c 73
    0x1c0c80d0401804516003561500c042420910240d1044c3e015812001c00c010061a281240640c04180d0780f90100c103514224002914030f0403044440c004001c8400c4010045c10100c603510f107803101000300a121095600d00c1e005954110000d03010051a090102154440c20f1a000352860704040d83c448500305136092000900d02e00c01002c100341010303140d400c005e19000b82441020301c1c28405281159640b209400c1c4003804100b9003011000b1540070035002d40040300048291010250320015a071000b4684100102c640c0c000c0d41c00480240c0070348203002940d40b02c000000d1404a000040040340c69aa40702c000d210345c040d4070010400030320031290303420000b0310604006030310003402000001c0d06080ca4580c20300d05000c0214108100f500c6c8407400c0c929107010402140140300944291348040301c00c0d0000d544030000002d0101c240013804150400701030013030000c4061103c001e0800c54591401500c0e22140440c0405100081a070000c0802c81c1003812509080a4940100c0321000c170a240c0400820 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 845663597 1250 845662347 845662357
    0xa030e07050d1202010f05150405090705010203031f0e28020a05040501210501030c092007020d02120607020d2a021011010501090207060e0a12140403050f0607030c0c03050f 76
    0x3c2155a90865242e15502e240304844c050401455113410989008040c8400c0f90005040c03042154480401001039a900000301c9900c00034403400c146800034402315a81680000317802c0610892101e07410041702c0701041c07011240300762981500201c501d03180e80c5114201d20a072944403001a078100310600c01c2e5401181d4101e04900121a2254902c05501141c003c55000307030003c50301206080c608010107a42d078000c0584900c090f0440e41c2500342c0e021180c5200c0d00c10202e00074001c0e00019011004d565908650140c0c1c0080c140c03e452542c9042800251200101c40e4003801084050076007001042550400c0005411001d914000c1c02c140f030b808014030030040d07841d240c0802485000b0712400d4a401c0c000d0368000d1428a5015841e0905441d2800035544881e0a1a41c0366210007040700104070380402c0007811000a05085607002c0d0340b0700400c10b41d07100e00e0304041c01c03034865412542100480060924402d28859400700140320709410100c8485190710f0740600011002d0202d6940e80148600405d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 845664847 1250 845663597 845663633
    0x606080c0a1d03030d0b0909030a050d090212060a06090612020102031215060a05031614030705030402010c061811300a0606060f030b04050606030a1508120a030e07050d 74
    0x20402c0480b49001925550003400500241e41d160032141d0741c54142541ca040d0060311203806542010000900141070b8000c0a108514954035035000005545400c40c0841c0040d032680152000c0b0310b0910300000107080f440c0f203094102c519003a0005000010311265180096050380918900700401030300d034400050180000c102403119038005600d80d0b5a5400401140300c1545425441c5c1c50b0003880f0340002844419220140400c800a031040611a141182c3d445445820b1040c5c80e038965000484020303054800c000d0180d0f00d001c52811031030b6107007112042801e2155600b10001c1d600d0009202da590300d6158814008800703030020100703001603c808201c0d55415070049031080c9200d40c5442041e0343c0d096001304045507540c80c0350380d61103525024100302c1041c10340d018401340c1000400714580780f10051424043c540e60700400c06451521032204c40040c45010201e4a80d00c10048984441380c0c0318011100100f4036201402e25418401b00743d032001c560b001080f0b40030208058841c5148944a1041c03d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 845666097 1250 845664847 845664887
    0x1802040315020c0c210106050406080a0b13060f0212070c030f140f030f1f0b1801030e0d09080d0c02100f2c0f06030f0c0c010b030a0b09010606080c0a 66
    0x130318280c5510710300f200e020318848110744403101c14550b041c0c211005504554016803c140b03060244000021f4a0200340e9840340301c18089603200700c4003003192510300c0c4000384201e04141c43d04c01901056005010208060402c0c0707001034580c1d40707098601d0714444070000d0128034103510a600041c0030382044018400d81641c82031030405c0e100c150700415403044482c50840385480050018004850036907031100b044d000b021094842c01c05480d0f16883c000d2100941860300c86450b10007a5900c00c3d0040e1180c0084982141c0c0c07141f800d2800600903145501035403e10380b1031a126107454a00c04c0716411034658014006581182d1503034011520350181003481c50030300c1612049010307400c1d64415507407810060101c100c280759520008110b0442605807102e8803e410900600503618061002a41c1200e100c82c06941d42d900840382e4207014040e0301c110f15030f00d8001c0504040500c02e40d800042c2c8520240c800030811a500c0b640140c0d80c0990682d881d0721480390a00068103501d009659048030b0503600501 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 845667347 1250 845666097 845666113
    0x1a1306050907050301151a1e1305031609050c0f1801031104170706050a210e070308030105150a0f080601030f0509210405011223010b041802040315020c 67
    0x845d00759441e240c80180780300030000080200e820304082d4803810500e01443c542c0b92106070400d40d48041e00540400c1c1001400060550b030400342c0e903540b00700502c0b01606a0321b0b0740000040c9030243c4800e80c40b0b005e0361b26041200281410381c6038422600c05600c00c0480a06100d990410814140c04481201341415511240302c182401c50301c020b030000f01030700c3c03403c040640301400b152428600e05a01000500c1014000b1854182c3c02c84814012074650089a00740400d80d40300100203001c4a10280341c40b070140660210174403503010b000314162401507407261801841074004600078840c001500303000900c1c0301c1c1000100d40c030030404203400510516021565152900700001101e03000d484210141c0e002c06042112a45400c0030b05810070500f012141c1828a007100107001500007081d400c5501d0b070340b426041286030b00030203410814030400c018010740d50f844205031031040e40a0300031000d622810381c5007203100c1c001e01c0c0200c50969070320080c101298442c0502210180d01b101030030895501481c04 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 845668597 1250 845667347 845667349
    0x5060402041a0d06080a0c050f0a1512060f0b0306190812091c020121022205120307020319060207062c0703023003040609031a130605090705 62
    0x2410800c1100041a43c0d03540a495884011103c41e54004400364000c0032008022488150341141200c00580348118440804030028184414070b03002010308007400900708503041d80c04082c03a00c00c9109900208015902c884194003800c40c2c5104940d11150b0800004403641030252246648242807640d41100b1070b1150065810308401e410000c13104440410384203c2444c1c0540012191404004100e40303501745a00001c10706980540f4420141c800b1403520054182d030ba0781150a0354010540a841c0d071800e078203581c07003210b6451203650f202d1501121112001c1001004841310258003c004040f40074900c3c2c000d000300d062011056030855400c0c000900800c078940540000501c0f000012186031800c032009030405000044c041c00268014442880182c40d14261309005030395000b014240904922000d000d0300001400512081c000030500040703090300300c10440f0599200c5c5404c042e00400c1e094505e04080300c2207951041d0321238074941c1c01010488a61103a030f00300d0f080e60107683c00103403928 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 845669847 1250 845668597 845668619
    0x4060c020a0c0b030709330c0c080f060108070803090418060f0504030318020108150a1203080f07050f0318010f140405060a0c050a05030601020c0904051510050d03030506040204 78
    0x280c4400000080041001841540141c03600003812420f6402c040c10b10b41e013004003920003900303041c1c1e075031000c4003c0a1003003942c040c0d1254501c0580c007954850ba2540c5030f6034444d444d441c1c001042a403c2c0314cc030001044013000451681c0680d80c069008600b082200fa0401c0040c00c5468070210584070b604d600c60001c641540246107a2242c40c0001042c50700f0f2915005003110f8605c15442c061207561024000142c1e4043c0009821003003961005400c4c590b504000740c040c084ca076000c88030203140006002d04040d00207100a200c0d0150050702c0180c6c1e91204000e84551050360540c00d0064010400107503140860058030404040840000410607110540001181d41d49207052084d40c1d050410001004410811940d11480d0342400b4410300c801103102a00a01801d6a01c0c0e050003008400100310b030b4401c0012004400d402010a070031410030307080003912125a80b12042c8102e5140c400907070341c18810020442202c2014100400403001074600724024200903098a0b80981c0070880011b20000329 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 845671097 1250 845669847 845669849
    0x6010f182c07020c030a061a030105072109170705150c0d060504200c0c030a06090201020d0c03050904020f090910061d0a0506210a0609140f04060c020a0c 68
    0x500100d40e609601c40c1c0d0612085000414040441d8001400031000b40c0340800c4070030409a003c000030034080411800c1640464094452503015032800040100f2203a205d0310902043d528010070031003070b92040201030142e5042440c0580f0080d41e001d0401000350b4a400240303149070043c0b0036200542c012036442e4451240a450780300c02000003040d040542915031081c00300410080300d0401c10600500a802004082021074a006900200da00c0251010034022081503950040c1500c441c1207052400c00000c1003c8481680107118600c05141d059008242040c80941c25880d1141050030020800019600207049040040414451007840f40c03502881075001d83c507064480c4120500f030160040003101e00d4403a1050b1907100c10407000a40e05c0f41100101580c2c0281d8030a0760b6070314110215843e5101021210b0204561b100800c4080e0310766078805001c6d00d80e40c032014001025030680c0100e00e000203a41003a403802500c40450b000451070742c440032002045006a40c0d0b4240d2940710f00e506a409 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 845672347 1250 845671097 845671139
    0x80403030b090901062606061009090c030212130b160306170a03032003010b0a14070308090f0a0b0f0702010b091009060603021c0902060f0409140a0506010f18 70
    0x42c0c0c082807060100d006a10a0f42c85c3c860001c266417806c158103025582c0c00098007213030003004240484900244517080000c0a05144181030104034607031540100250300400c0c040b80c03600f07100740c081074580442c2004c2c81007130f0341c1100c034506050b2a10b580101e400210820303800103050751400000751000c4011640c0703121102ca24050b042121050030041c060b1041c070002c0580c035447c0b0304c00041501d1000010342e410768100605140e1107000c50101a1094101c1540301d80e203843c00440c0c07640815521041481c82a170082c801e6544504440180d140d540d0031013800105004241e200040141900904242c4e20003814400440e0300340074880400d000300005d88c1c010380ca00708403075000d0044404500500d40181800e1904614104030b520300b0321003004070030304419440f1b911800d4050540d03403030b00f090343d8018206060081e0744c4d507600e5540c1001002ca203000f62114548005c001290000c051146d42c0c49035030180c4407044d42d00107600049132103684105011b0031b451000c401c080b2f00c1503406030001c144844 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 845673597 1250 845672347 845672351
    0x90f1b1d06090c04030b0f0c0d02040909062d0e07050d0b04030813030f110f0609071805070504182301030b090c0a0b0a020109080d02071b08060601080403030b090901 73
    0x91407810300c00c000303100030080c010f6810100802c1000500c507442e660f5000c3c000111503c19074541d1120681c140c814a400141c440d1b00220b004642941c5541c45821054401c140c104040b0761214241d03015106081d10918440c1d0440300002c1c210310558200707208070310000060761ba1490315280018541c02c4c1165040d1071400a0404100405801500d0380c0e03004107075801c0324400591309640090110704011100c0c0300304101500174520a180401654a0078400e802c191201880e00c22210b680d1001c0c00c0c414141026900b0011486110b0184103250055005a8840e45454140002c98442240c1d501d0083c0255985500080c04c004010400d030004028403449110f5952460420b03044014014104110b00d800003c17040740c0315914610440e048a25450100c2c0d114840424143d004100c0b403940030300f002e800042c14901c20f15082d8028410144038810202072581380405001c056000c502506810b580604041a101c0d03000d90a042c1d84103219140201d0240300003000700717048003015103072000144c7d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 845674847 1250 845673597 845673601
    0x2250c030b0a05040503040302040b01020109051f1d0c0d031e050304200f09180604080408210f0d0921020d020307020102030702210a12030c03090f1b1d 67
    0x80450a5071582115400409000c141455191282c0328892484001c1c803c0c2d0b50707020300c0300e00b41c1d000b0340120409540010a45040028001580c1103e110bc020403030381c00c603d4003806070701c040d2071885010301d4014544010a4501c840b00280803100740c1c0b640042d400c4c0003a051005204501003800100ac1c1a00c541e5059100d0038240303061b0016140900702282c01007a42c41d0b00d44415200d50882c3c010900088603400300f1502d4420007030f000d01e50b605c280f8004070f000d5042040148140c06000f0022a00d004040b1049401c1c0c0001001c984100940d8881e0b03070b980100f10840c0c0810b0080060903006600c40c200281901c5503684a5840c60b091640704030070341d50b1401501100d143c06104583e4400301c0e50002d5441d00b6042c1e40001d440744208000240b08211110040c034100b1a64a6811480c41e480c1044400140c21400c0121480c0944c140300c4000034141500680e069100b801100f843c00c2d44920340707000055042d0f40315810602c0c42d10854915400c1e01500103104481d011107440700702007a5190705114 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 845676097 1250 845674847 845674853
    0x807050f0312030718090b030307032a0803150a0302060304060c03021303110102070b04120807050a0812040b07091a16080d020a020c0904020a050d080d1506020c150a0302250c03 78
    0x41741294844a203036454220109104c0d2800f0040394429036041c607124428001703a9007400424110003c0104011400701d90800405c03011308004e5008070710081104a40348000c3d402c0000543c21400000d4100c3d41c1840440d000074250b420180141d121801c0142c10100b80c40b60310f20540a03d070340280c030308859403070b0707605400e5806000301c1d40500074103805d26203414100440c550b04080c00f0300c0000e04142d0009081d0382442000d02070741000c41c0e88016803d50b00d01d060717120418540c40540302903480c4541e01010074001c80c0116801c0040b1011030308802021034890740e08403016082003444001e80726001c4420800500c920f0700601b190603001000507101c110448009280c1a04841000c0c0507040300c41c01e00c005070360b800340048103d802c1200c2212207403040740740445060050707440c0039503124200344205600200b0001c80030203035103555088824004106040290500d0342020058120100b0020b84074254405d400a00aa5000302000000d00380c0010b4960b02d00c560401080e0b03003a102d045428010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 845677347 1250 845676097 845676137
    0x90c070b1005011d0112050c09031c080408090f090103150f05040825150b1203030f04061104080a0b01091b02060a090c1203020618070807050f03120307 67
    0x2510031460304401c80e0600c070000e012134032460490300c442030500d81c502155a01c5035510000e504403418003400141032049400301650003958059100307001d200301542000c04004007101030306029694104540e205d54031440c42c258059054107400469640d005403158481540c030328021442480308070002049504c0640844106481d01010300f8240801d02c004504078009480b2060b03071281ca000b20700480041010880c50702c00100501c12100d42c13801480ca44015480a1542d81094940180103000c0300d00f0741d607c030710080b5500811408000081008515164015100b080907103803240d01d0300780c036039841c03074070b080b03251502110400c2e40c0c0d4006010f100700c14007414603a211020b00b050702050740444080d49070000200204074407a42c4041c8035007804a85000b05000341403051003552198200e090003500c880c41120b070703180500c1007040b40000031580004c0c80d10803203400784042c0200750b003004204503486122040b015418486d21055035949144403000718003911481c0c4034004211000495091 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 845678597 1250 845677347 845677351
    0x1030507030b09060405091e0318090c07170c16081204030b010618090c020c0a0509061008060301020c012c0d080c0721090303030501080307020a0e090a02090c070b 72
    0x41010309011103201d40d40c0f0340246050300541301703c0c1d000c20140e4481c15010325012118800d030701081c5048240001000000c001072076080704041c502c00b003912410003409800941a02e8a8181c40001c00c8804045952000746103044008210620714240c0d4078201e03185450070aa1074049010920541041403500030004000503842c000600c40c181495520b0345807840c14144110710a105140402014091100801001030000e05200700042180702200a40e0342c01c0c000e00041c061708e038840b40411145000b4403020b01c00c0360003c1c0051200c000002c0b0440340b0100103481150150340031300144031820002c4c055942c030019102c066141d14901101c5c0040e0000d9031083c201c1040c0c00c690007045407a5400000c0356400241d1340580790b5951242c1c40d048907144060050b030b1070f008074008061924268801d801104803802950148941c0e6240e011041d00c03442000402507018402c48020048242c105416591011130881a40c20902d1143c02003070311700070116180d070041a800a842000c03c4a404030f066 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 845679847 1250 845678597 845678611
    0x20301062a0f02090901150f141e0d0302010f02121e0903071410060807051306051c14030301080a03030507030e46031e0f0305040807081602010305 65
    0x3400c5000d01e51521040802c18100c040c0c001c14210b4000b8841e100c09400900c15500c00081715112030b951110780302090102405090324601e24849e1a101c0c07480c2042c0512030b0507000301140040001031604001d00d5491715441142995200c02c80165903c003039101a10007500388071040c80c4035160503a240b2480c2c0d1048000204000800c03c1849209000002130b01c0c01240e21080800307030700f01009242ea06e02440e540340250302c2418982c0110710300b0b1011808504803042a2900c0307011002d40a00d440076501603010b21900007a454a103d508502911482e0307207040c1c018085d105200e41c000350a14190352091b00111125030000e11144201503061103481e9000c4428582004008050f140306511107061940c503070424104e00e85050740b00c05500003607180102c03070325001074030781c0000301041a075070b1600900660200301c2e56182e060a040980d02c01c0c44507540507645290214940000c143c0c014900540140d480b08800c1c0826000242c100c0b008010542200380c24601d82da04078400141940e40003840e90b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 845681097 1250 845679847 845679917
    0x1801180c05090714090d020f030a21020f03120a0605030a0309031b24020102090604120b0f04170f1c050a1b1205060d0203060c04180c090b0d090602030106 68
    0x1201031404131a003550888103003141c00394900e00c040d000046132000b41102c043d5040c003802100408012816050102803202c81d640c0c8a01d0890300d070002c0e45ca03480750002c806a585c0041100d200d04007940d00c10b182d448a144507001400a8440002c03e14000302510101c020036403000c024402e1007a0700e244a004055003a064804040c04d0007642d545000295000401c40d9480d103d00b101118001e4050750801407016180c541c90301d948200c121001100354905032954111140860300b220000401ba40c070454010000a042c0031490050740101d40c0442800411603800b8400f00c000c20f50503411911008181440c003161600f02412294211840680d550b0315281c0b0b07542c4892101c5c0d03000718500340d82d2030300e240000a03140c0d0741d00b02194950803483c80003540f601501c41084039490030030b0081c0041e00c40c100400c1100881c0241c04a007100c800080c1503022900001c4200494440306000342103281145401082402da0365403000e00740e030800e030005400b0440e084402d810a5186207080c03031a414440c554 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 845682347 1250 845681097 845681117
    0x50607110c150a0507050c1504031725050c04021c05400c0e0f150d0209250509040c0201050411010503100e0a0b1201050601081801180c050907 63
    0x2c03440700c0d00c1001c034241e051250100d000014094140003ca21500c4007801d5203103200043c0c1d110a00580c040c2c001191802d0f007040c68440e040b4280d80581d50b0030204480301000c00714900000c4140102c800b00110740c07070b00c140150700c1c240b91500d00242080b108259440c00c408426001e4400640e84010100c4080246440120500b5052a01044032100c101000c10003910346000c480c4501c490f480c0b1000e442110900000101000d01d01c410b03600c030f140d0110401506407500000110b40020340c0d00000d5000e208005e85502525240181a811070303100000100341c1402441b401e000d524003002e039080456000700358041c2a0505002e003001032641840204810325042da03131250642801c00d070b00da04000b40400001c1101c1040022000903140c140e4880c4982c1c941507403000f02a08903035411174015101060058180c500500070103014940507155060150344004c40d0a03000f0041014040c01c0b5900c1d44540a2035841000d1056802400340800000040c2002d00340103180c04013400074400c02442c015 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 845683453 1106 845682347 845682379
    0x10f18050d050c2d01050901060501021c02061303030618090c0902030702100b061902160806131b050402030a090c08010b01020309041503050607110c 66
    0x4441110750741075001c0b1914000c41e1600c88040d48004000c0f4000c02010b000d8401111000114800b402a0311400500752902a91031081c030743d5440009201c5541e040c0508003040c081c1110056840041d103000a6580c80f00038840140c04410040c2d1004061183d0441c10082018401064005907010b0040c0c0c014856030b08112150410000001805a1300707009a91050440e82c000e0107025400d80d8008020341a807100e0b10783d10510070400c20707559035440d0010550fa0b008544c01400141d003802c401c400503424641060006134068020804e080c10700b010b0030b80e203665009004500003200044040200102900656030090000c01048040038482d40141c0309280111006003407a55600103141c200c502a41005006804c20880c1218900b81a00301444600b00d100440480301d91384e4030303032a040c40000c0d00c4400000b00c2c003034a1000380f54010040088000400c0b00c441c1c0044000603 = true := by decide +kernel

theorem cover : BRFrame.Cov 845503597 845683453 := by
  have h0 := BRFrame.cov_init 845503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 845503597 ≤ n) (h2 : n < 845683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
