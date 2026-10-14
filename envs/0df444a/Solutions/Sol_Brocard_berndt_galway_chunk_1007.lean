-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1007
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:47:59.24396+00:00
-- url     : https://prove2.me/submissions/04661ea1-a644-4bc3-956d-581f29368885

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 180935251 ≤ n < 181115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 180936501 1250 180935251 180935299
    0x4060b18040209030a030305090d1e031e0504030f0914030a020609060405090103050f07060503010e0601111002031e09150402060d09080d0e0105090f0705010c02060904050907030201121a 82
    0xa00502285c83e605040e0a001b40145030030f0b50b04030340c640207001600300c902d031042e080b043c42811460584004020b5003481600100343c3d11000c131021400002601100400e81c0c0714040c8210b0082c0c039207242e2085500c01c01884881e05400c502032041c10404102126100010856071060313040e41c0091fa605d4118000031500c0c0900d03402183e0043d0144004001c000d404a5200c0002e0b01c00e2017120301040d240c1d081610640824003030040b01c03802c10000680c61350321648002160080200543c0d210415128040303059900407554820300c1d0080310080f07108441000d0b5410347c008150b00150441d4403440c1c05401c2482c1e0007400c06480303000d0204100100840f540d11224100354416820355a81c000c1c608098082c10400c00c10300055468000001c1d050b910224194424240810140c54564184401511032505c50202660080340521055000e47c881c2c0c49442d0160350b00710020203541d4503600c0010049488194031038001c82c2460480381d6954016a80b001c0a000b0803541a41d0511740b80d02e41001d481 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 180937751 1250 180936501 180936517
    0x20d09080c100908010e0d0f050406081b0c1515010503010308070308060a0b070b1015091701021c020403050d18050405040204240e07020c060409050c090307090e070504060b180402 79
    0x541b074001c205403824000149083d0b00c6d94661960040b48680900a45050046200d00070200d000000010040a245075200c45000303410310300c1506080c68144507514150b84440f642511a0000051001c0000c0e0210103120300c10091910f40d10355130466884416500036050002d0a10420501280090340e03019007100243c1b00144125441b40c2c00d0703003000032004000b40c0f400508020041008905400380c2e02502c0c40c081110340b241490f1742e14240d254007a0b580d100c2203440e815542480801e030300448a2144c160001d80c2001d003d038a95085041090400004003610400d10801324000c0c0c0e0361010302c000b00800c88004540026955440380042006001030b01005084008ac40000c1c06117034070840705290944041a00440103580d40320710590355060780c1030105602c0500be1000700300201154200c0342d404030007224800e00b40360101d070109182810f0b81d00710001d1151183c0b680aa1040c08204240091500716001d0084501d0010b03861000e1003064005c1e0320f030422266001c03889403110b804840c84c0c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 180939001 1250 180937751 180937753
    0x506130e07020109060b1518041512120e09010b210403110c0f060f0306041b02030c101a0f04140a0204080106090504050715021207080a020d09080c100908 68
    0x50314098030002e008044040c000c071200b614014001040f801c0c2a03000b03600d18064400031f035207050304d04a0780d4160441080348aa90080d201d0186d01e04a143d601c424100030007010072410020314562170710011030201d902c00c0000300020312003514901ea83e019005411035040c000c2da9943e514201c411103a9200300540948641c030800420300c4205039111108142d507021880c15240d074050820204008004144041070340b10905010f0200d02d24101d00040d41c0009004000281c400c0043d80380c0900501703058000790245e0004107000300c0e26803007846481058414440208840c0d00500074070020701101d81c5141e0f0084111000c0300340142c8869200c0300012404810511086c035004443c40b02940c4507006107111035003040d000042142c5070f070145030b0043d58060007a110a40c180005004080c0d07800558208500c03550b1103075043c030406d502c010890039001d150025a1404203600191070189480c24940030440f00c100d04112034840400c00041442c02102e10001c225150304088a000400e50401002 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 180940251 1250 180939001 180939029
    0x308090703120504050f090105090c180a0602010e100c080a11090301050c040501110106050a030803100b030a0b010e060705062205120a0e15090609010c06020a0f11010204030c050613 80
    0xa82e070b412501a0084032411101c41803445206010b01c40c62090a11402e9006480c0e180441e4000c03104d00c026003000c541c1151214141412079002605040180e48440c0c090323507580d581402d60240500c0740d5461400d810400703003c00c1c44125001442c03a0b20041c504508555101c0c0501c8441c004c1c40e04852600d40e00400074001402c00301c1d90541d0681c481d114182c0451050403410b041503d06020b0081120303070040c0074400d11450b5440d0010301d0b91004103104445041c03054007041700c5100402443c0142d0f910b5070000385038404140094440800381001520510044c4030b9500090701c002070450307201982c200a15400b901e42480b4605065664100500358080c0140c01c041000301c0740068016440e1719611846ca08110b10240401c000c034034141039104100c00c1002046c5401c0c05401406007113810702d0071200300c0a041c0c44040c100d805c21868040050780920320303c040554041a1884111291002146440d29581c1d070040781c8420b910039036000d9040840c1c200c003801034502040005110400c00303910 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 180941501 1250 180940251 180940283
    0x41203091a0a050709080307120e0a03080309120712030903200f060109200f0d050a1b050c100e030405090f09060703150501121d0d0e040510030308090703 68
    0x141e070500712082c81c111454000003541083c0700d14009012240d004010714070380201c5e61284d0007980380b0102090140b045044da060050384a0b0720180000b140210361294403428100c4509040002003e42e01c050907906001c00d0000c14104e0404c030140040d2428002004241c524041c1c4a4a018a01d01c0c15850b5040b0186590b030306020421403214400038058a035641c0c2c8403c82c12044071800b107500d1403a0944114465064125500101204d00000018030705218240306850141ca07400c440403100107840e41d10120501e8580c0d035040e4166191810b00c141061210032503d0b54910894142d00021511040c0030030300740b0814070865015150280807844030b0303e0a0690001c00b09025a00061203100c1c0074005a1200c0c464410620111540d400e000c420341d1a00004480307020488100c008116600c0c0c03000036005401d24040100d00d540032000c2d100001107110098201c2c050340e0540d9000354280410000c0b112a02c054507015203034181007400d01078480301d802e185040c1183e00000d282d4a84162300705 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 180942751 1250 180941501 180941543
    0x7060623121c0f080915010608150d0f0506060108011a0d111911070f030b07021c090f2301083115090506010b0c2b11031204120309 58
    0x41e980c0e81540c6440130143c441d031107481d544000c07402e0010940042c8400521000b4030030300c929500603401c0d0360145044514140010410401001d045a000c0ea660611034200b0109000d043d51108090a158465600d00075080342c88680084660720041c00000e0201030081c620740c00995062070f84050507440b200031404500403000300a0703140000c0741100c0c1c020460030038000381000035070310304100100c0300d2461903554a80c1100042e214500758001d014a000c09450140d01071140c218540c0d071040b078080e1924401511401d02c5070007440c0d100c0c001e0b000b08140341802c0e1103d140000f02c02e2818581c6569101c500000780d1403000b100003000c801d2009103c0890842c25103041c041c034040e09810704825030200092017100c0381000b0040031600035500406c42d01c25032501509001c680002034820a10039034112040c1c1031944c44494138456060312002c3c2c0c00d542e0111040054400e1400110301c0c11090003100e000c42e07440140000c0011507889642c0d84c03464803c1d0041405150b22012040c040d401e818441 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 180944001 1250 180942751 180942767
    0x303041e0905010e09030a0f14030712062c0a0b060d0504030e01030513060507050c100203090105090c01021903090b0301151425050102070c080307060623121c 70
    0x6007503003004000b00d142400050200d00036134600005601e0010000000ea440402d4034040320248a6a0a0b54103009840c00c3e00662141c4003903514206140c01d900005021a0556000007a4100120380c1c10f40e602071303144d69a9620030061890ba00000c1c0d480301c8550002d410b181010076082440803a001c550340b20248c201d00d010b070788203485040c00b0001c480d0045049600031a00082000f003200c0b081004150242c2c0010f0700040d1070b2a2041ca000d011035441e518000616213804006031b030010810030150820312a840d007120030b01d4040c010198554000030f42d03072032903c43c507105112a01440c1c8030805005000d41030080134401e485a4480d030f51549019110b0000000001c08146244040540321001408403098110096a851880a2041d04580380c2e000304050807612590b007040341c074000c1240e41d04014018056100290794a00003883d0407400d07601036602c0703259001207416103031001000b4003a00880d42d42e8166107040d000503608080d589408000304050312441075280301079400030b600000e0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 180945251 1250 180944001 180944009
    0x70302100509030a091203030e030a050c01200712091a0304060c030e070603090614130212010207110d02031005010b090f0f0a050609190e1e0f150303041e 68
    0x3080015664006803141c580c440e040441002901100e030602c0030030140500c00402a009150015641d588540c0c02c519640c861040300001c60b20105116038944024007400e034040300c9501110104440041d48152107018603040106101c050b40c03850310201d80318420180c000d080c03074081c101111144008804080c0c0c410f403016180c060501d5400c10795a1301074002e5081c500c91481c0100401c078a000002c50082c028940125075180d110801c00400d0b00c8440300c1c860090b0400f02e161a00b03899548108184007c1a034114030059005000d21000300e1030440c205108040140c4001c00003600520000e82407416a000f482c4005103881c0010070204640000b51008401c02d4030b4488680c40f0741402c2024403d001c4078600d0380510300000c18012420701201415052902410300401282c0d200c911124110f0304d03070000070000542804200d51a948126071062102ca0303080d10001c0ca00b00f078481011455402404100b141e2146c0704050850b490403c22500107150002e805410025184104d8501c49806c3c42 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 180946501 1250 180945251 180945283
    0x603150803090a060f0203070204110c01060614030105040b121f0f090503090423042001050a02150613060608060a1508010e04080708040603020705210f031902070302 73
    0x480400c084800008885480750024811210203103803000c200c550800d80181c842c114002801642c00585807400348902c14002010f0950700c3e01c82c0701c4045401c5404582c4080100280b1401c0c0c441e1864a1a00300c9041d10702c25203010504034240008102c030303405a4254150640b1900c42401003074112440580700d95003040f90705202011800c1d2032802030303407140400901150020000c0b00050b02d4154081103034142e40c0350120402080304051003103188402c44055411004860300c0400d000e0000414294600f0309007082c5007403900c6400020350790400308045103d01180031000c03400c542d5904074020101c5201794401e2108580b82c0c08024048102a40c1060144500c1c841c0800c8440303100302d034840000c0c41c40e652a021686466000c01c5034400160055540010402a41000c140413000900180c105505d0141c2e44031500c0c98094900f0f0059824180d0035108150303c44009103900c42140e0402e40c0a07580e00c0d440c1d4807843c289024440920024401c507a100040c170004054000c5080419049124 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 180947751 1250 180946501 180946541
    0x90a0b010e0c0a1b050d05030405061f06081f080d1e021507090308030103061a040e1207020f030115030212011b030f15090b120a021509010c08040603 66
    0xe14107004100a46400030080e9050151840851042034942103444448070003095400141d2111070034402c8100400e40082c000104010601c00100f240940280c012511003111400d26075843c2c000f5900c9001e0241040700d040040748101201e1065010140440d20840700c2d507950360700500307981d00030000c01c0700041404090318141c0d03d6035441c0100400b12181d0040d14460110709150421500700805e800e003440b914160100104841e00041c50103940300c0d01000a822071001c1ca180b1141715000b080e00d00c96070900010b4400c001010071180303289041c0d26039807602d500300c510010f4046944004030940640c40d08642110f041141b20b00c0ca8101c900130b580c45402d803442902202e0903200c00301142a14110001101d010741132007030303001e1450908100000510003e0000880c101740c2c103ea40045800e43e00c2e16003035212440c1101d03a4070024443d01000300f0006040e41d0121385159505441c444070b103280452694826405441e0008006501c51681035951782c0780c14014005015039108500560b03416 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 180949001 1250 180947751 180947759
    0xa09050601151e200c130b03071203090806040605010609080c0a05100905030a110111030a0e060703120507110c030a020906090a02040b0a170105040501060806090a020903010f091104060302010801090b06070209090a0b01 96
    0x80c452047d0042028014120171802d00038481d0041007038010442c1048003a4100050414051121600481c454000441c40d9458900001c1011580f80c1000c04140c221150fa40400d0365041000e4003100c1c01a1052007017090b0030306080c2c40c4c8071402c4c0d10003a054001c03801400d080000710000a5403605090300d40c074602d07229043e1141d5a2703000722400c01c404503201e100344032030034540000684603c6209140280130b000c3c031130481805441701555204d02080d40c504c0d030550001802c0c8080c00c003101c0e05400a0844030242c0e00011014040680070302d0040c1c4c0b44a003c07480c007100c1a01281d01910311201c0d02a038410b1400c2c00140f030039049042040356942c3d0f035000401c09160500030541242d1071580c072605140c8500c410085e4510002d448109225400c000b2564a13490030b000c1c940050641c1000050428014181201403070351643c0c0c443e20a0386820010710041c5e03000741c02e407810340309040300c0002c00041003c080b41c514802c0c400082e504c42c0c541820480100c00020b0394405503072280880f00c1003a42d171 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 180950251 1250 180949001 180949039
    0x501060f08060f09011b080f0a0524060f0c1b0303040e0c0a0207172103062101020f0706060503010c020c1e0102070308030a09050601151e200c 63
    0x156008600365500203101141403c00d000d85200d070001c403c180001909940d280d48034002a040c0380000c3c0102e01c1c00d0342080300d05d55424183c0b66001c0d0000383e0600035454284140c20154007144001424004100c0056156888030010740d52110400302c445980c40042100c40381c1e0b00c001c20903901b40360074151138111f040b504010007641d04849148211030390984070f0340810740040c0c21090203401144185003000540755214951801e10102100c050940c40e2108401c03603488441d803a11000388040d0800500145441e000d440b1808815406100d2075a042c071101002c1c0684190000041003480104406c401e203d1035501c440206d80e0300700c0003003002000303041e001d82e200c0780e100034260307400310419040c00032940e41c44840e149442414070503030311034948035912062b541e0000d541d44d0f118645d65080c0c44082150070010640174203a40d440c019441080160010546a820043c01551070000e82e04680c4040c060070f8400c4881a00e0400341c02c100c1c0000e0f888a56400055006511680c0c0003003484c920741c00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 180951501 1250 180950251 180950279
    0xe0106030204080a020d0602070501050f01140d1a09100c03060f0e100b0d09020a080102070209013c05060313060f0209011b020f0603071707050a020d030b1201020703020a050106 78
    0x120507001c1e0000c074000c1d408201b03440b1a07511080e111503801301b1961001520a00c10b00d8407a240034101b500746541400c25400840c144030101e44c1c041c07071100308030f0808a0b4122041c00c5104281c04094100da035103250b20035041404183d0140c1c81c1d070303081020b041c5c40c00707400d60089c00a4542404981188079a103480050003164291920308105d6100031082c888100350600910b4a074101c100041508803040d40403800c18a41d9a004000f04e941c040f800c1c070114600746002c180100703039003507800b40705000c0c000c01e00a0084a01ea1001b060b50340c0c0ca041000c1448141d401100103280080149841c1e151400c04210072030f0401104452040c034001e034940010b0313030601c02e0301c68469041e501c0001c0c0c07055582c004072501441c02d03401d80c1c2c0064601480d901555417107004620500c910754030070740c40000c0134070985200b000103000c8a0910006020ba04032080e40050084114a030502d00416080d80761030101c0c00b0300000106080c1c0b55400003a02c14245600003901c650311034030500003000250341da066061101c00c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 180952751 1250 180951501 180951509
    0x72606060f1f0806010f08071b030509120a06060b070503040b0c0a060c0806090115091206060305010504082d03040b0a060302060d06060207080604050715020c090f010509090a15090314030901060e0106030204 91
    0x35032549014180703002240180c042c039601c40e013001844c20b40c1d1309001a03d440001090b8140c190b0041844003f080b041c1d000d500d0080130b80d02d408501705030007940d0300383d00d030b010764091101d40410100d1540740c0360f0700421071070540e150441401c010503519000d00038403ca01c100c519a01901840000050000c0000318641005a00d03940b254441410406440c80c11907400d0020380310591106030100129000f0b00c1414004e0348191081969500ea048030701903c4441c104084030030200419a00b014040e007902200d5026500645d031070010f588101c1004020130300d07508065000f440215100580c0138682d8000f009544158080380c02e0542d9481440b80d460104840c000c0250700045001c000f4600c0030501411058401d00554050040e0140400c00f90b840803111824a40d5240004128a00f804003210750040400341c080c2c2008100c2c1e403682c42c900c7c0b80007034210800b01e5803801480140340c400d004118607100c0c0160b42980d00d04140844a01070501800340c030101e14a15800003d246010780700303e4040f5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 180954001 1250 180952751 180952757
    0xa030b0a14010c02130204080a0c170a020d020607060608030307030609060513020304210302071104050421210203010602062206021305040e072606060f1f0806010f0807 74
    0x100700050011151410900d0040341c02c43c4141e10b500142e8a07440c0060000303044034100501440c440c50a240f0081e00d080e5201d040042c0703d08141691810300030a5201c0500e80690f8101c011010510209005202d00103000d4041c603c0c102001c241d50308003000079401800c859506001c20307030302d440340c10080794541d201d840ea112031201c0341022151490f401a590040c000c0c9040c1071030044807240300c140c801707504840c0b00c0025800511b01c810084101030f0a041c1201c00e40e000c20171898240e03104000c0c040c01ca9618401580588500c1000030301c1904400743d01044000c0d1702003410040c200c04c80283d0000c0c060304001d40500800600054145e00300e10201144112a8103451040313615600c000f540254444401c0900c0c816022030a0340303c2c4e0007040d41c01c81200c00102051480d02515125075003031001c11114908407020f603800036040000f04a900a90112640746c0351121366400285d040c080c54580b000100407984401102c0784d00075210a01c0b4000a89540a250b18034007800c44040901300c2d8500c1c04 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 180955251 1250 180954001 180954029
    0x7090e012c0a090b01031101080f0c0a0c06020c01110c07080109150b0406050d052d0309011101090b01080f0c01020606010c03030b1801090e010f020f0f03070905040f020a030b0a 78
    0x2036000100d82054001194002c0002c440020351210034410409810548076240100c28030941c03540d00c002080d80c400c00d007550108103400e0801c1008a50720035084a4010800c2910900f01880000e41c12141142606002001100140009000707142c01c03c0403c20001e00030300e9000950448107005045880360700a07406050700b540a601c1c40d0092424000c80da8103d6070780c41010816444d6101c0103219203015500915410101d42103142c1d484207000040e0700a504810020810700b03100000351603c041c024280252882d05103811540103089081001c0c21040520000048a04010840801e002141d81c152103640c4400401039035215400d417100c9000807481c02d5000c0210b88294040b092094000f00800c1003441391001210300310800b84c210fa1a07003660b5034506484003c00b449080c2c000b412104040d8100000c02004c0103080c00b130a041ca1a8001001000030314040c0f1408074000a0301000344200081803030a0421402500010680320110389001154030840c07034a2034010044485000107030354 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 180956501 1250 180955251 180955319
    0x3092715090e0a0b062b0308180d09050111010f150e07050412021c0f0507060306120507060f02120703050a120e0606130920100512061509060307090e01 67
    0xc141031a01310719050320006c1c0006440c0201c080d45d80018944c004c0d551410b0a04000c082400407501d0590700c030205030b001a407240703d00c42e0000300390002c54209090400240d02c14080c501c0c090b20100070704a0a291418852000025058110000303031030346031071250f906e9074a6a10580e8184224090b00c0e40c0c00c0030844040c0010719200c1420400309201d100c20300707100901a5280ca01000410400715295081710006001d00f07a41803042100501090a900078500c015032116a00c0c5d0616014130400c21540d84502180726000304081515015040c1c0e0865032075085080080c041e03004020307070100117405032048034036100050044138007154403c40030789041e450324020442104002d05201d88850b13224011903000c80d403420144108030309501441100d800e032007410012080c0340076941c0d500b4010240160603200864600c2c0c298006030645007403050082030006c01146008062400d50b100000104000f503a59110701903070300b00d41c80c154254200d0b1342ca42119094030313044018100156a01030020710 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 180957751 1250 180956501 180956509
    0x30207081b130e010c110d09050d140c03100203010806070903150b1c050102090a080a080d0b1c050318030316020415031202070303020f070303092715090e0a0b06 71
    0x40141501d010300203250f041c40342860307003544c03018000c000118031840700c1c014880d08140101c080300869440c0950b00981820300092484044441c003620000981c19290755a0004004d0054201401012603101e41446052000a9402409804100c0c000d400104517103901a5440034140c0703521004c0b407050605001c1d5100010300d0354080c490f50043d03840c07498032001c0325206180c05c01203006c2c000150751071090310144000d5076116440906960f02c80c2e080760700850441400c0d1242c1d01c03070780c90011034840c10075400176810840494540800d18420308005041040c0080104440307185010003080424000d004c16443e40541c0300008998130440400070014a402c0d401540110054544086400d1b12904c41e500f000015034090070141e4003d003002d20505404206909100d03003010b0050910504556008045520070720440310000c5505524124052030080b0f02d4580d40b040040030003049402c0034070010800424810200100e15200d43c09400d0000440c0c00988290800e4040006403a85000c0c8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 180959001 1250 180957751 180957769
    0x503010b0309100c0207080714150d091b05090709030b010612060f060c0b0f04020d020120100b010f05040b030708061c1b05120601060305060d0f0c03030207081b 71
    0x1030070160089003108410b400d41842000a04000c82d40201b14040c200540c0b68508095a00b03c2044048a8040200c81d543c1c0c2481020002d074500c0a01602d5081200e8820050000144021300405071011038141c5507200b450351404580d411107d62860b9181c8035400c1d582c2c0503480c080a03004400f05801481800e0007a0940802c094451000046c010313a5003034003a940845542020001420042c0c0c04014094013070072107500b0001515403074140d41031a80c001400104500c07802418400795240300d11040f17000000c80180d45c0481400e842002c01071f211070320000c10f080c844290200e84d1807281030190600c00c805482c1650785080700d451031a1601401510400c41c0140203aa1015848620645202040c4914440a8441c05002c9000c402c030003040b004201140d000070780170740021800c0740b50313289001440504403030543c18005120344951002c03894451641c5800b81c030707056041303115008104111543c0e0040741c1c00fa609441c10641c9500701d280e04d130040641d64225061081d9042c4a40d0b24140c415 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 180960251 1250 180959001 180959011
    0x1504020903120f07120f020307020f0402120a06030209011401020c120c180609070e060a030f0b0303121b07020d150615050903100b030a0b0604020f070503030a06080109030503010b03 80
    0x21540114040b0340740307403101d5026103111030203e08042442c0341000036160014030405807608081d2050710f00510f0080d568015207801031701c1001e4002c0b81942544613503045070030716114822140c0b01c91a020903420007400d458401280075201c0c507000001c102c41200000c00d1404416401f07009001c44403030030044001e40c0c4049118a9015104001c209641c0e0540311140c148441ca1000c000e62904004104540300b004203140c09201144010314019031b81d0340110785d030709603880c2030000b5144483c2070100014103d1050198043c40300080c0c0c400010b128845c6184030310f0002411000280c88613081031020301a4084c020b4014000c407a004001500c0d54002400d81450100005082c3c1d5580d141200d10003881d804240c00306c1c3c00061825102d007001c3c040015940a10b64050012114403c0460360360490044007500f010300303450109811380e4441d0111040b8144008603181c45810a040681d240e5000f992a400c0451802c6030015001c04d042c0201c4042c00c1d016115141144e1800c442130310240d0000700 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 180961501 1250 180960251 180960253
    0x2a0304050a0e0a27030905060304022d211204050f010f02010b0405010905040308090609071202040209100503010e13020108010e04031b05030c160b04090e0703060515040f02031504020903 82
    0x8030b40f0104800e0800305130000f4490090148840da0f581c02c01610709000c0c0e400c00ca01500d030400805c00541c55010030b007a01d480f01482e00720051031074809517800304808003400951043c088242d5078003460300e0490030701801d0383d810103035040f07500307680100080761150b40f146580043d8054600d0a440d80505021110300515000200356107504000103070448100f41c1080102944d54010b00c0141a44a08a5075010325044c1c002c0134103003000c0d14829a42e050500c200d00f100070414407088210f403076640603208019406003600701000c01e01280940590003d005d00c07040c000b07000b00000d01700151030070042c0f1041d4042c0c59095059003041580c01c5203042c02841501801a0035107051906400c030400c0d0f0700d1080c060320165484614201010341801500d04d00602a440b642c1c609100140300c0604550455400e43c00001e00300e01c1385800142080841e0740f020f800149010f040100440001305481001074080b1810003144941c01ca0394422400180e8401d462402168000e01003410280d00404441000170 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 180962751 1250 180961501 180961511
    0x30218151201080706110303060306161404030c0905090715080406060308120105040b0f030c060c01060305030309010c020c040c0e12030d02070807050f07050607060903030b062a0304050a0e0a 84
    0x1820100c95480e081c3c2c00b8511a61100c4001c00030b0f941c0c4030b19024440c5100b030000c1c1d440d60411000003503075540e018050b845000061940c4050840c00b9982a070454001c0c04116900d03180d0b641010204800746104440c081410b00300043e55052021903100240e8018045200b5905903011044541d404010400c17210665199008004075002801800d41d94588d079460a40640c101010f21040d81c00e103503082801841c04500d00946039402003580003e54005071143c0b501e0302007181c0c0e2035014241d10740c0040c18902001040c440c5010041d0410003004140360215040d99031301000313100895001c6420100000e108003007040080c42d00c1d5412442c603182d800101c90610501c1c1118034202da0225108451984000502a08006c4240222205499240050a0001d00e0b260201d9814807a550b030007800690f0f241d035080d0415001368460805460098031040e00c03a020b0300707600b00d21504100d40e00071140400c14501d8410000000443e410340c3c901404000f0780390700d8000c0e810481580030302510016603e071 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 180964001 1250 180962751 180962767
    0x7020a06090f0e2211010e04020408210f040e0117070b030f0709180207020f030c150a020312281109010c0305041e05090915040f05150705030a0c03021815 68
    0x81c4a0100041d40507440c1845c0c113068150024000440e00083e19001d68010b01007009408804503082014030a840c0c005800c44d201c0003444103403442003814190a2280100703000c140f40404680b528180c500c0791482c0ea1f28181408002655800e0302c0c4140881e42d00200009080103800720003160700801d0358104030180584a084250780700d0003030100c20f40090342c081003100075458540f8000d03425240030380140000103442030204004200882d80005115000220074060718400c1044880314a42013403501514100061f5862b1300300000c500b000390404207000d07800180180740c402c0c2c10f40e6048807040c1c10303e80b480751001598894400e0005a042c040284000100042810541110300001004158103a0700305820419494000348c0f00710b01aa000d041c0f00d0700354004071190304e500150460035002d10001c1c1d0749086441d00540304051815007802c80c0c00d002e13100e5000005075000e044040424440c900d0000c074110300728003a00c885035400e55144c40112010742020b0600c2c8001d80b00c00100a850840e41e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 180965251 1250 180964001 180964051
    0x314070f05010b010210020c0a080f040b1602010809030a020601050f01210c0f0207120201030203040804170f07080f1207140a140624120705040903030207020a06090f0e 74
    0x103503281501c40d40d4444049060a603410702c44104410143c25045040600e502540c81c0d0b00c00720021700520389080012100c0c0c01d0710003a0305480050820b075420594038490440c54040d0503a01150807408070784280d0100d40340200200580707958404c00e03070080c14180e10b420108070301003100091603030501001c2040e00d03d555003c000560034003051000b0106015a0b5074a008113510821701c0324004540000400340080110205400d114640900c1d000d6165149c90a10010b02e01c6103030f0000b52150300309228141d83d604041902101070400c5000c2c0c502c5181c0d00c52601d600c41c89800c1f8080c0756a001032000d41c031404a074401600c0c43c2406020380070030a6584c101c000d8940800380c40c0981e80c20102d05400c3d410801c08009103640321410640070194402c81400083e4200d509c3c804161290054103450b1081c00810000706008100c0200306105c1e03490a410081e000358803420b8180c0c007a0b8181c0c2d81c0440d01602565135076040340d05541d2100c1010780303401c1200b030304102e02402d95454802802c5180c03403448a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 180966501 1250 180965251 180965273
    0x40e0f06041b061b03053612030a110a0f050313060f050304020402450a0803030402060a090503240a090c090b130504060e0d050705060103031407 64
    0x4502801080142031a05001c050072001016915206a4444040c0a041d5110340c0380d410382ca06444400090130198a07095a2030302609241c0302070b01204030380c03c0c541c01070061219100302d0302104201141c42c0014092155841a0040710a59a4010004481d00c00d12841400c42440e00180540c0c4000304e19a941d0b1001c602c101c0b4003511182d001068105150807211004c01c0140b0203403d01f8803c00c0f02e103a50241244c000140064070a03580440e04000c0180d441c002c01403600c640b120007500c0b09010740b079942e0010944122203440d03010111005c4200741020a100740c00d450040c002541140d550358200903036a40011140c5e030421212903400a01c03910200302c01d040c601c070307000c2503071502e82100c01c0b49200c15200100310042c0f45041000410100d14110800c40548982440c00701d1401000d40c00700345100380c4003d4030314009107000f0030030050100703542c40205442c8214060350140c1081500882c0c032405160030141c410f40040004100207809280a11440d504103a20142495415124580040c03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 180967751 1250 180966501 180966523
    0x150e010e03010c03200a09210c080304060e010e0603010e090a1e060c170a0c1b05010603020117041109060f03010e01200a0c1101090f0303030606030c08090d0e040e 72
    0x81e21444440f140384020390300c1420100b10175082a00f0b03c503501c4001403009089200d02440303000c0180c044c80709403803001d400c0c010990300140070306012650f031008503580b54028805e02d000281c3e801c9001d0a9503200b0700c04c100c01030f100105910300356405d05502010340711024140e0f9286208152400001980e51150000d0603d201091006580094180503058502182c81282009004a00c030038649034584800354104012001c00035032210000400c0c0c412500d040341030010800180207180402030150404403d6030b00c01c0e82c4031003c0302d11290035411151800c0d43c0040404071061201003007401c1c101200b940c00040145070610300050500441d0031111200c500000e10303512441010b6150505c03c80415001030a40c407080d2401d0341e0a000240584502a00104516800c1d1000d842c103a104100c81c4014040e08500e40305526583d01d406002000d4a100f0705011909061755050691b0084107114800d01443c80500030b040103202c1c040f50002208034400303a01c03547e2282800312501080054020b49 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 180969001 1250 180967751 180967757
    0x204120c0603060b09090a0b01030209040e03190f05030406020c1203041a241306051f0207050103020306100305040302121605190c051c050d0509040b0406150e010e03010c 75
    0x5982014002000c3e01c2d007940120308281001c100c894542e464017000560b0011b0034480001ba10301c0f90360f004a0180c4542d0030030aa01c6400c02540328604c18021005000600c10328079140410000840b003640c5491002c420031010800c05d100090110344150000d0000d40340b40310a41e81e21546454070541250010f45044c3c0d078030101c004010b541da00e00200515000107a1405850408000c0400100100c551a07410b0f4041c941c1c1000401007400c00b40c110703034080e000040a191034805c910128517031006034050220018420910b0028481d4002d10840f402178001911210212a0180040c3d010700000361089046225800d011800b4142100103008007804d209071000504c100c07820050b01e0066244850000405d2620f07104000509030180b0703a049034000e650a040158004160481900140c1c2014000d4020158003000c4680d00c00000d0541100c02c07201002001c94030400d10085401901803496010503120103107040301d000d15281125030300140f5003103091401e0a4007190940e0aa42594004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 180970251 1250 180969001 180969023
    0x2503081609081e010c0905030c19090c05120703050907410315010e13030908030703020d0305070c020d031b050a06020a08062b111f08090304030309090f020412 70
    0x5010028040c06005072038501c2c06c02c500c5410000020785079100c1a02c03d40c400c415a995000d40701c0010303110100207080b042010841c0310089000580350764003140c1d0305012064030100041140d4068480c150040400100410126003040c2d1a2401c80300800c004240605c043d00340e16050706200c03900f642110501d4440c40d8061506203061524000d1654107075000102882c0052010f40c1c200340480354888246040c50325650014101030383c82c40f00030380080c6103038000080c3c003406140e0002030b22840110307a0b0350b040006c5d6503000c4040350000b488a0000b58001d4043d6141070110f03101e0540d1100d2038004d606050a6022940d032560f00c0d00d0390300350088603e250003280382c0c0d4206810944a590041d01503a650521146c0d5960414801c080440c1c40741580d0060440e5109020980701c0440059401410380f03c0c584511248001000c03a44440c04800a002d41c00014644c100200a0f202240e03419120354204c3c50a01d4100f0014201403a54240d109500f4400024060801004c401d96a8012415a00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 180971501 1250 180970251 180970303
    0xc03042a050306090c0d06020706230402030c010f0203091002071206050108010b0909030f03040c03020405090a02040f020c03120c0706020307080f070903031d0f030303010b250308160908 82
    0x410007100a1092050342c04c4401d508940c6d407580041d290344160312040050345c9031031300c1c5007031401000c0f48540498406055486401010154040a405280220101d1b1a1f580b407040c01145d40503602c41070000141c01c28055040982020a0180c8200c00b00d0700641b8041c0b5291440030104d102d05a1042d60416102d00041151100c284203410b011031040e0703600c00c064071306007007010390700d10459a5400420100100040c00e0107441442c660245d80d00500074400e41c01d18803c255600c1c2c070b00041c260705c84ca141480f581c0c007000246c82294000314a0101550504d0219042d034000814020701c0d110348400c0c10480240021580d02c001c1d4441c5010f80c03221412420600c5500c106a000142000f051145985080c4046504642040041200310360300913032a98180d40440c982d100e45200b6503030035100200c00403503142c61690140903074041d00c40106481411200b07201544041c0f0f100003a0100d80e580010401103a64078014810520007402d05100300b955500c070940c58001040415045201c800240c05 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 180972751 1250 180971501 180971503
    0x60c03090c0807030f02010c15050c09100314220510092a0b03070e030d02010b0f04140609062d0f010513060e040f0f050106030e070e0c03042a0503 65
    0x1c0040c01c0b48500402d2020b0541d40c0b8107605010100c40039050000850308201089220035a8110b21803007403900b40803a0030580c2180049400480c0000c1c030820182c0064808244644210740016040120507000d9881d82c0c020b42c452201c01900000310310280740041c6020071000c103e9511900c0d5030321000a0720859134203242c1d0700328401007220000c05002e010110b4041d44c0b400340c44826202904001650303501c1f00b02c4180d501c1c8404114094041c040d2014060a198041d48100c080c1c446c1520741401848030b002c00c020440d4020300c1106034420702000031655605045003603642c004009400064014901c1040b850301c0c010882c42604103080400181000327007450225601c0d02c100030300784641007010143c000d40050886005000c00c001400909140c80d1362140c00201c0e005410100401c0304c910100c003120040c2c0024060140443c2c10001c3d072440c0c4034000181c8c00d040320a070b6410312459455000b89140e141c2e002400c00d49042550b0001c4880031100001e0081107840301c54091980580707800241 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 180974001 1250 180972751 180972773
    0x30f09040b01090b0304061d150a050705040518090703081207090905040f06092901050a0b070308070503270606040b040506010c020f04061d1503010203062209060c0309 74
    0x160304000f4020010001a9100390a40e508941d0001c404a04540058021591180280d210f43e00c24814100d00642c2c0000303c0341d0042c0181c480c0e01041c841a07540031003e03600ea100358407800b900a2590203201d000d010038400e0840d00b102c0c000e000d80d89441d50747d450300b080075040114158025400f2109000b4081d81000309c00004050b410000e2016180a4540340f030709454010003d42101c1d250480300041090f1f1004015102204415041041941583d0954110f00074050640900902e02c0d002c280c080c00442503c01403545542d5030180c540da102c80880c0c03560405484131a2600d80b0700c18100c11600340c0c43c1c007c82c01c184210700030b04440c03900008020541e030051014078019441d000a03c846030340d01c625a2000c1030340640381011030461000c007260041c0740c0d603480021100314117404c102140241400207030180015100d5943c1075960101014202d10058582e140e22503840180b0040c80f410980d0042c2d11401401c00c00039035201191a02c1040d0790464081c0c40003c2d0340c0303181e0f18080003803150360 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 180975251 1250 180974001 180974021
    0x7050417150c090d02091602010b180712020d0c05190c170a05070609060c0f0207060207050103050a09020405090d090b1e0306120d050a110c011d0a08030f0904 70
    0xe10100141d21040101940081c000d00d46045000581881c2522480d000c5104140d000e40a00c009140c074031468000180c0e59140741005500b400c844918074a03005021092051510309400c0058881c00300641300c80b0840903c1210403074080c4034146510b0000d00c91003c0b00744240d1030740c960710801140f8400f004c1440480c81ca041c40349258a080114042074141422a40e0019000b5a503c4601c0d401303035264014940010000740c180022103040004581220140c1d11064458040d81c800300a81643c030b54019000b0840140e10401003000a503200303810158111040e0780340020900340a8011a05031442160101d100c2e5005085101e05503038040004402000181c0c009410001c00c29003482c45180c0002442400d4800440801c441c4d80e00e0540903480d03640040221a2658143e1002a1180e003241c0c030601c01041c040030081ca844440880d40301c408450503541c40038210091034800d0760403002c00c1e100d1a003040c4c8400300805c882808000800d811206041c2c280c0e142c079102c0c01004256032420703035 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 180976501 1250 180975251 180975253
    0x92414010b07030f0e1305090a050105090d0503150a080a030f08060102030f040b0d020f13180204080d0807031e06090e01020a0909050a02071a060f0901180203040501020c0607050417 80
    0xc1c0b400841e034411480c955003041807410308030358032000f8002000c02c542c0c42c2c3c40726072061412081c41b60f072601c001369404215102d0002849580d891003807464845032242070b510007049c000c200240054103583d01249400a004203150305942e2644699440d0401c03484048011403172031203e40e803180350031001d2550f0224003480190f2a0800400e030146290060303206501949802007201207200c84541c05a0394407020b00c090300d41d1a00c181a030840001c1c807043c400e403118100d8001140c058900d8500882c0d090720515001850514101c8004036034a4100500020416655801d081540c0303891006100590440c10f074082851800c080d0b04d40200e0340c09aa00c130615a00c10440642886d4000300e00d24200e900f15900000d071940c40140d900e0107881103c2c8010901c82c2158200750307155101520707841c00344400b80c4140c0284c42c204000e11205807402e02806050b0200f425150440c006203030020b562181c410320025081c03001c880f104616245d41900d564012800108040c0718009404801d04c15400c3e400c8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 180977751 1250 180976501 180976507
    0x2060603060702070e0c0f070302151e04030804030e040218150310120f0602040905070e030703110d0812010f080d020c06030c0a03180308100605070503030a092414010b 74
    0x200003c4d6807541a0b100344800c0b4408140001c1d00c5c45141425902c1c0c07080c00d0380640341e0320301c01c40c0340081d01d8001d060707003403204100e406021034403801d040f0007000020501030090300f00d00d07115900c09a0341110024401c504000d0310950941c0c1c2c2c0e8a89001405c2c1d21034054103c40b03819110f40c3d0421004015a600eaa024004e0901c00c2002001c1064000c40888034007034080c07801c43d080d03030501d1090026600300c0500300600015000403461044e0384240d1051500740e682000300600c0f442003585551700e0f444060201010340884100a00e006011022260320480010b4684442110308014804099001407a00416070108101000d420300955214070707444d201078202c0c2d01290001070514000070b0007a50052001142010880c0d00992280040032030002a02d030200880e4a070041000b0b83c00c40e90035040c00c4482c140028054040c030140c60300e180d0f0102c0a9070440e91800c1c0940003c04000e00f0607903c6c5001c80180001200300030640300042c0545841c0400c03c0c288000c4101807280f010380c80b52007000810 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 180979001 1250 180977751 180977761
    0x6060309080a0c1502130e0117120d2301140307030c0e10091b090f0602030f09060910020c0415060503040609060b040c0210240b09010507140303070206060306 70
    0x40845045244070704110f0007080080c100020701500800d0140c1c1440d01c0001c44d40605054004024125501301c1803201d4580c1e250109503910040480c10300c4200d0b403040e1205c01006110074054081d08070034050024a000d006001c1085403820706900b83c82c1140c407103006206014a210000007a4501a0003c2440c07a286540784046000a4841c05001800c51008908c55555802d00c43d0028400c0711414441c4030100030000e010b4804cc1d450410110f0b2070141e00003a405600341ca4041220b1440e006103003030202c6002d02c3c501da5440552400c0d0702c8a020080840c041c5c1d207204c0694102011a4021b0156801e85401e102c1280c055108040d0849080301c000c2140c0c940c02400c480d44180e10100202c0d00d600d6510b0858050300006070411360007428200c110032025400280700d1201c0701c0580040c0200c2d480c6485502094002c8003450310100440c0c0e800b4444080307024010700d82c0c100306140c424a4007555441341c03803101400104a0119400000034030104580c10002d564101104601514481c248 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 180980251 1250 180979001 180979013
    0xf0201020c1203090105010614030705210a05070801080d021b0a05092d0f04230f030a090905010b030c0717070606090f0b090a0e0c0a15110a020f0402180409060f06060309 75
    0xbc00e003401b0000006035401c10180a8103055551411022078190141081c007146c00190038220b908034001004100002a04040002d21a00e031403280d80152843d00d802d000c100100710310714503441d900720508200008140e1100001c0c20301c00d103541c0c43c588141d079004164102980e010441d681d040c2c1c10207070040c0044404504109500710b50720441c81810032899411001c01c6104a00810b4400d0040350603840c03503d88040020421a8466607580e07500c140c44a480c001110028001e0000009040c4002010a18400020601c4034040c03401c5000e041400309051503190f00c00c000c11180c07a6210502000422402c2c0140146d42d0f2484805110402030030b00802c0752403500400b40a00a6210305a0034580101841100240700c8081d0500c500c030b035220801c0901401140301c0fa000000d06544075443c05280118080051540c01080c8800c9400c40c601040041d40001a0b0364280c8004031a5081d081d640b00e00c500c0c81024464107010440c603221050010890705d03103a01007001c0c0f500701420600000c80c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 180981501 1250 180980251 180980257
    0xa0306060f080f0c0402030a0e0a060204180e0a14070906121a0702060a150e09010b0102070602060702030f0703170403020d090b18102a110607030f0f0201020c1203090105010614 78
    0x107421780d401a12551641c0410024101c06040030095025000000d024030445800501c01c3d40c0c2200070f10044a8803c201c0d0754110392a112100f041d83e04240440400a2905400d01c4296072824040701e0035951241c0080c421030f1015440300e85444d00280601c000c004108a0714a058022455414a01d24011101940b0f83c80c004044244060f070741c203481e1018031030034141ca102405001500340705030b20b064400e5500030040b01014034054801c0c00d4001900920005038540b05100641c055802e100d44445020f0f1560001c0c0c008605203c41407000080b0120180304480c4540e00903130040c00020440c031009000310703500c2d801c4828407440401c0312140100303480f0144401d40800382c03a141810f40c91038004503010452102c030300b2641074849500703240c400481c414000400f03001d00321540d46640701c0030802c0030610540c44024007146041403041803040c000c0780000705000e0f2600001d85001741201c003c50901d5806000005068000b00074083c80d91400d100e154094000d90509a480d20715000403804140 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 180982751 1250 180981501 180981523
    0xc04052401020709020406120b03030403051005040c09090302101109010e060f07020303070b01030515071b03020a05030a05040806060604140d0305040e280902011b110a0306060f080f 80
    0x800311515a0101e034030800243c00241402481151503540f81e5100400d00c1d0b200d180542c1119042c460a0030071803902008985c1102d510000a100101a104000c40680001401500c8411400b000003030190442d0046408041c400d0f03018110b02840e031510743d4102c400150030011200c405110001950340c2100824412034800c82e000f50302c07285400c3c40190184244030009401d40404a07110082080280e4001c0c10f07207118400752070702d8104224609240900860304100040d8802500310160662500c00340c00040c000d105a80d240720310782e103607146907034810080300000960005040100800c18002140c01c00c2d002c4402d40d02e400c0c40c0455000c800000e42901911074040050418105405038040760001d004100210009142103000307031006040490315001080162801800500603d1045002c140c3d07050b1142801c1d03164031010690300c9c0082c45009c6400c2082d2124548050b40d42c021035500461042c072002c07070001d040c0117024408044690103030762554044150640000f00108030b1107080 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 180984001 1250 180982751 180982801
    0x30c1a010303020c330a1b0b0411041503150b090103020a0501031d0d03021c02070218060f12010f0c080c071b0302120d090605251b090501080c0405 65
    0x41c04017900c4548481000b00a50001725110051201c0300740107000c05089010859116030301c40040c100880c0003075101d50b200083c4101e00f4400002c000601400aa181c5143c0107440026124030001b98a400344078150001d440180919220100787c1085002d0041681010f65000a82d545160b020542e02d140c0c40c010181416120b146000c450506080c460b5400038014040726103100c038000003e4000e50250b400b01d2100c2c202c414038000044014000c036007801d1782c090442903410081c0801c02041680160003250700503841d01c030345250340d50340d01040d0045041c00000010100640022041101e82d00013a81c41071200700000c00242c2d030010000c0c3c503d00c503041030070140c00051803042945100c0e41600001d62100c612550060311100000301c00000040a444d501401038441405880d180204102c61650a0541c81c501c494400c40c00d5030306400c14460640c00342c02c1d640303c1d0b101482070300141d00030007003081d1780e0001042140400c0140d0340928009440c02c01c05070a281405084039541d0140041031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 180985251 1250 180984001 180984019
    0xb030a0803060325030213182303040b040807150c0b0a140406150b1615060512030a1b0818030a060608010e01110f16140a030c1a010303020c 62
    0x103503450512002e400c44203000720b4003207080c1c0d900c0b2413540a844913020aa000d040004109100c80d0040d00c1003583c0518151040c1c001034103155a1901e0309030500300401d800001c01e07800c0300c408250410250014003149504181c0307650a04012038586480c0d40d00c0315145240c01c41c100400c0e5a0825070f558a6140c020030007048aa44a00e10326015023043c1100001c450103100401050211507400380d088592140550803c40f5624996008540105602044d2091000320a840000c1030034515500e086038440011410319941c0000400040b5207502620203a0000550598003030f0784412005003600c40c00c0300e15603001e032082c0c03500000741c02040d03107000c00700440b808448581e5a04001a441c100c2c2c1c01041401210388488015010304146d0002e103141b582003e03940d6495590036000e0302c40c140c07820803a59040c01548004400c01e500c44541c20b4402c610300b422901301c014414080c403500240a5120004030462600d00020000c0c070a14607d081b08d10400b0040c400203030b020075a0000c4600490f003902d1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 180986501 1250 180985251 180985261
    0xc0a050a120516060815090601021c0324051206070e0d060b040c020c0102010b2d060f04031101090b120402040209030f16060f080118230f0612010b030a0803 69
    0xb140000f0410a070300070701c0380319a000401c190b01c40301540c031401500900645840c883c10612400d110203a81803409078001001d1002003455952a4409485040c5004a0380b107030964501e51014910400225944840c0744052020781800035207000c542030054001d203036500c4c0c50f94005108013900b001b418442d1014002520601c62076401c21070304070000130800c000560004a0196076150080b0099025500b0020447e6080c613154203960b218590211962900c40503024946401a0390000c1003a8003850174400c5950740f500e80f001a101540c4590708010760860810009010034016901541c01c201c41000121025101000110303041617043c1c0b4050b8441003c00700190804501c000743c0310f498815502600c4807407031802c0c401c0313084407041d8035481c0c14120300c0c60040b41c1400b400d0041e41c0f46c080800038001e0b08000c0303580c0004004110003000303440030100700701070011000c001d071220002d6980f41c005024103441c004207100403c02d0450020403202d0a500c0c04240c40d0702c805440601803210120000f0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 180987751 1250 180986501 180986503
    0x4080a171003062003070e1903020102060a020a030905070305060f0a0902130506031e03071a060303160c0302100201020d052217040812120f1510020f06090a02030c0a050a1205 77
    0x140c07400d00c1d03c1c0b50039489140020300100154030441d0098412200c11001c07030745110b961008c0c5c4007038903012382c06020b040d03444080180c069486901540d0404d607030742c05048003240d82031244901841c031030b0700940340c01c0c1000208a110440702402d1444c54510f05500030005950f068034103001e00d60304076000300c0c1d140d41d20070009007080640c612074203e420070b440707807200720040100090141d14882c0f400003401d088002c003000c0e90b03010111000c41d0941d1007048814a814907259008000343e1040c00001400c80d20380d40030410a1032400b1003280540e402040344e40d01d105040c09607690218500803400880800150b65091130040391801074441c0527003e54070342d07105035154102e40180805602301e44240c0e08925084c06640d000c20701f0036240e0116407000c1100b10140041090003208882e0380e441004c607a42c4100a00351032703a1b44820095119503490103440000074882c0d02e114101140183c42026124014941400c50001d001c511602c0340703a5082c01265100b800c0c10059849004a005000fa070030b2a2003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 180989001 1250 180987751 180987791
    0x916090c020c0415080f0102090121230402100c0203030301090b04150f050a0f030b060108070203090904060e0c060f0301140303040e04060506180f010501081003060504080a17100306 80
    0x7003500182030074000c4e43c0a0200010503401c80d0342c2c1400311803403100d039020094203c0c003c01e024140015074084030042c7c5401e44800c02e40e1416109032001544800034150302d10148000c0c5007074042d8514003002c020075843c003c0e65000001515013401d03038800c2d0450780020340300d00c414042e00b03004655a032440905034940d640810300d24807240c0302104445480b85007415a03180075214484c8106040d043c0403481d16a03151104c000c50b0350010700001aa25002c006556921000708200214442404000207541d1a400b6a80c0900d024031800a80c032040b0981003807d0018409225001d0b00b07041051144009004085030304545c0700c0341c401c00310504600300080c03e6104950055201d44047d100f404240449684542d01035403007110b0004c08481046004c01800000b00c55200035044c2c20320040085500894080343c0c001c0c282400040303415101e98a6004450341503400380c490202c0401c0b0004542d4100e0940c1e10f2a10210320b07800020300d0200700040c400702c04c5000040109403184840c8100042c0c001507 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 180990251 1250 180989001 180989023
    0x2011206050306010803070516060504090b0114120f01090b03032508040e0a060609030816061d0102030a15050a030312140a050402150a050a0e030a06020408150916090c02 75
    0x381c450f01e581d98005140c2c1c81d00b0928040e01e060081d1041c4108907140c43c01d950f01120510b03201c2e58101b516210301c1000400030031401078180850070b040040d070201203000030140d81c1d0909a6040003030805411a5283c440141c214a01a07413030311a0a810035035001040e02e050307011459107021049030b0140caa0036401011070300100740907000f04000c100b8098021031503224030341a032010485503130f880808644526403480090b01da40d100300f2440d02c0905002d04101840341c0980700206e52151001380000800c0c1003214000e149035400310510882d04000d0180f800c6820ba880c050740e40c80360a140018012100621005060045503001c48413035074441c2d04010300c42000c00007030003da880c208001d2130140400b2075007207105a9540058410244001c41503c0440d9602da0380d00d420701040c000c2c240c03003881500054540c9485800148000aa001d0008001419004e0040c100c0785407103000c015034903c0003030407140d49908044910300e511069200f42c0c20480d0300406010444003810740090342840c0c0c400d14 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 180991501 1250 180990251 180990253
    0x91e071d2a120c07080304121e02010603030216080d050a180609080607020d02031606020f0408070e0c0a020a060209130507111203060a060309020112090317071b020112060503 77
    0x24118a0141c440e030160045040346a0007495640da400f6800609114804000300350940500108002c12250301c4568a100b0f001d040003500e500048650b848542d45500c180c60050391140f400f4030805506100d03804412030001c2c48400600d051850958655a21000904c100030000c00c690203444c0c814450484004603469801b0007541e107845000b01080c079640200c0d5424030403180441c2d4042c0c400a100070443c0b4031940650704003020034126144400070050309544103a000c0c00020031090343c1c03000510080101c1c8008014203468103c449100040050207000314440a00c50440059000300e802344100b85d100d140103990385400b000260100c0b50301c402641d49140307403034100a8055003005d003180404081c2c000301c6441a03110f51083c08944012101e0720f400c081062020442036019030042001c0610504000c489090000c0d0442c0898103009820341c00150301802c101c0c080c0094014054000840d8640440000d028415011400e0003200d27000f0704020501061000e0390700070741e02c02d0000d008001c0c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 180992751 1250 180991501 180991561
    0x908130e010603240603050601023f120a230f0f0903040311100c05100207030e040b010203070f0203010609020f09100305070f030c0e040203091e071d 66
    0x103400040d000c0007401031501191819240d1000940b14942c2520403910b02049890840d061803800c5000d4440645868158031545445c0e11038410751541e00c0000c2c845c40d8410300344c99a42103100400101900f807204902c6981003140d060001c006001d075691000e5500c101241c0c2500d0b0001d0018221020072125408514030414040000c0d0300c1119540a0421030f480c8603915101c0ca0750b600e48a100d11320004000c040707804502015820322513010001c1d80c106c1d081903c0d4520007520f40d0b03801c0015401c0d0400302c00364001450300030550031204180300e4802c180e408006a000c0040040d56904c51101c01900002d07117240c0714821540c3c2500714a010f40010b1009649580000100c50040c0e0440c1140d248254801200000d81600c00e04c5142c2c4246250ba031001516002240c0941c01000700012040401c4a020011001500d681c0021070103800120b00611082c5c4021160b2410345070f8884859000350441c5000b00104900340b603aa150540307e03644540e9803500d41070075407141b140c030311000703060411505 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 180994001 1250 180992751 180992759
    0x3190305030604050a0608030912030705070602160f0f120501060305030d15150f080408040e040b06010f090f060f0509100c051b01020a030e030c0a0b0d0e0c0d06090813 74
    0x114001c1d60003280d09603401c0c40300340c40e110066400d8902c00d0151550a610910a403c624500304070b5490901e20444103403883d00c40c040e2600340c140340c0290000b03030150b40080b65004d185103d82c00c60100030911014101c48017402c0c070100c034003c403030a4403e21020112401e05c840a1200a500c444003c503032090407603981306050101d20000d00000b448030081d0081d080310016001a0308040c4150310342c40c942c4c2c4d01020303e40d03030f20f400c1d02d0b5918050002e49500b001404003141104040101d18000c9001c0c03c0e01d00154940701c2e00040c1600260042070b020082660300c01c012910259200c241a13032164142140c3c10b002e154001c4031a4096407600d2a40010b00c40f01034004950860308544105008a0a5030002c000d94410080024810659980180d20241c0e0070b0011030300c181f00f44a50600f000301620800f440903400104c1c141e503242c0240c03295000025280f03220807a0f912803800f000c032030000500051000500041c40c0c151601d400030b0b090070f854880d14410809141c08980008a01094000400e40c0f5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 180995251 1250 180994001 180994007
    0x7020f12030d0516090801180f331b021b010c05190606050a06020c04020f0c0109120f020a03020c04020a090816060e0108061e0301110f130e010605030114031903 71
    0x1180f1424008200092008101c0d84018000c6440386423007103072040c2da20389060f60f900601e0f5110310701c180c031745024456900f4882c1c581024aa03c016010040c00e94015605440000458a03082102c0080c400e441c146480d000342c0100d4911000c8078a0361031144221002130041e1031000081c1300c020300501685c4400450070200c5134051600a01034503007000042e4032442480744a070418003075000542d101c104c180845190540042001e020908031150512000d03480042c00e50f195490b0460307202400a42100c043c0380e2000d0a0391103954648020708092500c3d032400307500e078018194042c4c09141c0024038051014041d025640080003540e044031122602181c900d6080c0c1440e001b4000094044031900021b98030920203180140001070140040b610b11400c03100500203061501078140d500c81c1001c680903106900600410710000e43c0e0b0503500c4584149001d150f108a4001260504c002801480010351200960703054a600410b03040030703004004002850980f501c601c038107402c8242c46404c3e08241d8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 180996501 1250 180995251 180995281
    0xc021009060e07090618050604061a0a1e14070c0302031c12200d090209012303010c02030a0f1e0c1101030b0609100306030f0b0f0c07020f12030d05 65
    0x109980c15642e00688881c2d0044c10341e4610321a09162070340991700c04080c065690700c010340001005000198042c0c1d28040070b1400001d200e0301c003520660100e03200c44010b0b040320b414044804103101104540c040f4503c0076168031801c90b0b00201c00c0c000850040c1c204040e142a00d00030395001001c5440f10045084c604484440c0c02c0800c8000850b00e520114000d6100c0c05035013032100301400989502d6061f8580260341c1c1d0815144c00c0c141236114040040940c0302c02866a021300b01030b002c108000400300340c61100c0d0001c080c00322070003a03142c942c0d0200c02980c040140c43c280d50303191a01c80300c0000582c0003103d20161030712004200c0090450144549d42d08000c158494600c1030580c0410400b0140041d0111108415459080041045104494581603080b1316a03088103013030000d00c45440341c50742c482025000c40210b41c0000c1280c1800054070040f10f1456102c0040c012540c0b4042d040e031b02141c4940141c1409902408040f00030084410b4140b00b40c44809110060401052401600415041c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 180997751 1250 180996501 180996521
    0xd2004090b27030a1b061b0906031d07030f08040305030406050702040c03050f010b13080604050c0405010b0f090d020604080d080f060319120905100302030a050708060d03030c02100906 81
    0x201d4107120407070311060b02005440c607110450300c6000d040b4940c145040820503200200322078a035500c4800720f001c8102d4014503250381d03034a035840203050b03400d11101400322040700c200d00e104001115031110100c400040c003507090364bd0015080303007035600c24a84103900d800307039400041840c00b000c200401c50550140c0070b412540d001325014008000884400d138100d0b80296200d500c004ca40e0300041c41004904c1008000030b00d4a01d02096a0031341c0c506c001810f11106940c122020703040030011500c6403805000e00c9003d031215003242d51800452079030001d41c502c1030900321402070034048801025950303110260303002801450207480c05038006103001081244100c5054540707100000124083e810000341081100c1c1035002c4010001d801502c46a41302141a455002040381040c0d011845032100a02c4801d21259a05d01603141d0811031995816104010088020012440200300865654031148508250907040000d0102c0004074128104155014281c5415050800c800d0800210781d0141d0001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 180999001 1250 180997751 180997801
    0xe040501020d0f050f04020f191d0109060803340609060515010c110d0203030a09030309060c020f04090302070b041e0e0f07181e0608060d2004090b 65
    0x4007070403c8143d0308540c401d5840441825918000030b0050509840901602d4401071a030317440c040e200701020002040b55004a5112407400d0700b4001e100304c0c01e4545c07602512929a090000d00d06150f031150f0b490107401100940007911070754003e99150041810100b02e00c100468105850090034043e0291191400c01c0312000d180c000080c64403113003003900160f40f4034144c0d54002841000d440d00c12400e14440c0489500907101c4034001c0c0180e800f04000c0082c11141e4580385803980c590704029101d810154444c0d0148034015010270016942c0800405052004541c0000d9100d101d090481c03400e10b41c0d03003100460f10300000700400c2c9120703501c60304103102240301c4000c0810b503291810400c8070501901c66a00d01c010202c081592180942c011081c0302e41d1108501c404282d9404242d0300251460200000d644244070060003006c0d07002000c29030014090b55418804c620070f80d150007818400b0901c0070300b00240108801d41e16a40ea801108a4a40111000000d802e196605002800640d0003110360307 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 181000251 1250 180999001 180999011
    0x3210c190329150711040c0c140613060f0b0406080c0f01032c03070f0c0302040b010c030c030813020a030b1006141c020c01020313111503130c0e040501020d 69
    0x4480340d6542d00e6039200c100585140c00d640b25143c07881010380c020312801c941c01c500c145100103168540384900001000b0b190366155500c02c60381080304000010207002983c1d0b80042040060565145000401c6650b11160001d12004c0c01714840d00100030342c0c035240703a10904011000519002c00500c4641a5600b00da0843d01d80c40c542d4015022106000080b010303180c2c00c1e4104160010301300e0940380714880d20301e080d01d140c0034990b500d000030f401e0201402c40d524030b8988018000c1d400e00d84210340c0703144030a0a21418003100c94601808403080e150b0002c04204503100002c0d000e41c116a07029502e0f581c080c0200d00c400740c881c41d008404990071215444100219840040d42521551807518102800403805180c45000c2c1d40d01900401c0c44030013920395030b408002020303005409100440c0b180e54a2031403e5040412407900d144019010b0108502c20001403c5c803200d001e00c00e4046a4010740b0199200d20040b8040ca0050148085644082009a003240402007404810340043c4140c0b50b0600c0c4c1005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 181001501 1250 181000251 181000301
    0x60d0204032001030f0c0806100e06040609180204032109080f0102041e03150e160312020609030c030a0c0c0e04031106010602120d1802090a0b03060903210c1903 71
    0x106c1d00400304000014a220004c5082d6090031315180b0320000c07180c40d10649c0c440080b4042405980035900c200700245c814081000b001c02c5064503100d404502d400d0640c942032542d00d070b81800f18400080000e08080001c3c2c0707414102d020f00035090003003800500b5228424482d06e00035000390401e02c10120341c00c3c0c6407000313490601e48280714602560b0b8480e600101c01303a01480141c008240b18a40c0010302d10405101149140255881d08000c51050a9041e0b070080c4d4584003c7c00d080c80070f030003e4201e62081c07090041002001c0280c6007018801e2a20460320440303810907120980507544090703a888a81002e120074146d00500d070b6100c02002d002140d42e01e90b601c060403a031300d6043e0035280111900034000352101e5143c6401c0903070100c0580c504c090507011729800160702d0410964404042c03550340c0400001606041c00f0040d40041040c01850400307804807600c0c148681400880d49003604848005914074141e84142c4500c1d540344900c0701c01203495207902500070864101310307445042014031885 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 181002751 1250 181001501 181001531
    0xb01090e1006030804031401110d0605190302010503180c04050a050115020a02031203070e030d080a0b06040815040f0f110f100e01050309070306240f060509060d020403200103 77
    0x3003100d41c4840313424505481e54a035400300000da48074100c100c0d500d07007410a0000780d2000150414001011000480307a00e85010404502e80302c2c0d86c0520074941c031f103004102503a04401540c3d030182100d1441341140c500c0c0001141045030a04030650b1140c90030003403046400302c035885541a076040e020009518010898182d80d01c80500788000d5050388284204804900103001450300701d442400d190781000a56000a400e20031460800c00004960000700499038201e405402e40000302600c41d14039241c1031588194030303040300640c6090300c900d040c00401c0400841c0e802c0c4002d06904619440911005032800b400e81000c8801c89510403800d002c0001400d152040101c00070000d1034071604420f9041800645850b00000c100d00054011100d0000214803140100030904c00c2c074102c0c0540080301c3e048061065040e81d00010580c1d000c000c8148550758114080b10b61800e8120f40c116142e1321800444006840345030402403c200c0c0c1502c42010901d250039407150400401d1701e0611044003404198 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 181004001 1250 181002751 181002761
    0x30503043809010309020a0e090127020d02040b191811030601050706090305091e09090a0803070e0a0302040e03030f0906310803011212030606080103020603060d0b01090e10 76
    0x101410040011a2940d80070754131900701e5a04c00342a202c820b503a1050000d0f8000002c0b60050916514bd0040054010048403022410300c00684040084209500812805540d6840081c081d0390b40d041d80c03400d41e640d02c0281071002640c4442e03c00e0300d00e032071f0084000b081c11003010000e02d481c14504d403000c0300c24110040da80308100603503d00b42408100d0f21982e0260400c02000c0e020b0000c00c2000c44625201e2130070484d000101c4907170301181c4580b03481c140142c40d10010706041c0355400c20049080010307550700849811041c54900160044111070001b2040ea650780d00c000d5010785081000a06c0b0040031014520848444d031070111207589038942a615010211003d54454090700007081d030a005c0310340c1c4c101c881c005a19074246210705640d40c41c0100d03442a00a2010f486805d00d10b00200501103001c010700030703040d02c2d0a010445c82c000028001040600009115010200003c0c12a03190702c110502c00315000202c090320303540c1d13804c1d1003401490703800d00c01c03c1c450080400884844400d03010b0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 181005251 1250 181004001 181004099
    0x40c09030b06090f0c07110303030903070308180604120e040216030206070e0319060b1002010905060c04080d08130203070308091314070e0a0f0602060a06080d0905040e030403050304 80
    0x41c02104d540c2e0000246034603404182e003103548580700044414280c604001644c41202140c0042d03559a16505001e0700d489802880591048003071038801606140c0410aa034209501a610480240e52000b09664a101408080342c1051002c107000110590314600740d0845806030b000c1e0740c5291954441100c2e5514040051a0941e12241c03020300d840c0c0c0003480c104540c0340550741c0010340d100e0110000322801484030381c40300140e446054140c244401440841d4001e108260390601c1c00d032510b02859201d40e062001c7c003044c40380d1a0002052605149444207219034018266000c50703840b460000c10940061005500925042ca01d01030306c0c415a1040a2400020005110350b0fa41e813800d0855940080003070360307508401840400281ca0220103610801342c801600a4442442c04010203007c6964690010400c2d6104840320b01d1010340001e56102940c000b0780b0049407050780d4944140c614440c55000605901c00014001440a4400c0ba00c50000c501401d06405000c0e0719007510b0803545034240 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 181006501 1250 181005251 181005271
    0x3070228090207080406080906240d02030102280e060702060d0b0904080a1701030f15110f0304120203040b0d0203040c0909060e010f050108070501050c030405040c09030b0609 77
    0x49060395440000584084038401403100190060715150450140d03002584101d0f075110002c5414828160407030801544141000000c10f5280b801002d0402c40341448a00c04070344400c10011100b05442d407200f0314407074940180095588100200440c4020080c461080e100c18012032401004c40b481141c02c604c0d1110000c200a0030021035808016841d88035801149003240d0354a160b40068031241421807003107000c1c4072015100e2118000150007413258100c04440700c08203500500000d45146290500180c21020083c140e980c0d44001c2c0c0b0041c4801640c005503600080780010001c2040300007548114801c0c0603c840344403100c2c200b030380d4070700031400f4149804d02c06202d141d842c5000c50380911340c0580500c5488003000d903100284001c40350440e100356001c40c1c48a201c0c800c103c01c24044c404d0007a504030803c00041d803400e28100d48030511400307201e04000b00010b50416810301003055078080d00008004120850386000080c103861458802181c0a90000c1c0020341f0300e1500621072440355030707061 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 181007751 1250 181006501 181006519
    0x120c010201060b091806030102190f0801050409020a0b4527070309080d020702010314060f0105090d300f0801060509030f060a0203060312210603150a0603060e030702 73
    0x107001610000717008144030381540d42804524503602010030340e0a01b100c80741d01c07000040c10200600500c4450160801d901650800b0103080c01611210344500c00c40d6070301003006031102c580b10300382d03c100c5030003840031a004440075075184c0c1c80790000c0240e4140c05c040c442185103040844018803016030f000d00804140b14040e0107204c070100491082e040c0d030144061500207005c0c4956504d002c0d203030b041104280300340795001ca042c104558061140c03891541948000d41880e00e01a00000d000c4600c0b114a541001004600d0180c02c0e160003501440159001d030314403070180482e441e401440703480b00c21080b17044070304000d00c2c800342c0b8081d005007141e1240701d84e10540d40fa801c0401c107440341d510188150381c07d442142c000c0d004c3d240040c07010380d000c4d04003814051780d241030040425182207202c0c40c900000c04030070021141101440f401d4046500140c1d046898180e9895001900300805c40b01a5200340440c05d040214011a640c002400d51780302c2d0004100000c0f0b51400e6a42da4021010000d4200e101c1e1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 181009001 1250 181007751 181007779
    0x1e08250c1203050c01062318040809010c02130c1e0e1005040810150503030a050909041a0a0903020709111b1608030c0c01020d0c081602120c010201060b09 68
    0x7000940980e203010303003001490a52007621842c21200e0030b90000b51101c00b01d40b5031101212041000da090000200c0705051103c1c02402040d2100c540600002c01d04880012241000e90103844a050f10030f0b002080c40c80701c5414211440003a00304881080d00058101c001143c054400000340a400055a41c5400c00b807140b94052118048001003050300b407000c103000c001020341e03081003000511418140d010410b4010b900b0810308444850300500e1007500183f0805144650080944400d030b44200d8942c030040d240e03400c007880748180088525031220803400070005100265042000d801e0b2295007100c5003190384820003411108440030074010740000300460314854145461405003050f038801a511015140c0d600c0c5d5100c1c0c80180d21044032500301044500b10160300348a081c0084100b80050400040ca14100818001c0c4003000146003072004505203140c00c400c84500c620b0145d001c1e0007140f1940d621588181d0b0f980c1e05946c011b006600302400420b8990000c2c1c165400640301130560040d1581e0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 181010251 1250 181009001 181009019
    0x312130f150213080a02191401051e030f010315060f06261317090604050d0302030915030105040509010c08060f0102010b0907050a11060c040905041e08250c 69
    0x100d0140807401c0c1d020700440d03402c1d1a08203403020092a440c001410400160310502c99088602d40c58040c00c80d1107a001005000d05040c092080442e003403034160750710b8440a40c40810340400d0392801d05190340100800c0b10415440202505a034011010180c01444200c03030602a03c0c100d0003100c0441c2e05103441085981d009000c01e52864034051030b100340002060040c001c08150403100701c86040000120390302806800304459064034140410349142911410210310f02d84543e10801c0e02031001289402e00f454804d200355800b203140202000c00003c0c0c0c61844034419003080c09a60701c0346192602040318002c1c148075030081301e01c6544555113103943d1242000201030744800340b54195521010341521a81d543c040c050310564468a80700e4403000c81420051402c090200040340030780c441801c1c0002e901403803096508542c0d000c0c401003640c0d0364514241b02501072014820300580100400102044aa1f07006011010032690190450307030ac0200e1700407403100c203114000d4142c00664005000c1c8101c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 181011501 1250 181010251 181010273
    0x507030302070b0a1a040504320d1806031e0b03010b12060a0617060609071709010603110324060102010b1207031e031707021603050312130f 62
    0x20180c28010b06085681c0c941c94981c41d81101c1201e01582e4865948071000c00d02a880059428191002c0045180580e02e0701400e605000000007200106545401c5031002001c040049803542c40a940755030880c450041c0118180008071345c504102c1072008500503100303204c0c2d0403000c0c280e9603001140d40c0f590701c5514010010361030750039015502c6417440885529001c240c8180d00040000a1141d40340070301840c8100c40f41500b10346040e590700b081d6183c89000c002020754000070110f41024482d110b20304251241e84d465031024005d09070729000c00402c51410b5000344e00301c3e80222120307940c1030003900405031038401604080d05d00344601d0000080c285c08202c1100d5100406000008a83c4458800511042300540c03a0450650180e80d0901c00c010342012120b0b00b108144180b400820002c1d41d01a000034250302c074a9004c0160200090300c0c40e4400c01c09400088080f0b500452042c1e1039050164481e4402c1c10034807034400040700461608401803924030016500116034a03010000c980d10030740101 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 181012751 1250 181011501 181011503
    0xa0e0f06090301020414041b05030c0d02040306110a020d020d020d1d0901032001021b0d0203070e07020313080f0703031b0b0a0204031e022b120203120a0209100507 72
    0x3000501c519082510244000d1003d481c040100a03403d0a070541044191160b41d41c1e0040fa0314240042c2841d00ca030050b096a80028100304000d89580284115800a015590020f4515410012128a11582c0c907000b4956040d0560031754840c1501c07800244d80e80c1c846d0000380703c0117a0020810f0503101e80714034401e1801d00e994400c1114030280440000c2c65400d000e170800d40f00140e44039140d0102100c07100030034a6282003070001d480c2009407079003503040c480341c034001403030141c0030792a00303101155000c0c00400040c18002c0640f01c054107060500a540b900b105440d01c090740661640403c00d0a8001411980c00d400400202445815541c00b02ca00601d9513100000707000d003e02c281c400007040d01c0d07101c42c8121b010300c00050f1680d01d541800c00d44115a003e0505164a00c2c030703501d00160701c0d41c041c00242c00c0341204400d06440c0f411450b04201c50b5041401410009005d030349108a550b01100600ca10081040b110600d501c802c2043d030f04038401e200e000c9500a443c9140c540700140540f010300405 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 181014001 1250 181012751 181012759
    0x1090303050106031401230a0905070807020d031505010302070501020d1b0e010c050604240c051305010c0c031e0501020d0b0f120d1b060f0f060f0b03240a030f02030d050a0e0f 77
    0x60356a4110041a00c50952f03008003c134a1940402038116030411129140f544035150034820900b01c9036003803a5440c082c1c040c0c03504040e000186901403003025011100e0800c191441001003060400c4000c205903100000c030030005003141c9440308250b20800b1500d01c004c1e0003001410fa41e840707603900c103d000c22201702801281d140140086a030540390740f00b03804e0100f4142d191180e035030f6000345004023100080c1e00721605215050b40d44a011815000305001178a5200440f010410b07160303141d82c8980b084032500240251300000e151401d02d12035400062960ba82920003810081125040200852000c40a03503103c2e840003200f0344649101e0a11010240707107819031040d0307183d065181c000c190384002c13440d5014261140000c5500d2001c600c03130000200340000070241002d09100b82d0b0030303251002811440c2100b42c0c01510398040c0030203a049800b0118002c000b0400d17150760b0300d80381101004614040c0d00c2070040c690000314050269044501c0f62402c5c5d91161580001d8404205001c03118160035600 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 181015251 1250 181014001 181014019
    0x30b0a020a1808030409050714070303090305040b042c1e04061503081305041505060c070f03050f06070e0901050d0f020324090a0c060503040f02030109030305010603140123 76
    0x70504488840040c005000c040d660380c5c3c2c1400442e50075200060005030030440300302c01c65149512010280e030200c543c035150100310868507007400c0b14107004036000302d0203804000800040244040201f038928400070702036030266181401c80400c441d01e044443c0d50700406400c640140030603500b180c066020303105650008a090b401d640d00c02ca410865001104d0300940012a06040051041c0f01d200034801124140000305945c2000c40e103042143c420940592030206400215810074041c0380054000c1d5028442a503950341420390303580c01d40b8080000e20703001e0b590200b500c80c0d204c2c10240705205405800e8020301e0346420103015980214910540d1a030907400f1507440166003d2086441e040014101103c0f8614102c410700e0070303030300060701411a50b030044454400164180b200030381201c84c5800d24545035515414404040c0e8039111000b5895460401c487d800c15030164002030598040d50b03001c02c0418005282c00c0710040d8207001d0000003001a280740d03081040c00c48402001140c02600f1131103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 181016501 1250 181015251 181015277
    0xb0a060b03040b0a1503021f0908060405011d010908160521040812030108120c030c030d0c0f0e0a03260c06070f0c030e010813020310050403090b04030b0a020a 70
    0x180c0d400035142142c032040010f0520041c00010300400d0481d10815a078074010520710742c0002c070300e0140007072211301144511620058a0380504402e03401880106c0503504145440d01e4500e000301070512a4003040c20b200190b9490b000c005110300da804a40c4031800030319102003a0280da051400d00e0408407034920030750900c0d0a4600c40700040340d4005c800c0884460312030b400e041e0a00d0518658a0380340045c81d03810300c01048182000101c284101d480740f030144c0e98440021180a0452050302100030b0345d44000900026411140c0e4449950032015503119a0485c01048044450012030340409600c05031081c800e00c041203089070521380401030135542c550401140404100e25802590001c4d896412060030448241c0c1c1142240307200030090302e0510100321250b50050701003164000c0f0b040c1080700700340c0054115180c910f1148803090700141118981c0803e041107001500045500b10001031603510b001480c0700c500c40a542c10b8a41c8002c0c080c41aa035590340c207030002c0d00620010420071001200b011 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 181017751 1250 181016501 181016519
    0x100b03010b040605360906060a0e06070c030210020607080c0a020c1e0d08090f100816050d0504050309011d0f0d02130501080a1e02010801060e010c060606121b0503040b0a06 76
    0x2185807405c0d2441c1d031002010300c4c0100f1806a00080c112400b5000822031203030160b52002a2006c00c08040341c2090311ba903403d0912407500c90f02c42c0c00080d00208440d006070b4075550001081841070265a540d9a45503442205d6003599015464119001d81c5c0181d030345541ca464040007074501d1074400c14541403e10380140004007046c0d00a101520301240c00120f900d11740c10300010000901005a03164903810f40c0904d802010301d50004c2403000510f5500300c26005e0343e80726900300c6000c00c0405405001a081c5800d01c0d6459034810242180850000c03400000e000c0350b0070001d01d00b41c00d0000d02204c0221800382c1480810904200226401b0314042c2600d090000e031403060074080d04c1e2500c000c0080140c5e40c94140c0361840100c200115000c40c8501100060f0b0f84056060f040d600750b450824007104203000181e0345d8442009004000070300313085002c00e00e66804141300c0044c0c18101e0051201003203650443d40704c002e4050020380090300c05c04c005000b151522044503002941c0500c00100990b07200100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 181019001 1250 181017751 181017817
    0x2010c05010b06030c0c0111040b070803040302100519140105010915031e091a10030204020c03130e1b070c050108041b0e04020a05090601020606100c0b0f100b03010b040605 76
    0x640b0b170505000c1a06a0800824412541c400c0440c42c490740c601030038031001c00d0643c010720300010b00c07004000000508140c403e02410120f1302d01081c09100c0f81c01c0404001c0e5211200303c43c500d0400b45002a801c1c00c030300f180380500e4100ca0040c1c6650b0340072410081c1115000400c09040c20505844440c0201c000d00d4985090301c0d6071200f25000980c4a00519089025100d0f9060034002108004144000b14128144e440212075040381d00584d1009c1070a4103c0c1540641d0740700c40019a052840014048403007040c0314400c1940c01c0d101341529040300d407500c040d80210003000d0301881c006103060041e940542500c47e00030713009040111000245500760904d103106c5401010b0014021014041181000d14122015001c116a15592444d100c00001d60719440100f82034441d80070b070b5122000d054000c1c00c0b203040d407580140d110410703483d1030741d0822040c202c20345154074181e46003040020301c86100e90540f4141c43c0c020300110f2071b01c0d28054084825412000400440d444040d048502e0120038400c6 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 181020251 1250 181019001 181019011
    0x1707022808150a0507020a080f0711130504030225030623010305100f0204080d0f0e0a0602030712020a05061b0f1204020f030102040f06030e070b0c0a061503020d02010c05010b0603 79
    0x503400310710f004402031083d200090041d0041d544030640c0300c5c0020720141d00340c0f0440604961071035256061400d1903044204052442a0049004400094416a075400031841180241c00b2107444025806400c0d030741d05282c0a40314044240d0b0101800083e002d43c2180751854809001402409031707403100209030800a0f80100c070079910840d4081503042a500405090034408001181428078080542e034589600000750001c105900b105240d4960103020f1083c600100500404141621100d0203941d07070740304000580b075240001d001c10310410b100040f50705011794040c024103020303290900c00e04c8004400300e03a5001c100c1414401e550180904401034019a0005200101182442d0052100c0c04108440c0ea070f0007640108004d118039121003510108907080ca2034001042c5002c0e52140c0e08210b4039400c018900000040c035110701441c00a50f9070700c101e014003010403002c0c5502c280e8040380403582c0f00007500003110101c41c101541c06440c2c1c596616000c1c03400402c03d804000001505070b40700302c0d8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 181021501 1250 181020251 181020283
    0x3100b180301020a120e1518071e0f050402030c0403231504030e09010e1911070302010c09150903080f071b0f0e06060405150d14041707022808 63
    0x2a001104049002d24070030b008a15014100da00007c58160303551110082c441d4202c41005a8204151501004040000c04071402140f40e4098544100c40480c102032044800d485003180012841d46041c3c82101d0091400183c0646854510794032401000404540780300500403400511384040d0080c401110224010741e180343c8030f49083d18000c4c0204020040480c000c11450006010545a607800b054001c401c1058001245541120220180c40c100300070048249012414008042c2c054000c01151651900c46540b001d8031140300c051030780911102d420001302c00c8a0100b0205804400038a039011100300d54924050560f11102e00c090444100d41186280300f40e0100401100c08081070081d141840c01c0100c1030a0040000d0140d00507405140c0c8900700008407000c03013913601170854901e807107601400c1c040d207261040b5a000074801100d003038507030100d8089440d03440d0130003c0c00c8440f1942d0081030032802283c1400d5203150000c0d20207942c41c02414003030b03001c9a40ca0003003000300d5803095080b03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 181022751 1250 181021501 181021517
    0x807081b13050c07060c0c02030d030b06090402070b01091d070e0a18030f08070f080114031501080703150509030304060b041e1505010e0a0b07051002070305070203060c03100b180301020a 82
    0xb01c0d100041b43c1040464104002c01000c0c2d201c016a8041041c01c0c102005140100342c521141d80000d95078455100c8050740705100240311410010070042c81c2e812145116010040001060103624014089000e206140c0d00240c005000d1300c0600156548c00000d1034000081c0d2541e42c40104885261008040d408500c5843c00580125844041280d014400340360040700100f007500090241001030250050003603070324001d456a500d0800032402000f40601c41920365581d02c6080607103403c0b4600064440da0803610a50040c1011401464001c4002a0003985144d580e0f88859004204121340550b100b07488034144041d00207400c50005540f000072000040d110084071800e002070300150f200134180040c681310b401c4181d441c240c40c0c1c1d040742c04c04800c1300c0e41c5280619115080040408410001600c04a420030a050344040500103c1f4426011103c0e90345035117a0319440b0340000c994044194a8010301030040240307501c044c020000c0c0400d003400350044c00f100001d081e40c2003402503c0c001038902c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 181024001 1250 181022751 181022753
    0x14090a06020105100906050a0302060304061103041406070503150d060905070603020909090115120305040503120c010f0b03060105010c0602040e0c031e0105011e0c0b0c030109060807081b13050c07 86
    0x304c0703480c0024814294100526440c110129a5100080c44040d21840b1301200040c140320b0f00d0b4028100f000c0c0307004001da0350b07840c1903d068103801c040c440c0303911160300c12480040d00c41806030045034050344c01042130310900c030350410811407255400341c03040340d100307441d4002480040c1c400c03c1210040c0c100c5850141c1c0b11560b4500344060105c00402e19280c45e1b051651074064080c00c03412040c01d43d041d0303a452088442040c00c0954161003940e110580520400c1c4e24908142d050601425a01810b24000d1040d5401000440305848203101e03c00d40c941c2100707004201d01d40c02400c03c1c00201c0c0c403652002d806d0030350702e1135807103000703502105c5000104000004020b00c100d0172122000400726019081a5154100304c0002c2030703a074003203501105e0b8500004c81514005d004601c900c40050340203200c402285012145407146030802e01c0341950103420900041030a6a012a05070250340007100100001d01c241c6000140c1e0440e680d01081d0007240c9003a0401d00c841d243e00410b480303582c804000981e80e1460b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 181025251 1250 181024001 181024021
    0x90c041109190e07030b010c0f0501020304030809060601270b0f0403020a05010c0c1e0e150405090c03060c0f1e09011206031112010612030201090c05030604080301030314090a06020105 81
    0x5900c0c52082c1041d0001805039000009503076810444510300028a04000c0700182c0e00a002e15a02070300c040b10240324a01007103015002140310f90b10907500d0100d00d403201210035903900c0003a2407250200300420003030100703008003418240d0496030844103440034642d50152503c480c3e105050110f24000005824015030500a54020060000b031801c24490412600c4005400a40e8014030600c090041d668020042c01d021b091030280609040e40300305414400780b031000311108546418040c270706060005003d40d00c045080c0c0104980540507044c190f03115211036200307a100d207920386001d1005028400d41070b624000c00c07100b4298014415950340b926413002400030b404021076154194104181400010074020342d021034440c050380e4202600300801c80a6014000e0344e0062800005001d08a07028140c0c150026103981c0d0107031004488050b1a1401c1c56228501103c011f00240380030001080000c1c031400007503103003014240f042070400e02c14100244c101101e5a20400041c0c1d143c00c144804002 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 181026501 1250 181025251 181025269
    0x121505120f060114010504050909011a03030c030a032307051e0412060c0309150906050f010501140307020a08041d0603010515040c090b04030615080d021005090c041109 74
    0x244600508001d86190405607444405019036161342c10250710394244c99010300c0555018000040c0308501600d00441014020301c01c0c0e40030f031111410056004003a90a000c4111802c4060f2900618034080b08007509a003d00120b24606201828088841c110450b112100c02c0c00340d0201d03600c041c1e407880f00345c19006030403820b07070754a816554081000308000d202d213404001203160700c08404a0300e40d070b012070107500400c89008050300100802004100f4034580f61321001419118860820260315004005825a1000d0207494041080c0c0f25004001c01846005075074481f0203441190000100760741e03898a507411a85c00341020f80c0e09000c0c8404d54030140c10705070740c2c0311758150300800540c54940c00016048520154441c016a0303915001c43c10320384a040d902c005010303481da0095660740e4900d040401080030141c100c0d20780807010b80205150401080d50802450b0980c014625600441c1d580c100400000d0302c1501d0b1441248500000da40303c0d4020100c0c205142d8882d03503141c0c0075000c1407002c0c0304 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 181027751 1250 181026501 181026529
    0x20322030f1a0f01120b1e070206010504140412030e0a0818040606020a05070308030a0b0301021804050105090106050904020d0b2d03070803030c0c0c0a122d030807121505 75
    0x10070550010722924545d95066001a5082450618a40c603101c660750b03080f400c1e00064241c412090000c0000103a00020064100c42050790100841e510b140e07021000c01d0019180201104003200d2203071a480c2c444c0e002429000c101c4026911011101d070b444030103981c020030399140740c0c0c0780f4000c4034686031070184111401400c0500240400120301e82d03940362202c0d500d0000074544140403021641c4046142d000081801d00640219558003e514481174220030b002c403424452401d00d07001095601303042d090513040301e035079454842c00c00080300204800783d0084805459190380c1c426482000b0f643d003240614078045407100c0314102140040c52071484210f502825400b85e44804002c200c448000021241d00405c4030112949076618641d501d41022403490409510205182020594504891140c20a00d100d1080e008542418200816000750890000340441c00007010300c5000c01d000d240d649902581b40d00c2c21703141d12400521502c040300c03004200081050215403040c4203c0c100704101007192 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 181029001 1250 181027751 181027771
    0x9052b030b0a080d03151703070b07020f100f0b04050705070b01140117090f07030b010806060a06090506030402030a14030d1a060306011d04050403030e060601030606020322030f1a 79
    0x403d007081c03001d55842600d0b042950415130b43e40f0741420071140130291003001c0c1082a500280c441c400380c0f9403696a401c44030045d034022480501003170405000003a41009203021780d0181079030400a5038004020485603110160300f549603607580382c05c0c2c0c0e140d20405105000a80b0b60644820b106d0600080241d41604050f910f4003501d80008016a0400c43c45044d50200340d0303036206269100e05503207083c04464440c0c2c0107140300321180807082107a03854144e8162a01c1d441200e030250345000410120004910544011071110103003400542480c200960340940098200c901c41507103680c41c1a18210622402a06904042013003c80007556008001c5001d003141c0c0259084030304040080c0030f43c803002d011103060045004003940100d0028071020303e41000248100b02034580b07030030058080c184282d00c0760010701039100021001e42c028441d20302528000d500860408042024520644140d007000d940000d0018000000168070f4120111482d0311038007064200c001c180b034850544c05030280000d006 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 181030251 1250 181029001 181029019
    0x80115020f0c150705030706020714010515121507030f06090510050919020708030109050106170a0f02130f05040b01050309190311190506011208040909052b030b 71
    0xc40074001200d48441e0402c9590b50a12803165940890381d03c030b049001400350001040d21400d1150b20740c0a03103103150151009103005400f8940e014202d4508a03118008031150341d603203510701d040c03004082d100011100115040001503204817620b4140440300040080d40700c01a260700510303940507a100034620028207010900b0710703400882203a00c080c05850301480e9010002811100700341040410012001b004543c2c0b6400c0c1d042c26603c680c024050b803080e00f424540002039840c0310712509121141417052000b26515050000343c0685400080d0b040040d07001d0004010308015003c240004110818121401d24070f0103090005580400130304070305001d000d104111400002182115080c9030281035090544258601a208030030140301d81d0115100e0486040d1428030003100d1001d0242c051801c5070b2643c0c0e039411140a03000201d20008004400500040041400b10b0b045108202c0c41b84081c3c03000c012149071408100400c4a1045800c12910b81c1e00f403480a80610500049190984013201e0f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 181031501 1250 181030251 181030273
    0x1120209030309060f0f03040b040506060d02061606062105100501050303070f02060409110c011b0c0b040c080102070305031009020f040302061b0618160311120f0d08011502 76
    0x7403030b4090f000b280c40c06441e00144441e61680800106d40c60000c08010740e41e141e0420f410040c0342c1c640b0444040380c551150101151203490000c03e007021050b40184001c3c0f070b044407400c00d24261540b4020032240651690300124008210300c1d5002540c030513040d81405417617079a040c00c900c1e01900e01070071000c2601e4000107002d50341300402103406168002404880e540000d01c040340885c0f150354002111246004c102ca01c410b69444010556281244000e00042c40384807160035005d464400e54001090f503804511002032154013249511034004d1560644a65441c1140c0d800c0e131b80719a000f03c2c0095800400c00200340060000f03240070300740c3e1480842c00e040003031042007100d200f98000680b0480740400c200301c0d5299120b5400a48095081c00d642d014105201b04e042a214000c3c0002640c2c003484035056414600c241141048a8210507048070004025051017a46014200b080e00740b40100700c14180c8200e400c05c40046040c525a40b40e200b04d43c03420700b1610110303103060388400454000e00000c0f1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 181032751 1250 181031501 181031503
    0x30b0406090b0303030402010c030e10090602011b090909050304050d0b01060f0c0b0a0203191b120504020d12020a060608160503010c0e12030909131106030f01231e0112020903 77
    0x2035106e5420300380300d00641094141a1200b84249005907804134480a5011b47c1540c00f5a03210102da034941c000380240b20342c41001d0405a40054010b0000410321407003000100007a40004400c640a081542c3c0740580741c60100b8002c501d400425110f0811050042200c5980514003040d034031403500d001290740c5495a60f010820101400440200ea0040040303270b40c0240d800305100c201c40e140307541001651049011401107031200f00031040031903040100c6e520121054025103100b2640201064440142076560500e802c0800110034114820181c071a800a540d6203d420040d0140200406c190b080b100c51083c4080d000350045030190b4140b2031281100b071740080c9401d0000000325171032500790b1010101c1520798095101c2e100ea002070420140614891001a1000c005019220b1124505241c10600c0400c2c442a01c074407114a030702800400821401c3d43c18405545010b0105000001c0040001414103100d50321440140000f646044a250f03080603ca18056842640550408460800003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 181034001 1250 181032751 181032757
    0x411010f080708070905061c0f06031e0501090c030803010e0610020303130212030a03050f01210b070c08030a0e010b0901050a0e1801061e0e19020c070e07030b0406090b0303 76
    0x42c140321040c0302241d80107000b04858006084060306180e2031740020008801c00003000c1c20700814042c5410901084104070340101000e8070703000000051503107611100721500402d500010f590555071005c100380050031483c0218010760280c000c2d65120350600c00381004a410141107107204640740044425149d030080152540b048040d100103404071803034008103800683d030301c0740b03030110303000000704034600c2da070903500050080074031a90a078010307038860703501e440700141030302e0808070708000f040304440040e617041510350b4801d0b600c0c075186c0304250f00ba540390551a041950541d00403030300e0301c0c0c00f001d00340c03401d200320f68010a08960390780d000c1d4581001f0070040c0e11075003d50380341e490302072000407007418880280c0d030034400801300204031083d0b9580000c1095031041c0502401a008900001000c42c0e00b081c1441c01024a01b18091101c0c100c8403400e0b0080d40103803500e05031130050340000140541d24032415481200207490105810300032108001c125080f81d080104180c2c6425070500c070310344000080d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 181035251 1250 181034001 181034011
    0x618100203040c14030c120a1e0203030304080a0201060308121603060308160314040305061f06020c010833011101050c070201050a020703060504080a031b0c0813050303070b0411010f08 81
    0x1164802d0240440400c1c00d11b035190781d03007603041480076440c003550100c0045c0c1c40b0400741c00390100301c00c00c018420448142e18800350000c0d605500c00d20229000c14260780c0145481c0405000016045031760350b440b10101c0c1c001c4101c401000c5400400c0109103400803003003c014004601d4108109400c40d034074410b143c001d20010344d0b0103a10000d40e000c00c16016041042c19a04200a01926503680b072034950390b1303039908641101d0300455006280d00b213107031818962010b944503500a82103060b00900111002e14000342008414442050b465a6200b0072110812003d5204075001c1090b6400b00000341c031103040c06006c20100d80c503080802214482030b40a9038842542482c096542d0b00c03500d04c1c12864200a50009000c0c5442c0000b400300b041b2103079004058100c0b41c1e032010300c1495901010039040b441201c2030000401c104501580000c3d882c0d100400f4100d1984580990440d21180031074503580003240d0803130780303d8043c809100500405000d40a04010240307080810700c88001001007202c180034007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 181036501 1250 181035251 181035269
    0x415030c140306060f031906170c011412040b0f01140a05040f060b030903090916020d121113050307090207150e0c041a010f090f0501110304080618100203040c 70
    0x7000c43c00c69600c050848100c06000d07410b0540313a085c07070f515041403071a00c04204170301c06182400001d00030100c80d0310024250b41003000780098000400040d40c3c480c071a500c0d0303024000010001c10818100030003165001c0c5020740103030703402482c00785000f403540c51040e000302000c41e4000c250a039681d5121b410350029140165408030b4030861100c8410058201078015400e00f420120400004100000162103442001c03902e0313140949a52200e805101c2e42005030000603040680003030819030180b04580c229142010300010800d1408098105e03a4000c40203400780c48140002c10801840c003003003944045e0081201c210716042450b07a0701d943d664084001004002d407685000155501c09001c181c2d01c0400180c0103018001c1d203846042110108441c059002c41c100240240e0450301c141416400e8a1030411088120390600005445122940000c84010b200030080401c040c2000c1c05003501514540e107000000303024100341c0300e0030300d100418403030002171040c401c2002294100c0144822901303400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 181037751 1250 181036501 181036507
    0xc0606090603120d0905010e0f0115030c120311030a1716081803160b04020117070909021602030d051e03060307050f120d180801020909040305090a030f06020415030c14 74
    0x4013400041d020349800909654079040e50340f0b503d4040850490300151a00c0002c128401c200c03460b001410a141c00040c0084071112000c1c8406001c500d00c1c0c3c880140281400800150290410f07072031a48085010000510000c9003400d0060101c0003a035003115441d8030064040d010140020302c030480040400c107802c003902c0d103040703401e2206004640c0200e101310913401046840741003040a28034203840403400190325220b440039910142e280c5500411060b070b1020407040c608440500650441070b100b83c101001054030000507501001075460140c030545a141d1603003000190004002e41c10180e43708001001c01c1005690382d801b10700f44003521422250021611241e5000c90410f042003641c03c03007203119a6010b881641c0e00a10228000d101c00d6603201d42a07529050b0305402d038011041c03116009412480460000380c02440a40008070015042020050743da84850700386050358103090314415030000c1c0070700c159501e04004414a07031040c1420b000710000148010301403905800020340812000c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 181039001 1250 181037751 181037767
    0x20c0102120d11120403030501062a030806180a0b03010e30070b0907051309050a0206030c07050303040f050714010c030f020705040e010b030120070f03031407050c060609060312 78
    0x360141c89880d6184e0358540902c0ca018a800ba00420081c00303250301180c21540075a410802c8403080f001c400c81d81c2340c01c661200c20980d6041da041580900000da00075035003064405001004440b231407150500140108101d10b903442490300710341051401b01d920b07800200c5240319a20b0201c05d10030310908070502c05000c00da00d403038003901a07002e03001c8000c00300030301d0009200700c03460000364501c2030b0750702103070722514801034114400300315062108000c0a40e040f5451910161408101860f404580403407818031f010340c150b03100c0b030842e403085808441c05084042c0d01c0052003410403941000c0c2c084001d022401c0b0b44160b0001c0e113100d298400040802100c40001c0c0010791081c8070380d000a11015009100c0d05040d0412903000c1d002c200f1031140250302e480400c04110204000aa0704440300000c028a082081d460703066018183c0c0500741d05254482840040c0940c0300ea04640c0b00f00150381c1c402da11448009010341c2005000703050300b03104e80c8084090101555000c03650208000c480f1564542c2c031906 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 181040251 1250 181039001 181039031
    0x10e030316090803181807020109050706030204150302090f0d0506010608010519050918010c050903120301060e010f050c33010e06120a08030108030a110a080a03020a0507060e030406020c0102120d 86
    0x220710001b10412940400e0150b426015080795806520480c1942e043e05d40b141421404c0340618031500c06591072100041c8020350080e801040d4614026003094600310318400070401040160b0b5046070b4550007503004002d41a84141254051300e011036500c0030403910400018840056405080d01c9003411001096140306a08012000e4010500003480303450f910510150064002003051402401000d40c9182c50244020403a41030328021746405030810b1118004680213419a03000d070b0240f00c400c000d5103030390340130401109081038504d01c40040d00c95900c8910140c440c580601d5505040c01050060191944c03103c601039210b0000c0e9040008415401500c1d4a40b01404074054021000000080382d01d071000320080c82001d03c1526002c030ba989007580241d54440803504003507d00c3c142480900c2d500f6101c1c1d00100081442440c11030300f411a00d031204001c682d40006060b200e90301c00101080311503018403000d15504002d0015124144561003845079900c10141d041c140559118007905040607 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 181041501 1250 181040251 181040269
    0x3080306040b041e0f0e06010e060d1704090f05100b0c03040f031101020715050702011d1c0618020a0302190b03070c03090f0612110408010e03031609080318 69
    0x4020000d0210a07403000c030b25141c8404100c0c601059604084032410a00400e000700d0104c041ba42c070081409078a000c01c2c0b075001c98805040d2540c0310074150394500114101c8250075404495402d0b00d01d90343e07441c025082d02119020401c0541050400d010032440200b500e01e1401200c201c102c1f9039039039807a2000361500750700c80d641140030000032192003c020301a0401d50140d404da400e03002c9560742601d4103110046102e81160800002d1410026140103501c01c0072200030340b4908141032000c09650100041021a0701540b05901c11030190815050084038040d4500300c170000c03030000216105640224540d01c81c2404040e014030000902c0481100080f0a403030014811200c2454980c00c0c40500202804d861941c103400160010340e0100d12610303015440e80440f00540c40b103c2e04041c10060800140156110700d2501060600c03000039480c0e000e0141c0142e0940100c060340c0d980c9460f45d0f1024011114544038020030404207401d0103800000422945098403503130000032603002040004074503030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 181042751 1250 181041501 181041521
    0xf15040609090308011406030c0403030e06040302090f0402010305183301030c090606090501050702130e0f01020a090e10290708030610140301120305070c0b0306100309020a0308030604 81
    0x10b40741910300800d25500005150595030800000020740074803808018041c0800d550a84100800700800c0002038015540c00003c424094910b604007a5a5000a8a00c00c41105d0201a40414004010456904d842407503070041070180541d0740c03400340c039081c0342e03850b0342c00c5002181440d941942400a40c95016090100f01040c2c807001c03c2c9903850785005841301e45203108015045003880e001007040ba0040c1c42074015503c06079152810900303247c00300071503d8400440321030301c01d0303031041074180754641031058003c000301c0a0005641c6000c60b60300181104003a51114408052810174446000d1200c0d194800701c9000e039407064a0107141c64180e600d480c00480c1003050141002803260b0403c41400059441118204c981808821040c0c0f4183c51001c80c4007800051200c0800060051944180354070b0f4819000f0320f01030341407104698808101104075009190f100720048100100c5151620072903000b001e1924061141c8002a404242c40311514080104455804000079030540c4555002004c04 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 181044001 1250 181042751 181042769
    0xf28050a080f0403020109060e060a050d0b0a030303021b3f0a0c03080606120610050f0d0609050105031903030209121603030801050117040602030a0213090e060109050f150406 77
    0x50340606207024580d901a110481c0850787c1c629001030080d0085103240700851b0003030000c0b460b00a80a404460301d51101c1d181101b1980d845204d03100a80700c150060307000c0c61298400503074510158400c0d1102c8282d05500f032009d81c6c0128542c02001c80c190001e0449810143e04030304184800e2400100410301c040d080d01b1001001080c00c8a170076900440703641c1e40c1d90194440c0700387c54680c1424031401c1c2c82011b5a03002c50004100100b42642000b414230003000015143c164200016006140c1e4668401840740d032460707881e1700c0c040c0980d0600340f003118014001280100310840120308040c0c0e409000100180c245540843d80d0625901d560030106500800071050300e2000400a0003000541d005002c140c0c00035400c2c0002140550207000c0c01c60003000a80c0d075550003a540d550f6510301070362004000721010754003032110b4281d140c4002c1011001d81700011020551282010040d0714241c01603000c950710506010a000550030010040c541000c40c02c459040c00103c7c000c0890040c1000740d200400c2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 181045251 1250 181044001 181044007
    0x2030d050d0606080708072001090602250201080a15120f060e010b0a09050a06050a15110c01200a210e060a0e10090e070f020f28050a08 60
    0x156030100c0184110006440304101d000c1e22100300b120070110880f4204046200314000c80d110300c2c00340002c40001d056400c0c0080c00112480c440c03900307407803c11a045502c25004a451100c0b07450301000000d1750744030110180286201500003c0c071050024010400590359011415114010f6103844806050040c5110302da1100c41c3c60010803901c3c2900e010380b20189424181522450180518440c060005180101032424241d22100522000c0c003200800c50359110006a640c44281000c8001c0003241c003840040a8bc3c4a000b804611040e003241e481604203d50002e0321ba03030042c100b10300d00e003001c80c04c000c04031001e000145d01c0d0200c9504080d205003101500401400071112084c0903000c0b03d0382c0c403440031b04101000c2c418a4003c403803180e030104802c0d20043c02c040c1045000100e07407201c5490325602a03951030f4020349807030405580010010780c2d450210a9442d03010001ca0456141c1400202103401c84a40c4054070700342070130684002c040c542585982032150412162107099000202299 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 181046501 1250 181045251 181045273
    0x5090c070203010612060e010501030b0606130918051c050f0703120f05160503060901030605190218100e0307050418060e0c0307080a05100507050c10050a05060a050109150c0203 78
    0x14801d00e080c0d2046421b28240304280c91204018056581242d90103080f02e001c1351260001c20005400000301c05a1040048100164048660003000c050004d001044601e858450900a0600400c401c00010f40468000f041840560220480d1140c04200d41229190000783ca000c8444e4070304e100719460481d08010003030a0744a03081c2c0c4198011420b00c1c0c1100c181c0328510000350380500003101d017190f01401c440c00400c00b01c0c405400c159840001c024040d1000480c2031409d80483c0c0040300020016a000d50011156052481d07041d0310016103800d06003074054200c0700113942e8a80720300030f0f02d00441d2214203030070180d1240c10140c1d00f5207610203814400c1d0091030840c559074403418590517109100e00d1078001066071010641a0103560424060721780304100141031006428080e1690041200402c103226001e030050200c101e4014a00801140b10700389040000300b03485001e0b041700e1007548031000410041c0e0304204c00c070088a0240c03925456140c1d0440c011b4948944401001c0c0d0103000f104080300d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 181047751 1250 181046501 181046519
    0x30c0f05010f0608010c0c0b0f0703090b070f0e010509030a030c0302030405120f331302120d0305060f0d020103050a0605041b080a060f060806190b0c070b0a0905090c0702030106 78
    0x39602c00100800c00c25000503800c42d1f031440d102401400030805003000c40e0000c508041c2c110f40c013101030304020450700110780d24281100412134001c00020a00c46250301c3e03066101408034030145003481c1c41407d05141c500001d40710108148003c0c14028081c0504e801c260080c000c0d24000c01c0c00030b10f40b2800307003541000740da121020207400408502501498134500c919501c54068401c4402601c0604071150412120414002401c00d07030b242c0d007114041000681c0e607500c7c801d404101c03041c058060b013040c21030007a040d038074050985803003500e1442141d10151100f010310198260246400f1400e070301c54084078402030405400840c3c20509203002c0c1d100c4501800c1d801d041110141d034401d4000d40d20100c40c503049030401d004008013100c040302c0c1048810300c60546280c00900080007071b120106000b1241a888020b54460f20100e1008501c100a095007480102c0050288236405072a040080c10000e00101c1d0601030b4900c15400304011441c005049015221000e60180080041c543c80302048 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 181049001 1250 181047751 181047761
    0x10e040309080d02070e060a0e04020d1a040303060905090c01050a0f1103070302030a180503030403020918100b101112071401050103150b03010b18060609040612020a1502030304030c0f05010f 84
    0x561018100b06c1d01065003401c0c400140da0483e0700071005100c55131259030130044154004071040c0c40c00c59040c200840c61044001d4a43c3c0120300c65280095400d183c43e0305082601c0d4020001c1a00390400e0000c4075159800804484a40040346011964400d6007401601c0411503501c01d02c905100c040307502d0041680000007010070070304680711003c03401003459078515070f00d04034060560150800d010804c010304048443d150000d580050701e10140f092400f41c1072070100d108048421035500c030814a9030300c0c1042400c01c44074403214a03002910001c05d00240b80d403000c0003078074080041400515402480303000f880214009155a000340550750b9a418140b20b25100d80c03141140592600081001a1038144a00c002d00c0c07134082c1c0303000003800c0703a06007031000100300401094001904200d994a665610321686001e050801c4007003102d009103006010069983d038018014480801d1800309480b5000000d40e0b5120790b043c504030340c41e84c6c2c0b2458100003130044007400511540c01e09a80706400c542c66084 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 181050251 1250 181049001 181049009
    0x9030124030b06030a03090e041109040b010f09021204020d171201050102010c030207030816180303020f0c010302090913020604030629060405010c11060403051e0606031203010e040309080d0207 85
    0x1030b40705140c03525020544c484418460040105048403001c00a00c0801d0b24515071042c0911300303c0c05811802c80208002003030454040301c190003440d005004600c1c141c1ca2410140904070703c1142043d1070310030900b0040b08080e0001c3d1041e449481250100a036103080c0b00020565001e01c19104c0c07012800c01184444207009041c003550a20b007041030294070a10a0751041e0350103a03070b4500140c480c4604000b411404c07040000c100000d000b5102550742c070322641540214402d500824582020006c00c0381422602c0e640c10303040500400c94a02c1c0750b9a00001759420440e00c1040c54121040d85c800148548070b00c1e84020f01490034402c01d48480301c030001d1202070080e181c4416044501c032900030464030f072065004150100b01c440c40048041021421300000c00800907100320719182d140d0f221640f600c41404807200c2c110700c00102d040c072031220a00043e40c2221065005008200f04000050b8150105001711603503400d01e41c0000e001d16101e04a1b020082c003402d41594150701900d90000d41710a05801 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 181051501 1250 181050251 181050263
    0x2031c0306080c060d0e0c03030c07030b0606030108150a0b030618060f01080d050a090f0909020a0b0301081c0309020d031e020609030d02090a0b18040c0302030712020903012403 78
    0x1800180b0407801151540c1c4011000745441e2400d03807000040d00040c42084507640507481550056011500c00300000c0140c103002100130801c5a1071450510038007603008202c240614410b100400181500046840490304a0f4540b024281d4500d0317900700c01021a403c240d58188201c5050240c00d02031113500d9110081202d081e224540d480d16642c8605000a204d0040e0740d40c0010504090305100c1c801405078114185030426016a8a100c40e00540a454000340b03034150307484590104500c1c0800c0403100170901c56422508561400d80390a449160112640c0c8411103102c5032501d0071880781c0d20980000394001e24034500b880503410020b00d43d02c40d44c03200c0343c51b070040e00e240c480c40c140c00010707007a128036200f02c000e500e00310001c10303000041d40003541c0454105001c950082040740e56200a051100c03102c01e0742c0c7d031000320220204029103010400341400d00d8410028041010392200c0340c0203810003c403401603541d8040c0c03004070340103120100c1d480307001d50324440041d11001049a81142147d001d01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 181052751 1250 181051501 181051511
    0xd05150a05030a020a05040c0507050106030c05030118051002130902030405010507020d02012a0207080f16270b0a0807240e0603071d04050c09031501140f030a02031c03 74
    0x1c05259654207031240103540905041300402091600790005600b101d220f01c0c005041499981d82c071420354000d41c100700c40c0e08241880c1482242024860004070756407030094807203450307a03540756240c44008251b682c00001f41c000408021042030318240d04004d00380d041045540e8501810b04500070507055910b900140241c40e0040b0300305105000751080704d10015a415605020b00c52a10790140d440e01c0020194016904005402107007800507440810420000d0941c1d00d80a20081c0c550441a4100c41d40d501290100303140c04e403407501440d54500c844240005500601140009c490106507400107007280b20f41500456604111014ac107403149408000c12202030142c001640c41c290510007058014005000046c80207100e1508042c03c482d02d449000c0ca180e015101081c00e03910101e46204004000003202515424104004804460b800c6d48041c03181d41024044443c89a50004040c810781030107518410750f42e002c0c0000804194010122810294049021081000e0a0041c0340c00f2928003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 181054001 1250 181052751 181052759
    0x14090a0e0a0b0f03030d1a060c0a0b0c03040b010b031e0702030403020f060403020d02060d090c0b0316030e0705040b0105040f0f080f0105060102030d0e0c19080c0303040305030a030b060d05150a 85
    0x100c0f52001940d100401a5061202e5810306100030054075040c0030002d184081d09a07116118280140402029203015044550941c103081d02039600c090300c2148654001c10820001c00c0c20801c5180c10b4406010340c0315660303180d603103400e00c88140520081c1d044006440c180005290004001c000f103d20a071020508204800304121190042c1c0c0300281d0015515190a001032030201c0041c440000100c0700080d00e1a401e4540704058030441e0000420464000140020742134040480100e02110b4901030003450103c607401501d9545a06c41c1500907074680340039090350703801075040e90080d0a00c8840034160b0f0f030383c61a0300281400f00d03100300c2241c0d000e00c0e66950000e40c01130103820300c103c4060b002103181840c0300c100c42005100007841030703d01340100410718503541c2e15001240244a010f41c00e1160b0b5609001c0c03420306040300c1280c024860f07802000f04000007030010041d80c1780d9586034180000d004215801003602d038800c405041c0c0c0780c10324120800580d401c0900804c03000e140180e0b42c1304421078403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 181055251 1250 181054001 181054009
    0x406080a1502090d060509030d29010f02120c0d1b050a2909011b020109020310020a030e060403090915050117250306090c140a14090a0e0a0b 62
    0x285400030301030050901440210071040c0d001407402d07850160006030201000d0302c5420468a0a64010601303400019003007142d0005401b0780740c82c24000e4903032070500901107103c2c0022082c00c100100d050200440e40350003c6070007444028001410082d000e9a143d0f0f61004903620340c1320400c41031001c0307500f1040d5442d1040c4003081d0b2a110650220040043c102262540c5161b22200c0c1c0d01c0c10103078010784125005980c600201c030790244219000115420486410501ca14420301d803d2504680c50303c19248050f99000801c05040351404000594500d1984c10031406009070406d07245861107000103000405500441202c00c03071380c40304010041800380c1205032a0000281c8100340c00524141c0c0b8003d058901c07901020741040419540148450400c2c505264501200c1d807040c0100c4d9440300c5c204030303101460082520782c05003032900e0305d101c401711042c00006008943e0784408010060450001400d01001242c6010748000d1a088049503505048074184404440b1404a41e04000d5086100d00b0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 181056501 1250 181055251 181055263
    0x305160605030c09130609150812040e040606150203070c1a03040305181005040821030c0717030a0207140d0909091109040803061011030a14070c0b030105040608 71
    0x30403980c0346841d5496114080115400c550f8401c1e9001d18001c28045000c3c070076100d21030050840007004035403000c01f040300081821942d0b00c2150f0075004001103525500e4000c0c200c9040c0d8400516100c4161142d042480041c01540c001074482c41c07a15010044640c2c0000140030700ca8414501039103466102e03294040b6421421010303101d03850040c030100340060b001d4409002401c030a08055031403408140001221b200d0b1560001020a20005d4107100849050201c07070003e030183d01a01b03c01d0704140c101d802c0d10f0300c402000c030b00170588007048190400c03405441042108130596440d6459040503940c1000a502c00b0408480e521713208581000000c0300400c80c00c0101d40141c0f104035055151919030800317017100076021507040c2440c4c20060380740d03034854110303134007c50268003041d03200e00d00a0240441b40800584580520202d060001400e92000084460040c0c880c9043c0200c1200070040c41c8844c000c0e890000d10f41d1318685d901045034141000030714102d5808980c10b10940ea80c0300c2c4541d803180 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 181057751 1250 181056501 181056509
    0x706050405061e04020603040f061401050f040203042310060312090602060402010801171603120e0a0b040b07080408010906050603010605060703020303160207080706030f050c27041113030516 84
    0x40b40700f8002005031a000015651280c05004160f10b07a10840ea2801c0844203443c03801c045809100c0014411820a480c0680000c8000d0300c0840ca18100707a21060704460300c8600b203842c081c0200000020a0b04140a08038000b200902c09000680d207915020341c0a2500008210000d003041f00300144c90b03880003c01c107006a0301030b101e902140e4204006d038510540458400e444074883c10b51034550405111000500540c080d144010743d4a924542c0145427004c070300003844c03256048034801c0c481c0002003000c036800c943d070048903150780d8a004e01c0c05030320600503680090829443c1c02c44050030f000d140c0d04214495403045008000081c0c5410420582c0d00134140f0190041e07005100003144c505084015981c240510300481d0030b410303903c000750391910030541c001d040000d813900d411480320501805030a03040082142d0b00c60401e04201210342010001c440c1c000c1902c4e920b03010307030302c29529641e000c0f1f0800d4824803940e40c0d45080300004006a421148001c9031148148241500c0c8100503020791401e40b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 181059001 1250 181057751 181057801
    0x50409140115030e010b0a030503030910020301061d040b061c060e01080d0e041103070207080d02010203010605070609170d0204062601032003030403060b010e3106030503070605040506 81
    0x590740b10021001416081e03450b60032596944501021a41c50454500085125000035030352460580c1441c0d040c0310180107401d11441c01400184040713600b01d2000e404181e42902c1c820403074801c100004d00509500100705800c008001800c0143c15454140b40c036800b0034a401c14441240e031604c0410420030f0074482c0703502580140000d018210708c20700c0000504400200045160b0003941064011540f05840000141c3d1014000b0440c0d04000d020000e0020001c0c0001c6080d580b501201a025119011008122039600c003000c00400000e4005c07080709060500c00360751240d20300c020001c020342c814001c00340454000c19140000c5500204002018509150401216480c66540d2203080003a4074250300c124003c0300c1100259201080500000d44c01070502154144090303002509111700410b006025441240c00850f24a00b0818188840c170300620f409000d2080641c0700c10001d081a41004195000003d90401031141d1600007a028902500030b82d45951207042c00103000c460001030080c98 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 181060251 1250 181059001 181059029
    0xf070302131104030221071d04030f02010212011403070923180303041a01050105130e0606090a0807061701080a080d0902030613140a08030a150302100504091401 71
    0x906181074000c5002d0956031920641455101d1340000c44041081c0707040c051003144050200a694801c04c500001400b0880444007011204142c900e81c451005202a00740300d050101c050406100354115003140342a80c10503030b003d58541d56155a90550248054030034440d080010501c6e5400d0310402c1d00c04103001760000c9a8640a910304690f041c402050f8070b00040181c8003070b40901409100030f61045118030500e000e040000303460702e952231006811540c100a01400850310400c1105140d04c1a01c0364402c142e4619030f58400007807441d101c2e004460fa0000803a0000080f00000058913406558282d2911224035000200244000314240324aa078503602c8141c01c0300114032004010400d8004600010860300e1540e00032914101003a10114800c543c0b114440f4148012400401c11511400014082c0d1030a1030b2104100c41c000508a1802c10342d0f50030012a00560300e808690045a0250110015841c03000000c1c11903000351049407981c50400314181c88e0a14001455416120341c0043d2003d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 181061501 1250 181060251 181060279
    0x1704050d020721143a08090c0d1b09091106090d0303050403020304212d110f030d090602010b0d0201080103060506012705130e0d11070e0112050f070302 67
    0x4540c483c0341140340305000d028001100c40d0202180c1c410b4001c1e50401500c600185100517030440c41801481908010407502480a500390201d442940326004032060101150a81413501c0b044058080c0e007000100c10340c000062400340c0c1e821016600d40120f000c00c1c080100b00302480007074815486e5a6600461001c1c4075000640079030300036038005011f03104607400d180c0c850300315450301800340b15101792050100300d910040284c06141400d00880100b02070f403c001100b0f4000c030a00c019800c00400005c050f03001592070307454030149100020340081c21035102030719025002d4509a10b502500c0c005500300500cac071040b4100844038a0105034180d542c803059a1a540b81d0794001e00020b0015410482810400c10030b03034041d041d50b42ca00001c2c084403d0340040c40c1908124098803040c07909252582861030f400801c04000c84c1c401d01ea0b048605040f070991030354002990600340c26401c042c2854101e000082041e0615000c1c00c441c1710312031403c4410000d46910103aa40f80000d10000b50b0000c50302540300 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 181062751 1250 181061501 181061513
    0x6010e070806091b0d020d0b0409030e1002010e0102070c030516120308070201150306050a0c0804050a022202030f33040f06091a0411130303030203071704050d020721 73
    0x35801076154071884d0380205400912101d0307070302040c1460030f003e801081d00c1800009038410b4100840342120204105421a40c0151110455070685031046c0002e040b0100418000c0d004409501c5080000310b5989010f4a0190840300c00340c08140c0b83e40c0b00d602040f9003441d030103460040a41d0720304d00b24008000115175088614034002051032046540760005400083c12000309900914030550f0045914a002c1909c081201c110b801103008110044082c40003169020541180030b40e010355000b00700351480c03c00750b041c030010300088001c10303440001045060b121f408202806240280c191501d00058140200790350003031803030040c10b42e10002180192a00e0b0130781c03045150716101680400c46070369500b2070500701d03040640c241c06005441300701c2544614180c81141c4011001c4103c81d420b103111070f030380c040c42d00c0c03201c0c08010203056000000c40c00490046001000401c0e45005425280c0351600c0c20741c1e107510000c280c00002d841600804a18807400190040e002080d400c05e14254440e152944 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 181064001 1250 181062751 181062769
    0x70507110d2f06040b0f030a0b06040803130b090105033103020c10020d09060c061503030c050606040608210d05102c0408030402130e010b0306010e070806 68
    0x5180d205240080d000002607240100e0b240c082c90018000c0e8048076000040c0d401c5602910020744075000400051241c40100825190450003103d0f6040d102c0d5200441c13a002402e07120000d5500c030704c0100340000c1c0c042c40000206043c1140b000c0d0900c8290340e036640c02d060b034080c0d041454041034003480084c420508040c080c605061691508400002591640f040307980c501e99015001a0411d21000c8483d0400300e0199007440f18500c010702c000180d003c8010103100031405200208020449000180728080e00200011500c4d40c90070110659a40340c068000354100c40110751130f00a0b980042d01e2441c2500c200b00480303101c0000350481c1d10b82c002030385035541c802481007402d0403801e101e0401d42c07289901c0b070b42d4814100880b02c41156420a0b0a100030141d402100d0120f600109051003003001c0b104401ca9003180d03000b1714142d201c2e2110300c001401c11307600a0f9140701e528640071b541500f21805400100d44460b041d8191281644c881850007502e140454000c07020910744808149141011003027 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 181065251 1250 181064001 181064033
    0x913050702101805071a041a040b190806090613020703053108010e1b040b040507020105011a030f0403080415091a090d0f03022b090515070507 63
    0x540d81d1110406002c03a04032401d405105294000b01c02c804410043e0403c80d070009410903495800c022109200d140106100c1e43c02511fa02e008130a07604082c0b501034500796005480c02000d21507d49a0360703580b50002003041c09d140000100043d02240d114102600141e005c2c007005069942c4403030024001038080e5010941c1101003041c100182006005c0c509007402c9040d1024480f004004c022900c003250f130701800d800c500360692400c0380a0851200c00987c50910f22100790030540d42c1c00544000500506a11034620b4101c0c1c00c203001c01c50211303811f50105061ba96441481c007810010b42d0326044c0640070880da03400003034030700f040402d002c00c3c02200410f0344244640b10501b03c02e10006101c1007992075240c4102d40900700c0d0050b1100000140000a9100c40001c0007801580f0701501d0042940040d01701290906a000580009120078641040b9034442e007003078416031880c40389100c203004042000003920f582c021800700050002d00000c006018003203d0b600c603402c0c0101622510510146410 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 181066501 1250 181065251 181065253
    0x30a0b0a05270a0b0619080c0f1503011e0305030a0906090b0903031c2301060e011e0f020f120301150c020d080d06031403030405010501050901260c1f02010c02030913050702 76
    0x10461900406c0346e08040040c15402015007070204228050160100909407100d00c03500643c07080d5000461900c0a0f00e04440d80180300c0d1114011800031080304c21811f40010309140400120038904a40100c3c000d0101c50240d503c1840c220383c1d80100c001207024201c505641504100703c50b09100851032620846503a0400c0c1c001a820158041d16880c000e42c5140d002c5042001b07001001101d0300400044000c00d03003030070b2540c50301d08008031311003802e0b90420a00b030070301000001e0401d0047c07081244842040c031000c1115a8482d14a6024000360801d214104407841e45100391200c017842504075800895001e0711070b2459040c1e56403040c5803900000c4100d92550341e140000030202e0a5010060a85107179440030315031300e08280c141a401d484058204502590810740100000c4c0c03900c85c4044903403106c8104e4041c1c01b5104140e00303801e103200c42c3c015079840042e500205800c81180344110b22200c0580d00200485003255030706a8807170203103c4800e40c2c1700c001072801106041c12a005550f101c01688 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 181067751 1250 181066501 181066519
    0x21b13050604060f080d08060103140106031d0d03090b060303070302070e0912040603020403032606060c0a051506091612020d020d1d0705181302030a0b0a05270a0b06 73
    0x10b80349034607004ca44d502c81d04a507072210580f0386080d500031280d039810000c286400c1c00b1044500d600714602c1c1c0018440c00007010780c2d410081003650346060160b24116030400a0710155640010010040c1c2058102501c0340c00741c120100d581858000101d6030310507415000741c588189001700041d801640100030b007400340200002c1c1000d440985006102420341c98500584603415810000d10030030500071180400700c1201c140c584001c9075082c0b055070204003150306c03c3e980c1c0d405040341410843c801800606510a20080f426890900b0304528440c0009580c0c002c0c8030b503119942158215105e900b40320200d05240819200503503a80c0042610500d0110007602d00b03100200c0c080100e41d1701c40481c1005006014054240105c10310450b40100012030340060000720001d001c4002100181c455941c0f400e192602d00d045482c2440720210098104880b241c0b1071601c00269805040c040720b851400c2041408003006002c0000e1b82d0304080c07030380c48000700f600005640e10781041d0351020300b24682c090302c60 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 181069001 1250 181067751 181067759
    0x1804030c0f0b04050304140f030606060d0f0e010b0f1819111306030c020d08010509061912020108070309150c0509030a050a0615051339021b1305060406 67
    0x1549243c0a0751040c0c00640d5558a4080f9021100c6055040c1600c100d01030300030383c00e981d03500040041e004242168107030303a2503000560b0700d07009100604100e411103003040d900082c120019802092000402d4441201c4001e8100407c061319182008003400c0c5004032011811042200707140400200920348005088440c07804032200a4021f20101031464403080c5003403024a0749401403078140ba10342e000401c1d0f10141c144011303000507014083c503802a85980001411541d4401e813684481d50017402c81201c15032200105109080000016404110084080742c05503100c1e210741580690440c04082e020003090440030041c1c409200c0c04403c0000920030b100e81a6400c0c0305008090f48501d00400011003140303000410390764a010585414420702d03c2c208056140c1014030781035522110000180e051104410080c4881d54004105c040c0c01c860a045e04130544445000c8c040d4140c0c2d40807180f205462840800ca00c1e000011015000a002030019480800fa134000a4010000510100d841600c0d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 181070251 1250 181069001 181069013
    0x5030415020403060516020303010b0f09040605040507081503070b041e0509090c04060e071b05030d0203010b04051306230f030f010c12090302120f090411181804030c0f 74
    0x2c10780007601e0543d07807a801c0c422103040500306d4003088541030001d0740c25503140000100103806210406034000300001440d1400d50743e9035005001400005200300403c0c10b00c160002e088040c01c40720000346020307401503100c0341d15000680d0b008840d1195600d5140c02c0c1060a0700a0000d400081c0d8044140305003404a015940d2407500c0d0b101d031341c16000400ca00b4040314100002d56245074083c801c0c26815000340000c0b5680b10503010234560054504000310900c80c41c1c801d04d54850940c080d0142803000c00007140018401004008544048070b01408910340401e0500845030948240c0045d2989100b03409282d0441e104e4070114090020f150502e0340207000046810f00744020750b0710610ba5501c54401d422035811160038180a244103c040001400750780e4003941d18509440c09003052003020408016a1018008544170b0000103042402119404404455584c011403404401000c400800301200d0418900019226611108080f0181c40d6520251103403a4085001c0c0c2d080c00b113055003078001c00d203 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 181071501 1250 181070251 181070257
    0x605010e060411030f0402060a2a290423061305160b03071211070c05030105010b121b0c0303040516150c030305070302090d0f110a030507060503041502 67
    0x150003200582031500c04104001c8941c0003c80030b69101040c400d111640c40b003203402c683c1c01139050310810390322502c504050710043e800c40c000c20300c1c1c100d14141500b124032071040d950400601c10001c02c100102d24101c500e00f440003135501201e80003004070010340400c150045000b008058076540002a00c407001c51542445c008880c036507a83c858034035501040150130480c031070150664014540d10b20f400c11030700b41d0151001401120801c005540b2003000c08010b80c0c4088890030002000c155504501d20308900c004100c4d02c12230b8400c1d440c14000042403020740c0b01f140e000c0ca250300c81d112a6992504000392480b201031000d0510350300c0502507c002e10b10100019030045000310018220000515031503030b80e14001e5040700c060301c51141c41c070300320040c1c0120801c3d55069040c10003090565880740b0840090095680c800d92009040c1c1d010002d00c64410407000c500da0240c0b118401103c0000148014881c840c80002e14503444240100701d803134880e0300955001031090740c407007000410111900f016a0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 181072751 1250 181071501 181071509
    0xa0518062e08041a0c0a120b0409050d020105010e01180207080408240603031c020904090c061805060306011b08070b010b0c0c0904030203040504150803040b0a090803090306041e060501 81
    0x180707110091100340b0001c94560040e1000890100e0307000e24141401585c2402580c805005110458040883c0b85005400c501100c590103042080300180134101965684104081280594a040000300e401164507280c28103843c0c0d80d81c1250440903910400e90005c3d0301c000000e0707410707150601001c80c05c0da0b428400d038411104990542c250b03198a2015640e1804d2007d04181c0c860341c005c04c0340704918005082c034a100324241850068591101c00c000c20090003003107500808044c44170401041980e0401d1691100d58204102441d8903034a400030b2012610041c0c030110701017031682c4403040e50003242084145459216003140350819040d40d6804034120307404c1e0080039000c200410919560f0f4010409510440401c69080c0528201910040c3d101c1c0304030b00070240100d4030303a8051903580b403148002000601c0c02800f202c3d9110741c1c2d0020f0800350f4000728000d00004400840c002102030001007070350903001e00240a08101e444690781c05e204003040c510412417030003914500c20049020707442110300130 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 181074001 1250 181072751 181072757
    0x61e0a030e120c0c1c0609060507180e01052103031603050901020315040c030603050a0b09013215100801061206120b0403020a050604110a0518062e 65
    0x81000d421650030500d142c091042401424000d0542400d40055030501c824802d80d03c52226042200c001040161070580c00703001141442c4220041102c0c1d688080d2041c691580c505a00400200d101c528100c494032411004003003820050103245448050200300300162485107800700301b01c81d091030443e042101c0c4103a00000350b81d0b98440458040c020940c1c0b01d48107100840c80c0d4503103086e0700d850804a0300b5010740655607800901010307500a40c40940510307000022200203030f946181864031071400f00c440e05015400c1600e8007400d019007130b1007000580b003d01200644500354100000712818000c0c94140003460703031985104aa140c3e0020000e900b0896a105242c544c1030140181c00e1510100d5400d03a03840ca0030342c04100074042c407800c02c942c0390752000380c940c1103403528103089142c00c18108028005000d02810301c000c0240b00c200e02c1c0030560065803c00d0307519640700200710140790010001c03005005810000384503071403c00c3c9a84020002e03c0601902d114986460400e203906c400042004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 181075251 1250 181074001 181074011
    0x103030c0218090a230102040b040807050a0e070806010905060a0f0207050102030f040308071a0f09010b030a08070b06030a060626010608120f04150906080f06010905061e0a03 77
    0x1e600700b4030a180e10400700500c0c0d0541c242482c4101d144d8940d03000901400742801c051504a000109244c01c4103c0750300c0764005e41d1100d403201c0c88541c0c0d0b54030071322504405201c7e4000c00582406c10203039006c12148000b800e020341c2c0c0d1b150b21055900d010001c1c25a810072120342070109150f80d42d80060710a09825a9400d07040242258001e45003080c190031460540d4803e2009414107141d2030110307400d5a5006001030348501031440c025041c40b05402c0000388106544041088180304403c441c0c0c03240082e08000e01c8503038250004d01d9261942400040c00d900402c1281c4000f040c900f4103115000392000d821684110455100d40c012074410750051012b5250f64030042010f0400c0c485074981c041621070081155500c0d100c00ca0303070303035402058503148201c40c00304940f4816651441564014a40903042241c0001840300041c41c0701c1c2c0310700a070b00104446402007080070241d1a4107c0c41900103840c0c1141107403c1c0002c001d459000410b00240340008812041d184030100070103400d1008241e100411 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 181076501 1250 181075251 181075253
    0x50d020d110a0320090d1401060902070c1505090f0607200315131e050706030902090a15090b06070510091703100501030b01030e06040c030b09070b0910170103030c 72
    0x1c1c0c800745080c07113104441c43d02c020307a80349002c03030120f80c428041218031100c4c02d0501d180c1205e405102004080d070f1546020000901240d19400411440348100780300060152102c0e4002c03041d07691040d003100024414070812049090422000c940a50010102d82c1800750640e00c03448c0780318216252481440d8002d80405060a0401031041e49010314440c0e44550303d0007501c060345c0601209000343c054039212000d140c18030095040c80078243d81200556404640300c40d07002d000343c02100c030700b00d015890300300000c1c034981d102d03200e1a00e100303824101604000b803074840a00c1c05824249081c55010320100318050014408000800340400840d0002c510150f6a00380300700b0140c3c0c150800d4600100400408c401d068010b840d140a0b90002d0900042034900e94004030010004954854000c1c461a02440244620541d901c01200d108028000666980b0310850380c84120a01c210042d0840038403026440b898803500035403004005d40750140021002c8141d1210081007a4019808180c202c00a58 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 181077751 1250 181076501 181076507
    0x4150605030c1c0207060615030603050a0219080f0318010908100507090b04081609020310032603010e06030606031204030b0402060909100314010219200f0d02011802010e01050d020d110a 82
    0xc0c07410050a0800852f8070f9503e8041c0c8a40e035090700244221181b0f58007040050000403480042c181901c11200320409440f2002c0d46ea03488450761340141203980d80080055071145c0030f00c5040d16040000340c00c4a520301410500030707005c09020203040c01752244020a21595020250004000c3d0784000d0a00580180800391091000d400000c1074500400803c90b003440f403103005000b00c0f540b0030142050400d220040b0504180c000c0b40818103420b00000000f10003c2a07590310340214800c60545103070f034941900309030380d440c0351a49590500c1024070040020803500d00040ea8414009000e19240c0f2140c1000607120200072240040b202ca1868401d00034001c001d8a5103e1161840008510b407422004400030745c8013152211000f003102c00c0050040715900b000e0b92400700003540d0110345014150b43c82898860301411110001580b03010103c0500707101282c4142421501030f140d00c3d4100d4040740046441d640400c08440d1040d80070803904004a480e48614040d000145001a48640d082c030801 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 181079001 1250 181077751 181077779
    0x705060a120f090f1202070518010e0709080601140f03010606051c11090f0105090d050d170c091215010602011a06130b09030c19030204150605030c1c02070606 70
    0x440311451810800c60f0000b041c0c4001c0a404503000441d11000b05441881280b0744420f03074100580204045072245800038036203003401d040c0d41c1030b00c10488031a6180e4004503840100381c82008074a80c440f5004000d504040043e10024400250841407210030b500302283c00d540c8168019400a0070006c0c0c01c070804104d81e42e03200d43e1824000700034043c0060320701d12078000c0c2c041e40c050b4a20440e2040c080320342c0360703000300103ca94003038000d0705050912038641886070702c88081e800f07880c0115039240d41d0021302500040d5040d110b0041c0c007440c142400c4102d014046041014922286144203903103c0000c050045014a0700030300c20703540085036007880030501400c1c034442d0100303c0340200d805020091012495804540035540003400c01902c580c00c11000071301e404e0074856400c1d044412548202d030000902d480c0035085e24000ea40500100d40510300340300440050b031003008001601071000c0344141d00f0300790040c50306103400c2c010158203080c00244030040303900030b400850303407070380d4403101080346081940b41 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 181080251 1250 181079001 181079021
    0x6130b0312030106141801030b06160501050a0c030b010816090b0c0607120204061b080412030c14060609040f0807060c02031815070b13080c06150d080d02030403020705060a12 77
    0xa454100540da92460146c0802180028149525100703c1d048a407112016100d0500c80d0803040704000e500d50070f100c2c0c0201019600c6484013402c203081c0c0c0380458028007a443c00c410043c2d4130481c455489460304200300f2442000700e0100910840c0c00070b01011460b014200d04505a0050b01c5c46080c0682c01400c143c000d40d10015005005000420056070003424059010762038485010000d0030340d02e8103c03854032035074100a07088001d61054109255100c4800083c8911580d50503607400d000c228480d6076101c0840702c45a0081070341c4009400603844100328000303507200c0d0524505011035556010b080d078180c801d88800603800840c8000d2106904418100d50100070f69080100100c1000c108020f4442d10070040d14101d0382c0b10100380843d0401010391120740c3c000c555203071200d446241540e00c80b032040d9046250039101d9050400c3c9860040214100544e01414440c94051494807200c0a504020300c15425401014400aa0303919588000d20300917426994156407045a480950102e510480c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 181081501 1250 181080251 181080287
    0x280504060f02070609031506080f01150f12030f03140703050f070906050a0e01170702060601170601091202030c090106021f0b030303060d0c0306060e0109111206130b0312030106 78
    0x700030050150804885c1c0c0580c1d80000c09107069554441c6048084c20380d0b94800f01c03040c46864003880725420194090601d00c900012515205540c5009410030000c1d54042e00040307403018143c0703800081c0910100c1d0310f40c1405040225200705101320f01e00301d00f10202c494002081e00c1e2000c00500c0c1140e0340301c0980c00100d90070701410045c2040320041440c0a80c00d0601c050040b02d02804606a00580541d8148da04038071041c103051401e44030082d250305044d06c0700d038041003412004501182c21624071b80d00c20702040c2c0d40c07880c14916048003540c144000e1081603825004501040d00281c44480c94503020709002e40042170425080b900c07170006010b03c5c01c84000c5207880c10241040b0360b03501004698000e041182c101c20304c05880c2c1040c2c41c0002055000a20540c608040001d028140324180d034101c6001344000c11105102c0d190380d00c40792207030051221072100e4850004100380750070b04119004a055040c005401c4d500840030900c0c043d44034142d283e00c208080010000ca680c0b00b00c1c1c3d841c0a9681c19 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 181082751 1250 181081501 181081513
    0x80c01120207050c1207030501020706020d060605180910050d0f050c0105070506011701020f0d270b040f0501020921010e0d020703030804051f0207060f0203060d0206280504060f02 79
    0x107182c10303407107041144e05031307104548040d61010300e43c50400a141c055034010008654507461031405c0d000942c00310b0703544031171503040c0070340061070300e003e60305072558100d02103080310701c0005010402680090082c107000104a003044007140079218481c19440d424460140304c400342c41c507400d02c20310704030000c8521410000c0c200b042031b00048005c60042d0458221031985030088881180050280c0501c82071180c031110081041880c0610507080761455504028000e0044114600400d248000041001e812002a5804100090140c00080d442d0b28010b1f0001801c0042c440005000401140800c061640821f020a0340000742803160708a4800074100070310100b201c1d801301940781c032220f200190a011003240003405110b0240004070840b00d41c450b10400200b10182c80704000d400401c400e5039214030306041491445c1d5241300310390268030010590031561a1030750802c651070b07115190300b5602855105c103105418010b861002182140c2d5100d464032907003408001480515042180c8045512003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 181084001 1250 181082751 181082753
    0x1309061203022b080405010207020603040b04030806010f2a051605040b03070e060d0f0204060e040b0702070e130609120305010320130b12060c0a030c020c150307021204080c01120207 80
    0xf008104511a900f8100f9503056a40c5040a82c028000c500b000303500050700104100400250400c010310691283c0c44101d5140c50f40b0340111403c100b01002103005c1074100c2127400c07042e6200407011408403542158030342c5640583d40e695082200700b2aa0040d09a0350701018001807415000302d5158010030744c000c02505241034101901010080e1269015207000c40d0440103000c00070320702c02c40040c0c01410a010060740c500348025041400c0f541030f109001004041800248003140380c1085503042002222140c407008990500c4000e60031003100c01c2542c0d9032a0000191020000021074101c40d03e00046e81c0d8550f00f4506150002d00182d036650440000c410304039961030481455012207101c0000030200014008070754803800444851803036214110420034101403030070050540c01107596091000304000402641d5429a40307840a0b0b020301c4000d016800d0340442d0002d161300019604c111658440442c7d01c00a1580c856002182203400142c5400280d50b0070030000d031402002510300314902011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 181085251 1250 181084001 181084063
    0x120a0507060e0604231e01090308130806090303061915030209040204080f0105060301061d0c130e01030c0e010b03250207170303040b01062102130906120302 69
    0x100e000320000d00000c2c2c6904001c0703403030700c1c01a140a80f8600c0000d40e44507040c859502d141c4407018507a03511440a0b00583c1c04245000040c0c90340c004c4046e10f40810484c107543c0d95041a030400b21049940c061850000150b41d80f04124050182c01d00c0805955241070410500902584820301a4135100d140784042101b5017081031856020b0009150040e01c0d100c0c1000041e020b8460b540c03040c2542e106440710000d85580662116020320710440c000c02900d50f541184100c64000d039080031058555000000360b010650300010b03c0c10a01d0188031800140d181c3c450402216030a030415500380c560103105004441c1540800350162403092901400d615002000c8060000d0f00180a580c400c0e00070246400540200700400103407003a500940c0c4070b5180400050f5594204440a883c000d00c50740000540380e004540481e0030f039080480c60800c40314074840520296020340d616140564580c44000b51554140c411940030780386900c031503040c120381818003d240180011303054074414003206402d00000c103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 181086501 1250 181085251 181085263
    0x90a0510060f09030f05060a05061e060702180c03040b01060504050d0204020a020c040204092412031b0515040506160504290c15010e090606040506031606030209120a05 74
    0x2025160121802502d40c2049076081001d52009204541c01c070009002c100e40469103170320507401d01c0400c1116985039410441c1107001ca00c402d02c030304a00312001200904108008100040c0064180000d8100741d0b49081c500305021200242d100301c02005210403c40b4016000380104201c3c40d00606240c2000f0002319031014481b0003e105660000728180410300034010a081708400400071901c0d42e540e0303802c103030140503c00c3c03406242c5155208041c0d0000b407014008410b0342d01489160000742000e640c02d4400e1408080c5210114800d00d506800080d001c1007040035107550003048881c103050500d85507150000182501e21280b090401580042c3c2d48041503508640e00194101c01ca0032103d56202105c860744c3c0c0e5140f400c5040000c03418405600020170f40507200e40c0c0c051300d502030ba0fa01c208040c0002015903021085070040ca01050322403030160001c0344c010320b0003029544880769404110a0300342c00c80d4450408250042291141c0740703081d50f5464052402e18000c1d02e4140d8181c1c0c0c07003d4542d5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 181087751 1250 181086501 181086509
    0xa0201090506030402130614030d020f030307140c01050112060f330b07080405010f05041a0714030309060403020d020705061b07052707050c1504150f0b090a0510 71
    0x140002c00060191b541d060888401001c81c0c0008001c1c43d9120807810b141038404501e203074003a20442c00240340f8240300251108000045e1406942551140e070030488108551010b80e8404070811301c040340c3e840b85d003071080c68020200301c011414202014500311080e03411500700d600400e40390503450040c0071401d2408842041040c00001c1e2850000842845007000c603410001003480045408000c1010a030000d20688000b621030081c552001c2504540c1ca1286001e104040b100088803814123030300401c05026154850304040c0c442884000d0020302d142c2045612609980c00b9105220505030148003000703c001c003610291105a0810010072440d11586107a400318062440758117100ca00103011000c0a448014001c12005848210710b1041406100b185401d002200000c03510b1240200200d602c00080c080c0601301e8503005a00802a5450080041e9000c01d10902d006624020a201e0642c8007088002c1c000b039044540010300101803001030601d019203140c201400f10102c3c04401d810111 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 181089001 1250 181087751 181087759
    0x418020c030313080d060609030512090d060e10020708090405182d060903131202011403100e0108010609050a0c05040e040c0f060807020613030905010f031104090207140a02010905 79
    0x10301c0380352990040c0301d00207035921710301e1031300c0e0300840c445034807040e114103c0703001d80219162000c401d078080e0340034480d0000030340c4d00582c103880300400100d25400400c45818004240d48a20b0944000c000c1640d01240c0115100320002a80c00c50901c0d16200d0181c209c504981601314004080710402d5440302211442100c00060349a0190040c0d21410900801c4140300e09607041c2d030400c41211540d81c0c00c1b6030745031420102c00032800300352491600003051000350140d6841000750043c5818040c2540b0113003810981080382d0502007050100c000000d4000d1090b5400022401c0c0b44c44900301c1102c1000e050fa6030104e05000182420540c030209a60564680c0003060b5006d840358540808440d5050744452410800c03150001031158220004501c121440e400342c0d001592041c01c8401c819007103c0b0010085a41d1400c2488254441c0e000984190b2481c18000380b0b000038030078200040d42003544a020b400e0b40006030941007082c80c0601d035500005120040218200c1940044d20421340d600881e406 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 181090251 1250 181089001 181089031
    0x60312020c13021c02070305120f0708041403191e0206060904110307090507030204050f09091e190c0303031401030f060903030b06130509011d06060c01020418020418020c0303 77
    0x802500103e502140f13401d0740b4046544034180d280141064110b00c0c0128082d4070282c0000320012001c8500350f100d00000d645205131940c17140d1315a28050134440c40311007144414041e00d81c0740c00080105400031030b0b1a4450640411f8004034100c8070300d200640c0c00c0d04540244040c080d19031a540306a0750001e42c44010b40259104036800b1916040e40c59108032a03050800042c05607154141c0c1c010000c0c1c0d50191158011480300300140001500c05503607040d1349500c01210080141400f0385104401640a07040c0c80ca131800c0e105c840b0000003401c00041d188512800c404004041e0540714104d0a0f140c2c0c210507011544c50340d142ca030f00d00800c07000081c000f96200c542c1541054801e030300140341c2810050038142c480c3c07900aa0b80007161032074004c160050311450004141840740150100c02c00e034100201c030351259207020510550ba0404009030034a51b4007408081045484000221400e0011600044c2c4482c6800d1010154000302448901e400d4410411305484040100449901542d46854a00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 181091501 1250 181090251 181090267
    0x30117010b0607060f0b060408150a06051201020316032003070c0c080a020a0515090103110d090b1009060308040b090a03050706230c0c010f050d020d060312020c1302 73
    0x40503203501e03035480d607104000080e00707000c00109910004c410341210f0020030030041c3c000244521031145018104140d40080119910442c03924000c942c0310030315480100c0c01c950382e44049405a03045903049005a500030040020060442105041c10b2440b840c0501420003290b00d00341002c00609078441d4071440000001d480c0600410340300c01125480b01401d6006ca41d01c40c800c54881c0c84000741244100d01d8130000152500e081c400552100780380742e807854a007107015070054001384102c80034851481001c1c8098504100c440c841e4421080c001c6a501300c19181c00f4003200300304195900032180076440c129040c80818060300948060f00c03042e400c005d58031049c1c00005400140c05900c014a40d00c50a10081407036580f2081e01c20112204084c0310070802c0d191a4401414014090f20741d00c00d07840302c9000740080d0300c2822005040042410024505107114110509980c440c0600464403511103500300100b00211002d10a809007900c041c00341c240307545d0000f41700d440b459464210722607008200c0c19 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 181092751 1250 181091501 181091503
    0x51509060105072423040b0c16050a0b04050f030403150b030a14100b0a050f0103020319090302060f010504090b060405060303040504290a030308010306090c08010507180b0a05030117 80
    0x440070356180c11402d00748003d83d0340306000340401001058412814480d004181812540911b01a0741d203d61901055611202050019046418141c52490302c0a5152000c250144045080240070703030f10000c3c2d2880e107402c000e40b078842285154800c44d40204401c01c0030910541d000003041c3c0e0b40c44000300d0f1140d4a070b4002032401c1103e42e00501034000e49103442e440020001140100c08607115810701c0b030b00c1d20a0f020060441840c2c442c19402c800c0c0c1000041d05588268019648030030514041040e44a03540001021914112000c401680c07045050002c40d0242102c400e00500c030440d42440001c4440e52010007210300500902d0042d42c030756010030700c90780c2c007030040c0c402401e0003800403c109200140c000c0003215803d811600c490b04e01c9080c2013200e061400e550700c181c1e50162600031859285070b903004002d0003030a80644141d54030450200ba01ca10a0145901404040c1d4070740718201034200c05110508065809030078040b1081213516400303034012040d2411180000409005805801d40403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 181094001 1250 181092751 181092773
    0xb0d05030c0a1502041a0a020a1401020706060512150403110a0c0e01090207050303010b030a020415030b01080a02090a050f060408030a0503090c010906090314120c1005150906010507 80
    0x14524000420030080341407000a0315020310b03005000500c860321809400100320f101e54040c5850401207804429031036810000101000c10140c81228500551a180c0e1140c191a100f1b29070340d80c3e500001c1c240c0a101c06801017601515040368034282c500e81c102c820991721140500780e01d02d0090709400103018140502040b04021000c1c20540301091083e1800180b41c08007805071030a00100000049801c004520a9540090380003004610310f034213080c655421741d000113201e003400030b408200c08a0041800100f114007019281c8012440c0400d42d40090041e0000500460b05a841803240340750320b40c0c0b100310441c21030b4010340d80744112140351404200284a41d030040d0809200006800165980c49801180718495034000c3c4c882c83d43e0003800444401840b4417175200010000141400420321040344040308088803030880f1009894503400c1d43c8250444414001d080e00800f80c80d0301800d0003030040d00d50059014910b44848000100010403007070000e414681041400704a100130080c000c401 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 181095251 1250 181094001 181094003
    0x70f120f110d0e1e0a2a06050d0518103b0d0302030103112b05100e030301030f03080603071205100e0f0d050d090b010e09070b0a050306040b0d 63
    0xc45544040d949204006019003c003a00420703c0340c000304010b150303000313810320b440610030b440680b584071131584481200d20303960441c2c118451143c24000c4400d4503506031610041c80386da20340c2174031400403408150031500000c001c1032905a12141045031114041070710000120a0f007400140f4052029146a0005100c190191604506040e0070788500b00a5909a40c02d1000f000b210809103500d9821070580c042072000812456190702801d10a240144910380c60f00784000314003070381e042420f914411500315003005441c40d4000e00341c0f11241600301d0149201c100c025000440c519451945c441e440c1e02d40450001e0304012410012540b15501402120024214109500070704030036170a0003511880040c4c500d0000c0340c5080340701005824003103840c034400e10161010b0544003000042c1615581c1c44040440d0900c0c0ea104102c0001540c80c0d10580d003c1d003030900b001a1f00e8a40f00710100c0c41c0c41095000014104024030141d01c9442e401000c596000704103481c04190340c10020082a080a44040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 181096501 1250 181095251 181095281
    0xc030e0f030c240706060806130c12030c0204140106080a0e100207080909040302010e1006060e19180e070b07120e0301090611070302060610050403020d05100507090e070f120f 77
    0x584e035040c000a42c00480640d85040706950880d01d50401c08240c03500c5030b140c014a00c0d048200100a0110a016145d640070b003e8284202c00402c0f6600007021608500c4840d0200e43d4400010303c180c0e94480886075001088050400164810b10a200d07910b804000c0403103070140d00000c0d0300041010504c00d4031034150015010450506007413030080d0107132806840003030880c42214035240c411800c0c7c1c01480c08540780350702c41c0c21701440040144800303816220348032079221030f8500380001c03a40c001103010f020482d03291a0000c0d22402d28000300741094200c2c2d10121090400f40a4400860725090065000d11800c1c1001000400b4290100f40036080c803910141c801803070450003280d020107800c0107104c094480d900f518411707a2030070100074204680701174110000d1000c3c4000c0c00181409040c0145050080d01200c000703052803d01e01d400d4620031a0b1a0001a105010800c41840440c0000307070408014202403086088401000b8030900a4036104030245440700e915264201c0c940d84414003000580b5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 181097751 1250 181096501 181096507
    0x222021b031c020c012d0b01030501050d060b120313030201020f120f1b07090b1908100c2d0f020d080a090f0b15031605060f0a1407030c030e0f030c24 66
    0x2074010004c04400b01c6a001d424200403687e00b456219100782410b07900c0c000c040f9202c10840352225001020650040d542040c8026682120708804002800582c00500c0180d11300504604c002420002952115405070340b182c480040704520328000d440780d01107046040342d26200c1c4a405050018403180190081c1c1c0102e00002c108a600384c0c10180140d40309541007180d10041101c914803d80c00381c441d000c82500001040d0700d20740c410b07400c550030001c50391418000100000c2840c04c2c0030714101000800d00014042401d2400e504001441d002840740c1c0041c1203000342d08403000d0000c813801040356200580ea106001c04200b90f8101d000900340c0c1120700c3c00810716291080808826404541c213209205941d9030851904411403d841600ca001c0d16107414010740086d00146134002103406024000c4105802c0c0004000034007403d1114069501d000c0a49030505020308410b14100b445406040c1c10b11001c002603c00003039094a003c426654100000f920080c46000ca20300b01446404c000c1e000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 181099001 1250 181097751 181097801
    0xc1c0c080105151002060c0901030603020603010b030601030c11070b0703090b0d090c1e0b030c04050d0b250516050f0a0302030403061a090f040222021b031c020c01 72
    0x5500451040c1c0c01c03070402010300188102080f100484c0710300e1050069101500081e8400e0208001c0c3c041c00c0410704000c02c0c0e80d0385a80c0020f5081d01300740c0014680007000301c10004503613458010500c00411506046000050030818961500f29038012541402e0000a40004161198851a00900148100e02e442d84140e8650a000e0000f4010a4a0702d41c1b01e03800c04683c88040ca50309641007003007044010748281c901a41c480290700003c12540b8050010b100009280d2142160441e500c0c2c801d91900c0403d240c00b48420405040d08000400100d0b5800103c0c61025040070403904c80b0f10b0401d060355a001100d01d0180d140c00c81922040c00280550000942019000000303001941c1c0301e9007003408000b258034001002240b25080440d400038554010510f240300b440328440d0014005003076150b41800101003610f00b16014400500d22580c0003803c01140000c240304240c140c1003000155107031000310324a080c0c009400c07000e80079940d513000a28020682096024500c6540302e010301f41c8000007a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 181100251 1250 181099001 181099003
    0x2070215030f34030504140706020d080c03010303050307080a1d0c090c0c070b1804060605040e06090601051c15090204151b080d02120c0405030c01020606030c1c0c08 73
    0x381d88240c03119601c90b0f0f5607001d030801c0340c0180c9035030403020840140c3c1d0412400100c001c3d010141c4143d80c6100031b154000e42d600401d2183c40c0280c90307550000c00517485e00500c001d00342d003801045594142014001030001a50100c00c5a4202140307141411450311800c252000514264003c0c6104c0386c5c4040c4c1c580c520303040110b0741000e5280121101142aa149103102410b07100380d03005480c07117801c109424805240c050015146811181c407880c0d1030303c0c1d032100c0401c0442d03d098000b40b000c101c000c0380c10080610b0240c4200d5000748291201c0481d41020f030b00107021400343c85040301104907100070b0101348500d1580f00c10408040e000d0700c4076980f40c0e500100d07030080d030040c0030391074070a464400c40c04996402204908080310f900c1e080c8a061684513240c0106540103140d02040380760f020040070004040351900076001c1c00c034480c5602d0b0b9952a0408052500c5101a01d260564008604014090340c021418112545007030743d0418164004841d00d4141c07901c1e1450040001c03200e0040802c1403a0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 181101501 1250 181100251 181100281
    0x3041101112b3204030c0906150c020d1104020906030c0304050d110715091707080c03010c05071103010b060a020c010801171b0105040503070e0405060c0f0403060207021503 76
    0xc010402c48100058003000321081e5945a4004000340552009110b02442c0c50560700082144040c005040c1510380c0c0e03401c407182000f07500400d80d5948821050201d540385e007141c5074101d60700c0c0c1003004d60381e8019408102c0c602110304000d0401074440c541120641c5840c0c044a030f0200c1c00924850360391610b00c0c005002900140c5040d1007510a1541ca54585801040f5410b00c000010008001480c0303400340300d100344404140080c040040c0e2580010740e02c0e00307550700059a0000c103405400c1d11801d00c0b0000340350806001680b44642e040050042015400c40100c0b0321464120301da40310914a4680400e008d04691202c80f60003500004400403460b5000c5090304540100340d8603145503990364000401004170604581d016500204011300a0000586a80d6521001070500f030303060582e604000707030400315a603001d5070540d034025080208101d1b060019960120544c1d0556003031040c944402e62460140317010040c2207070342c000380707943c1595290007100c058000080c43c80c60740d901d004031191610312 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 181102751 1250 181101501 181101553
    0x323060102101514030105091b010309060507020a050d09061d0f220c170c07050a050d0210470604030804030204200d090c030b100503100902060304110111 68
    0x4c040359006a809107418000c242c052000c40c802415801c1e0000e0720256841c80c45844541403580c1c4000c0140003d0090195078403400b0b5036009440d062001e4180941443d03040c4404801300000004140849900701c4082c107000480d208081c500d0940080109140300d5800c080305034401d03020030400e403004004c83c00d840d00c103e0a1000c00d2002aa0034402136503c0c490840c61a0b1713040c0008000504210a40005000a1802030080741c2580340652102410400c40300994001600602c500d40003044141c040c1c171204080310003100d0800800f09140f0340048280e00704514030301540801d080c5004141c501000c0e0149030040641c1e40d00c40d40e900d450005a0700074481217024904102c00c000d400c040f0000c100410303100c04110701c1d04d09050740005034010801010b0807502480c0c420004008031300c40c02c154520480400b5445c001c02414141054644410700a129201d581400c0c00d81c401600d405090341d4000f548a042601d45074544030043e45c021007c208540194441e080c1c011016016000c102a208 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 181104001 1250 181102751 181102769
    0x50a020a140a090e06060d0603030206090f061302061e0408030d0e03070f060c050d0e0304090506030f0d140403050d02070e0a06050a050f0d0b0a050103020306010603230601021015 79
    0x5103045a6519031801000034a0700800d03603c50040212071018500f1580c07200006041c00d240c00c0d151502d8034211a1250026801a805030307080000e201c1c1c04000c4180341c0103d0750700a084924059010b404158540800280240e07004075843e4600320000448409a00804800a86458440200e155650401d030020300c0c01c241010148180c2660120490b54038640007241110303031900c03503180d40001c1e050840b0007404224041002d2503603082c240c0700e4042011400320155540e64902000d59084e00c00190003103119400190030020034131000240309e29020540e0901000ea0448028500c034507024035440500f85004907440c040c40a5030125044059524400c81c85e0003540394a03a5090881c0c10500031680c00c030184070400d03c03a80c5841c0c00c9003014401c00400c0c48a42c0105695075000c80401a507207000d0840d19000140110b240500000c0e01411291030200301180003001000f0f101400c619550b451980e100c0c0101e41d10741d10034050403044034207a92041c0482c80062896003885c078024400d283c50 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 181105251 1250 181104001 181104017
    0x3080a060605030f1f0f0906090b010201020909041b05090f070206011703090d05010209210f03070c030b04150c02250608011509030b100503010b03010e1b13050a020a 73
    0x5039010b071040e6400740001c41030000c0c85560300c5101c0105075000601116403c0055100020803a64900d02807000e0403070401301140300d915207002001960818050a815640107006c5030280d51504c1461543c440d40103480c00c1c0c001d209159400d6920103854200640210342081040301da01d040d103800f41d02031201d542c01c4459031b80e072b14002d03a090703544800100c41c8950420480311145141440128034100d010b14001450521140c0015010000000b4008100f440911906411000c180510090504c0071400b40d403400c003071039170381c410300d18000d00005081d43c003200046820310140c1d281d90101000745200401c103010071280081e594494a04480501d91401c140491003420140000d0341180c0c01d41c0c4410300c0301e9003081001402445001298002c11091450000109018140040c0076064418059200383d080a044c1800d481081d41307194040e17810310040c01c032300e01c0b030000310706504c2584440102d9500e1000c10029000045101484150301e00b800c2c01d00298062503030042002038241d4455541d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 181106501 1250 181105251 181105259
    0xc0b07030c0e10020304081606120b010c08070f020316080c0604030507090c0c050114060112021201061d031b010806190902090a08060708100b12010b0d0b0d03080a06 73
    0xc1070310810075807100000c1c2d002200d10154184850360100c00c00850054a05145d151030f040c2d4a041d80c00400380c145190351401c1008401e4101480c002c03401c1c1c00340001d028004020340060411001104001d0040d040011a003040c4940205849400c1c1d81c01000c1c0d4400524041860644541600541149001d03440c90b03c3d4181c50068226012a54460060315000c1d203000380c03840007040140303805001c0c45600201c000010b1001e2240340619022019540241d04052000510f0100e000300000c0c03105104000c000400804940b003141183e9040c41e01000040a15000c14001c441e00c0100c15010300c80d0381443c01c41144003030b480e4800c3c0da1003a41c4219013980c5c0c20081000c4200102028007040c04180002c3c410007840390005e048401010707080030b8a16503100405490014211000c0c03001807035200a00c4140500000050020048400c0d41070420880a900c6030f4016018419001c50000010b178040700202960051454907100800101d4408007609002d041c0703080403564007500c00e103000c80102d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 181107751 1250 181106501 181106507
    0x4081e060a180b131b08070b03130b0c1e03010306050c030621120d0e01052a0d0b0402040803040611191b180f0e030307021203150a060c0b07 62
    0x2400d48080e03146103500a180e00c500000c410064604c90b403000c2d443d58014042003034031100000b05040d150303070542e240d403601c07210505001c100d40200e0541c40d002c20901541c1a0310f982c807440f01d04d030408420510ba4550400d420501d11a1903002104802040d0030b0341c442641078800365040703c0c061071050010390f46460300300465202c200c03a0641d0244044c0c0400158084200c0c0b6038441300d10860444603002c8600c86042d9158004010441100c1c0d00d03111003131401071086c0280f54100d500c09a410148401900c0344010716a07030f45403103c03082d00300130929801e40f60084c1c100b0035070302901610841d500e80d01c0d0032403241c8960241c00b8500100d041c508241000d0540020125403c400000c0c4c9800487ca845c4c3d2016550305810030300d50049080c82001280050702405041c581d032034018400114114080c181c0c805450700c0241d44159908140704000001b500420a040c2e10090b55181d9035980d034440d80789a600040b800040f50300078644c0c80c404641c2540110958008070f004003400161680c5001e03080f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 181109001 1250 181107751 181107761
    0x9020a080c03040503040509040b071b080d0b04110c0d09060503150d060f05161202040e0609040c030501022101050d0c0603020901090302150706060602120a1404081e060a 75
    0xa24001030003840021801680e420180d50414800d42c01e0b03905d001c1da210002682404c0a403000e40b581c0744180c003805603ca4019202c809008451700b00401002c2942c0c0741c203050b900414419800b41030321032030300a000b0b07510741c1d000072040d031f9000c07a0082d196859004082c2c0e50301c1c5c0c92030308140881c0d0040300c04180c031405001500d10400780780400e8000740c0c0c2d001d410b0040a10101a040382c2c00c64440100407003000d8280a6240700303800b503c1c2400034021120307400500c04100c078200307081b4a0303104100c04c0c4040d80c2448121503000800f501c0c000659266441c02101e14001c9a1018045500c0801c283c3d4034501d031a00c0c5a40032941103115400913980314001c0004200805100030251303000b20004124060090f005405241014101204050703540e802041100f10328101800004400154007020003c0500c50b074005031100348020a070288070800b400115204010b100002d02c07494010300d41d120203241003103c000c0d0402e041940c2c4a1441302c041085100d408401a00807802444000741c91803405101e0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 181110251 1250 181109001 181109017
    0x506031f15180f1808180d08030414011a131104030c03060c09051008070e04060b070f1a07020a031b0606080607020f011104170a050d050a080a0501030312020d0e01050a060306060902 80
    0x14030781650100e031071b04c2910740b03140e407950030900042c00480458145005944100e0280c2514584800900c4586007142c413002d0054005900c1014080004d860310b00a1400304035403e140002d50101c07400d0101030a00a5070b00081c0080ca6911005c000c00c0801e070042c4013005100c2e00c1d01d0100130f4451003041480300b001c07440c40700014035080000d902c0e40d100b000410740d0707494080c00000d5026100c100070f416660040700d0a4403907040c4407005008010450180b2210210f8580c1007800a061002009407103c500030000f80800c28403000e001200c04040c0c0e910000940d20140400c051951015001d0321844101c41d00c00150160000c0b07070043d50418054500d0030440754035090b02d050b04060b1400c8060303d0b0520b04045030310480030110000740c01084411154002600e4030303616070381050402000314100601011509082078010000a40c0040380003140b01580500541c40ea0034400c81c0d00020000038009040d1907007400b0034072101d0145540400c058034020710003031140b6920b41440070260300c10340c04 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 181111501 1250 181110251 181110263
    0x50a020f120a030b0d020303160201091e0308030c1c0615031116060204181d0c0906040e010b04060b0c070b030121020102030c030a03020d0506031f15180f18 69
    0x101959052103a070024200c0500100040805e013101d03004649103400040c080c1075041000c11100c403c1d0760b04000c2c0d00c0c0007003800000d01000c4405042c551120455a444010328103003002c4042502c200203c01a50805448088802840c40354404a14090101e900c10703203800c02101e1420781d803664441c2c0500e54501540d20710071407601d4001190b8070301c404404d00301518915400c0c000482d041c25001c003d1607040248160200d10940303006000d560440d1009030005c41039005aa421441ea20745001195210408540000d60210f84c03c2c203450140c81c401c140c0c280e01928040011030070303507514005402c81c194040c1c2107501d2562590300e0700e00d40d03110030300410f242000491001ea050b03c442803004983c441c41803042c1d905041162142c5032442d0441c10000b004241c01042604044d6840d1040c140e021404030010206042e101d0701100101100c0b100801581d030b00c0302600d50041c4510071828004000a08414500100758454130004102071021280800d0506441a824641080701e040c1c840390420 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 181112751 1250 181111501 181111507
    0x3060906060a020a110109080a050304081e0d210e0703030f050717070f0503030109020d0f02090f0d050f0d02060a0e010605010915090b030c09130221040204060306020307050a020f12 80
    0x2031203000408605c010124104410108080b591580c24020840894420001191142e003442d0003242880b007202800f18601d1040d80e0841c0360480006414441d0031440c2c20104000c6080d00d890382508805014418100b5082482d90141c5910004041c4100d81c0680d03103591040c91101c404407014850076401074059107180c1c841881100e111401040103074454810705550001c69542c960446c0c109034010b4180b0f41c3d000c507138600781c0e401c680985043c030f5003034400440c0303040b43c2c0c00c0024a14021069005004040005c0b4601c1084010003050781804050011039000c1500403400070350300e51007215551881c0d418502c28a1407804140034200941e60145c44000d161424010100040700c0300c10007007800c01014450014050f030a010045d8015211803810703560342c41038002441040481d0101151000b80304001c15600d8410072003041a1f40c82e4484060002900c445c0002405001d11b50009484c842c030020501c0801a0454002d0035102800c0d000e0f2284c48126806d1507449074002c45041500d04010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 181114001 1250 181112751 181112753
    0x80a0516080c090c190206070e01050f0409052e030c090b181306060f0e07021203010909110301020406180b07020102100203040219060906090905061c02030a140303060906060a020a 79
    0x2000f00c80d41c0004450321190902c90507050207a0350040021160001d82c00c15000e00291070350102c910501d82d54282000307886c040740960464403a120324480e441f8034a40d200c0106040b04500b19000d5064250141c2d07011407038007000702110040c01c00e844100c176807440480000502c079403580202c0540700740c020b00380d01c101d1100d81092012420014108086400c101e415903000034a640f0800002e0418054040c111505003018047c00c4c1c080606100259402001e1942488000104981c1510007044000c14480024540103180b04250b100d1664075500201d004208558071149060100f45000c10341607240365102c84c0d04403203110309a00a4010b820010b42940c0c00b4610b900119006440904011680c0c0444503a0a440040c41d400400001d2204e070b00800540d5400105400034210260341000103061000001d00350b82d0350900524448030003440b000040d56014844c20160a4000b44104403001c03002070310948982c030440d10684101d42e1203010072072600b02038095440f482d80e940c0090188400d1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 181115107 1106 181114001 181114009
    0x80f07261b0102070e0a0c020d0c151503020d03120506041503020d05160308040e0f060d1112010f0f110918070c020604080a0516080c 59
    0x20490164056000410404108061901c81d100100c28460040c0d050410541c021006400d24808000e4210f4554004070051205c2ea429039016100030082a035140081ca40c018084840d90741100203407580235808502c041009034482802150380b0750004071040311602040300040c40c103c1e041580804140a02500820201c5040c0030701c044040500701ca0350740910020b8415401102604248031040c041440400d0194044c045015182d003052042035200307225036583d441d2003400140340160703000983c50103030f00c005007540c40840a0b500c41455031950140c04c2513204180c40310f400504030003403142c0408000c001401241e09281040031000b01c640148100a5501082040083d569204c03078003000c40c081051108501071b11508021038504010400094002c0700005000c2010071002a02ca04074601c0750048803200307100d2504d482d0302e0820b10302c1409030a60201841d96030500d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 180935251 181115107 := by
  have h0 := BRFrame.cov_init 180935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 180935251 ≤ n) (h2 : n < 181115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
