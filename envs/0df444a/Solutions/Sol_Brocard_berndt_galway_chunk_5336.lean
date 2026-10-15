-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5336
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:31:58.082462+00:00
-- url     : https://prove2.me/submissions/df71ce10-659a-454a-a051-49fc012501b4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 959532374 ≤ n < 959712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 959533624 1250 959532374 959532383
    0x70e030d080f0f10170303041a010503030d110f0d09030e10050406030203040606210b09070b0d0203090a082d030106080c0d2c10110406110f0607020a03110604 70
    0xd4002030306000e040fa00403540001d00b80c80418a1076210518003004048100c1c0d410b0300d41d0310010500041c800040d1180101c21026810500f01e0b42c104000300381c480c051540c45244d01c5482e88414011800c1700720948a52002201805407162218441c10000e00a11a410f5000c10081c8000a15030b062019186860354689c3d2a210324052030180102c0095200500176186c05541c1da80c08282004c0782d030703520340c81c0c1d000c200b00c5218072041d6800d004915950140c1440d01c0303940480420801c44d4062815202d401c07141c0040161603035181014907007808400c2c0c40c01000b000c8002505200000505802c3c6d2401c0c0b030b04114107a03403c141400007105c9110a0052070f02280700c40380060401e1010b980140b1800356a55004914101c1d0804051080309901956881c0e1100489020045450821403110703440ba221405100e5544480708001c0c06110714021710382000078030090340318800c1c0c08100101d0005002c1c001c031081072a1083c0001e4940301460000c400040c1045040380301d05000158040c000c9801c03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 959534874 1250 959533624 959533651
    0x60225060b030d05180d12020a05070b160204020708221805010b091c1a07030f181401090b0a02040609050d03171e040c0504050a060b04031101030e0303070e030d08 72
    0x1580c174020180640c000a450303215024070188000602c00701421008003030960001c0c40c86240700e00c0e00742c0c100080b54002c40010b803424070480088120b200c2c080200c194059038016502e818904000300d540c40b8441010a06d01c4502480040c0107100d03406107030481e03400351349026410440c11040801c0d52802e01c198100d071101400f00c820185030584060081010a6001c18034640305a40c0d4120041e504a8256202d240c0c00c00c1003003100c3d40c06024500303403640010070400180d80601c0704d240c0181d02c1034401604080c9404106e0315640401d41c04140b2050b04051801c81c5413501d031440d8000381d80203001e0203000420f4440d0009107070502450400b4920746c0350f02c0c1e5019490712040e03501000c2c3d0006100e0403070f011024007091b03a45c0c111240024040c0e401200b0300c0403428104804c1c04103a8201401c06000365191040170444400c0300c5080c0c0741640d600035184d031044440440120058244a4840506404004240b180c0c50303403c001550080c40c4241d083d038040d401ca11000340d40c0c020049484503958140c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 959536124 1250 959534874 959534887
    0x906020c03070b123c01120f120201061707050a0b1213020612040f02042d0e070933120b0403020f0f0d02070503061e04060225060b030d05 61
    0x2030320f00b510341d00240780b40c2a594200b10304064411171404d019075400ca0480c1800070940520280c290450141001c5400c050a0041c07540e0707424004619180098681c00d030075501220300314801c0d0440030007007030350341d80d4038040c4e61241141075241c1403103102c0c5078854005a10002031000002080d1051440d54001f803039090b43d200310700070800ca981084126800301c4100441d0061440d0042c0d118002c500070a1103090740703030107441488200c400c030503240b0360003140322840c080141c141c0381800c660840c0000e002048440d80540740a02e8203140f40c005210182c03c00740e4a41900f07400d852844566100c1481e090000321940160f4414000580074805002c0d0650117048003260013008110741061082c41212950018219564140903683e480f402007600003c001c1c842c4030780c0c1000b0000207000210003624040c01c2011404414403810b92940f02d10200000005050003103540c191011804148070b000c646820070020a001d50328000803c8070110326002c1e180c1030504000800e0807000a403511414580013 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 959537374 1250 959536124 959536147
    0x70804080708040503121c06050918070f0608090d09030305090609010e0a0902030702070905090d0c05071a12090c091519032018060d08040b03070906020c03070b 71
    0x50150100755007944003040f000880d80c808110003105850301c2458580c5451003030042031142101d003602120381c0e80c1418010300281d510740045603040300400f41d4030314292045004c45403d110a41d80030590700102c1c1c60002559680112816101e0342900d021b40d15030f5000c522041d0340500362400b0150009600f40042d402a04045e40105210481410200140741c02c3d00d000900c1038495802c00c41c402c0c0d401105200786d554040040002510403d40b05224501d40031b0900ba6a880501d0301510410811500400510209008801c043c008c1c64180790004e075680d8801c51025070001300741c0c1d02d0034a103220004074010408900c1040301100100840d189468007440b120b111064000e40700d82c4082001d00140c860900f00d541c110056105221920b00c00c02024060110443d880103000d002e81120326003654100310780103845038015000c582490154029041c0000d07140520b0f00140d0400d1400001d000c0c0180d0410014000c580b043d50844656160210a02d178803000300d4030805407040c00c1130000e508c0c000c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 959538624 1250 959537374 959537377
    0x80319180b0c03070606060f02190303020c061603060b07020f130902030f0322030525090903091a0405131107060e1e010606021b040e06040305130e041a070c060c09180507080408 78
    0x2502030314cc0541003403000103600d8141101542c1c7c07062100300d800b5030340c100190980035120041850b283d11604008068010901c040b269521310b80c850785400b49007078041c1500b43d01c07132084a0740142c01c0329981e408606425699a02004c800710b4030100388600c2d141c901c00c9072070543d810780764040040c2c06c0040803403212051610701c60546581000a480003c180102c45108044103540607a40e0401ba141c03600d804480c0f00701688001d103142d500d00300005e1055031100701c50381c0707490000381000043c1c82d034200c50f99030020b00a403100185858208114001e8000000a00521400711483d50085140c01e88012b05d0895549204110140e0003a40513080d414840c4030300707403210a0024001181901e062011542003e800315002c40c041080400c0007992182401244409040c080c2280096400c00d51030b0141c10360f41c1d4048214005041c00002900c5510170078039040c9451340400180314280c4080c0d805042cac180750340104041c0000321602c01c0c95041c01800381600514950301c40901c991201c0e125008903 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 959539874 1250 959538624 959538673
    0x200607021201140709030b10081504060f021303141c030b060403020607050124050105030f070c02031c03111305090417040915080319180b0c03070606060f02 69
    0x7555624007070000d4103c1c01110040c4540f900e9a94000c1c13003821413400d0408802e02902c0b203601001c1900e41403200303100004041c1c00c9840000150080f40e41c5a150010142444848264045001180700c500321040071800b05c069a101c0e140d6244994107041d00a90b55002e050023040314811844200201070b40254005c6030120400f40485c0d24060b00d07600410690341c0101c41c00c407034a84d515104140328092003198501042c003000484ac0c40d4a01e00b82c0000d28500015200d82901c000c0d480100318214051400180c1c415409400d0f50400303e480000b000c1000c03905039500740800e00705941074000c00c80d42d804844008614100c0c0c00b00542c180000e0003101c1c83c0060044910750100c01c3e00d0403800d10110050310051140c40300c0420321421a81708a01400c0135540000314903801842140200c40c0c0c14940d0b003494030400e1030001c0e4901007082c00004012043da002482c040c0340026a119161000300c020411a400703010305110150b41c80d40304480010310041d440d0016085050280345450350503c11505 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 959541124 1250 959539874 959539909
    0x1020415020d27120f210c0b10091b09120b0112050109050304090c0e041a280602010f110a0203040b0c072301030e01021c020906070501110720060702 66
    0x404585440100c62502c049541c1500d401580c1c8950702c081088180c080c1460012501c612921b21a0649002e405510020b0005281800400c000f801e20704114a451001b058590300078003125035040403020b1030341050150540040c44e5640c012a1100d180507945000c1c0782e1101160310a41c0c078241508008104030700b001c8503170707541703920300040810070070000742c401340548200000e50900300b00700203045500400d58031030080d81440c1c00302d10031260b0501580c6002c101581c142c299511841c01d89040c1e4a1044c44207003520410b40000b007003c503815400740d060301c1d90300d08041001c0c10f0a100b801785503018261030800107030b104001c2403000c0b02c03080e000341882c1c80ca440704442c070302c030b4565008522026900d02da1003850b0030640841143c41da4540500d28030300c20300500071803503c0c80051440b1611205220203a1700c440e00010103000b1034031400222004650008001c0144903000040403a1316809080d06442801ca00c0d00c541c811505a5001c101d07822500070440b6280c03081c20350034001d00d40f0f01110b0100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 959542374 1250 959541124 959541197
    0x10506010201052404021e0a030b0d0210030c1718010b03031918030c0603090b130b010501270b0306150f040315092001020d020a083901020415020d 65
    0x104207e503403012880207080e1188250392100d07140300740201216050b164031446450032007034040250700e03022041c00c80c40b041d41c40c002c01c0c2800400c10642c0c3e004620070040e0403251104040080944803100444000e10307146000f440554807400c201507680c0685071a41d104035030194800c0010600416401c0900604801c85103a803a550b0303140e40640321503550050b40443d4480328424200950030394010741c408000d8540d50300602450703d886140003014000c26041c85407240e00c0802001d5034038000d48146d581e00c01d8508000c1d071545006041d0fa0030070707200e090140080b08801540d0051400649072070300080341e403840c2001d01e1a04c0d4450042207000c41c1c0451035580e82c1d80e0001042d101011001c01c0072a42d080c90324024a000c000919200580c100b000864002c00b42c0d54001034135050480318801001e40403c4011404505880c0e0b0100c03039581c0320414a460610041e0400d00c043d0050403c407815080082030010300800180c2c0c495000d401908000303441e0030041c250506901401100f02c425560682 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 959543624 1250 959542374 959542387
    0x30315030304030b16210b09280c030209060c0d0f1707030b0a0506030403021b180604050408160c1a040e041202010b0d03030b0f0f030619090c120501050601020105240402 75
    0x30211030307a50168086d140703460312112442400c0c00450250403050701d81c0140800401007540b5101d0301d8074000408500e1b6101d0000482092094068a030240c5008081365520301120120b2a51515003a81403000301d40e110005503c82c0e4000c01801c40044083c039207000c503558402c503045005100d000d03101a405400503a0106690319460051449184039400500d5203c1c030505c4440284225010314a11800ca08400d0f00c101d070f00c1091405801074800d90f00814030351120714210503540500000384151141126164007807000d007070300800854140d540341c02c440410300714401c1614070540c05185809804a0041000629200000d409100440c400010314114110010700800c8814006800003a00d9081e41c0c01d6501e454080090008401c03604400d0441604000c680c1f1040d00400050811800c5044005000215085448810380c0807001503035250300c031410340140022340c05059460390301c0d140000d405c0d5401449268002d40b0140f5544080c5c0952200b80c80c4581480075050b42c1054090110 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 959544874 1250 959543624 959543657
    0xa0e0109090c0f0e031204060507080f0a1d06090a050d030c060507090515070f080c011b080f10030819050903030301080c010f0c03080a0504050a0b0405030315030304030b16 76
    0x2002c0c0003070002e42e12240b084001e20300003400198074212141c4242c200c40c48000c60240c0350805c9508441007410020b45074031213401d1440d158050381025000a02000a02c41c07151a4403141a030314001209000b01044400c0a051051030302415680c42c0d08001ca08005125030300c1e2075058141068468a810403022440d9500c610681d0010b4440074041000644240002c0c81c3c08400c188038a440b050301c04e4205903590300c071000749484041d000340207c8800501004607180a400030340a0300041d4140541c0c1401c500e100a1200104032022060400c2c0400801c45400301071519908498010076480d05140031400c0d2f401c82c00d15689103840600c6000c000002003510103002544c000c1c00c5407006009231840d45d0002400803640d400fa03880800400f210540002504062403a1300300c1d00d40c007000961a50b45207481c500d80740c6a4031000c1c0c01c58007404104010014008015440f8042100305c1b6421150340c00103050340c034015804010710340c0707a501c000129944008824a49801d100d4608560080e00d144d08 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 959546124 1250 959544874 959544881
    0x1b0d02040c080114030303091507020316030801050108010e0f1b09030106080607021c0c03140418050402030708210304020d17070318080c042c01050f1b0a0e010909 72
    0x1e50340049603103000104250a07200006000c0c09500703401844c41d52621b080d4135625038800c1e5000c1a1004561008516481d00c20010340e4034568840d5100203608032942005001c42200740b141c2030004040f040040340f89d0403054000c9000c2e000b5000103811070b07140e0a45609101003007000d03020f94080140325148840d6001d0261030002d0101d600601818102024000c0c03d1035034610301c0d00022903001034507a0307a00b43d00c2510100c8a54051600360041140d00c1006070491107142e1000c4c150740b0030440c1152010075a03901490140d8400c0f03045411155603000c1003615402003020100055840d84020900491540c00031a1300c188002c00c95641c451017a981d15801d55281c00343d4035030854000c40c4103000c0540000406018200c0010079942c0135161800b07482e501e00b40c80d00c625014589800c00d150149180e512000d4244101414261000506401c000e0003130904447c40d1907a08108008142d910104507110300b903100500c0102032400c509602e05803000c41a499000e410409000b03000240e1640030711 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 959547374 1250 959546124 959546141
    0x2090105192f0c040c1d03072d0f050a0317072414010b03161707020307060501120f020621040305070308090708030315040905030d0b010f111b0d0204 66
    0x3074180402c03214280d401d074a0001002901402a854491405101c0d070b004980646209803c1648600380d051840210f1b040c0a1250b1180c6040070402c0107828003140301800000c40c501d4404a1615800d40d27400100031418002d2040a4005140000c2030003c41c800124403c0d440c8450f1240c0b80c40c180742c40c1d80d030300c242d42c0c198182002c060000510101c0540c00c140156040c01c0e81c0040c02001c2075041c030384188024400940003449031518440d90205083c084c8801111b843c0c080d03140d121052070612070194a80d131040c0011508503291400104010161949040084c0d4110403001604411035007408a980c0c840c03802580007078500c81c80c12014a45500580b449180701e6600c4d541c03221b910303140190550314050103150305900328076414807094400000f52a0300c64003191700c40034581e20724030120700140742005018003580030000c0d042c091003445400500d1818004c0c0d942c075040301121042202e101454240c4480c860f04002c800c0741810000c44d80600c180c400040000c0481d60882d40000c0c215034009 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 959548624 1250 959547374 959547437
    0x303030603021302040b0d0f2426030403120516080d0506011e050d06080601092c030f03190f0506041d07030b04140304030303060f06030209010519 65
    0x214024030031810010302102621010f0f040c01c0d42030a0500406080d18060841406040c1da0385500404501202c0c2d040004003400c0c41c8503a0300c0c108030541d03096240d51000d01550003506865a00c034070030451084994600c000c5644051030909080d5614440012001d80d100400c10000f4051918604030308401e0600542c464908d0035a14074a4001d10307402d40c1e000400041c1800f0307110160329100c403803468028407203420394a802640d400341114294001d01c05904510041d00c29840007003007450440d0302c83d458a0810780d0f944051450201e1064404155a031340d40c0780d4075003060044d001d001542902458200d01091100d00000341121420000c45200700150081c00751900180059400c1c54400c0e1003440426043c801c2c00059400d141c6036a03402248001840d0301051400142800305443d40003283c80c040d43c094035540c81c2d13242001000350500340a4624107040c1e00c00005101c502900c200c0f1b01000042c1c464074206403d00c0c003040360200041c5d40e040b041c8502500e02e00f00101d40301c0b0280d80d070340c0b554 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 959549874 1250 959548624 959548631
    0x31203090606130b06090409050f0304090e060906070c060507030f0516080c2104230610050604030201080a05090106090c02010903120203100510020f0a030c02010215010f12020303040e01030303 85
    0x2450801281600d00d400d4444102e00e0003a013021a5107484045a41c0160103882c04200806240381c03c501e4034034180e1411180340000301c5d01145840543c1c00421440003100d08444242c1c07100d010040d00c0316829102c00000c0340c00040000001070a60300a143d01844a050014021186007031486c26100c080b508446c0c08000d01c040a0041600090301315002115400d009042c4101201d81e0780e0a4800100e0001c81e0000200004082121411003a0341d001c0c4040510141c0c000c10b50b980a90318001541c50040c0c290079601c0215070343c20140156030440e60140e6442c00c003602e82c004908000c1c40050020407182d502d40d400442c03024031030702803032a0b000c0301c4d68000100d086080c24010103001c0a004002d80b80c0e4010000e0041c520216404101030f0340e4225850408000303000c1040e441d11500811111041c06041d0245c014580c0040c1c00c1c100f000c2c003c2c1c095903000c00602180e4120101709004502003480c8240c0184100e200030035503ea01d00388090104d0340b03016120144010100000d078400c0740040d0720b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 959551124 1250 959549874 959549881
    0xb0a0e0d050c210301051c021009180c0212181519050913020f041a130b030906010312050c1204080d0504030b1b09060315040b0319110312030906 64
    0x400c2100c0c22003a4894aa52146014107030083c903140c1c401813150601c16468050014a502c0d0201c03c0c040080c1d03801026080c1040c025031001c0e040b14200d00c00c1d10007082c9008003141011945010b20301807240c042d805006c446610f8024240d44c2d400040f1002000010340802201c40d40310f0360181c084a64840c0a0301c3d4440c4000094001813101e010451801c01c1010301441e2500c0e00c58600e101a0014003110261303e41185044c803150a00650344444c80400302440880003840c4034100900001112100e902211034484d21401520b100a8800d40f0303169114a0042001c40d4450841e0011a0070510b4a5454580700440700780c5088031442d82d01c2e1080c4c41c001420851040100140da0b1418842d052180c2458030350344503100c0347e9100074245060640400e1000720b001941c00115010400700804603a10382c10107801c400303a0300e03401e0520b541c002c0c0d150050030070452030001010103085802d032100300c2020301d5a503103842542ea4041001d54051141002aa9104a0050245120b041004c005081d51700c1e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 959552374 1250 959551124 959551147
    0xc0702090717070f05030103020d050c280b072003011b0201051e01081e010b0a12020f01050c0c010c080904060815010f06050f030601020f030a021b0910030b0a0e0d05 73
    0x2c002c0d00181c1070051307041d0410702ea103800005607070441c2e404440d0401031100c3c9040c00781c1800c083e0a040e03a40800410031521403084501d4521840f000459000900e00352181803c80b064407070780b4005000401c80703280d00040030f04803640c44104140c02400204000c490030b41e013000c48041080356440542d450f841003100b02480d00e61081c42c0410741507422110365240110b159124801e00720300080200443c2c066031001e02007504900304e2820042e041301c0311075039140c1e9001000480c0c444124070401b0000407800c00c541c45282617a15281340030002d000304070000c000540d905216058101ca00d0b42c1c05200743c99055039684101ca000700880d03c0a490300150301c02c049040c0500582043d611011804da09000042e0302400b50340c400070b264052940da0b5100e060050f03140100001d28851140700020b0590821540480c6600340404120a41c040b4041180100304507003404035500c4c50b10301c813280401c10119003029821500400748a50000c0c03008525444241040c5c05140b8010205400144401801c0c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 959553624 1250 959552374 959552417
    0x80714040b090c16030c050604121b0c090b041e0e060a0225051509030a0306140907081e071d030c0a0e0621280305070b0c07020907 58
    0x30030460b0003940900c0c0400d400c40c01400f440c030641809080d50555501003501400207000d0140d003007c225002071070245488034003800d01850703260018613207036160700000c890200102001540035028511040c01c01c4030342c7d00109024841c103984031381ca40340c4041c040d9900300d40c4180901c11025002c40c0504038020070070301d05540605060b801c6441001050f0007501d1022030fa070906290201c00710158038943c1440d034036003180840c41e4500342c0c0482c800e101428600000401e242d0075682c405100399692485954604004031803080e4000081000042c00340d0701c1085240da0004440c2c0080d18550b5002590400c2020704a43e501c0214488800c0c40c507a4489450000303034801d10460050005d07110b441e012517614904c500c100140c8145a4000c100e80750303903028004810346003503101203104840050760780e951503070f58400c032020191840c004802d8001d2221840d480480e0152180e0707142148640d80d00c480c1c0c030002007056055800600c002401a5a8440c440b03009201c1d030f1b5191075012451034202c8542 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 959554874 1250 959553624 959553641
    0x80d20071a0c040b03070c0503030a0603020415030b0a0e0a050d0909050609060d020d03020f0a1a0106020a0c060f0302040f06050d0501050604050109090b06090301110403031107051f030608071404 86
    0x9200d404100110b0419080443e001c0e0b030308207200c0540b41d40314150207890409048000800710300010040220210141d03000204590086405200319a10070401141c111040c0c080508a036441034002900c00c1002d400c40102e0030003c8003200e12507034050301e4150038005038400c00400105258420014101d1078012160480c0e0120360047c4503050803000075440c00c5078004000d00403000c0008460038180203024901950411000781d421034041444c2141624140d030042512a600c042c0020a06601c0020020b007150b5010b0740c503010302801c10310b0541c1e00528166004003010b0302000045200700191502d54010005501d0742e0307484070302681090064540c140c0200d4010282031004110a07070303105000310200c230203403035000980c0003000c1c02003646449440c4a958240d8240740e0589031240c031090081c400c690003999034541360025566215141c00b198401d417580080300402d070940400c00003039070f0404d444803410001071b0141d54a003401c1c01e190305644200e401000d842212462420140210707150f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 959556124 1250 959554874 959554913
    0xe0103060f05010b161a1005040f110912071208030708070320090a09090b06030d030b0109361b180b030c0d09060c0f0c0f080d2007 58
    0x180f507041801040e02c0c3e0141c035074245903110741500404244140c02c030a101c1c10013034001d12140b181c80c12092841c820303211032040c540524900081000b04040521a91440401d0040041d1400b040c1e0010402080110100b583e201c0c001e500000800840901110000e82e203c0c1c10b44030340324a80004060400f010082460b01854204041116050700007200100c0f0791058070301c40c944940c4130001246c03404480340c210380010360bd00100728041c424003400603880f07040d0403000c4070003c0d00e001108030240c0d0010950b041c0803d2240105005000440410003100c1400d010003132500350545c05050048081e0b00110314010769299601c050f100c0409003441100440d5082030840c0d000303901c51103004003035284103030501040044042605981c0c5801195994a00e00005004000c070714104a4010704400d00140082907034405c803048090300800000d03c00707a40100c52040715103515140c54990760700040840ca202035583c3d41900c0041c2055000c183c120301403014141e155030880c44c04034000420a94207a8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 959557374 1250 959556124 959556131
    0x40c0602030903060a0f0b151806120a0513150c140f041a041a04061205071215050406030305040e011d0a090203100c08041104063206040e0103060f 65
    0x4040b43c4000448503000103513444002200121014810002c054440009520056512940540302c1006010b031605c540200d00c1c00c01c103a451b003c100b00c0f582c807840c140d0781c0d1107000c0c840c0081c815025507030146a01491952544d10280e00642e60300b410f000c1c41406034000265250f2540d00c4043d03010f0200f0303400032903980c00139261410071000250b690103a03104501d2034810b02500c40328200046003c1d0740045c03428488801030700ba80c000004080d038100d40071325000210202e507080540901070084501440054a17401101200d5a80500c003405c000d046148900a00110000c0c258545104040056029995881d10f4030308240c00ca120001040c0e1001111549103016821312003103400c01c0540103c0089000a0308610a101082c28402428201943e4a180c0129002001e82002c5100d1095206592300351a0340d0003842000b080300c1c0c281c0605280c25141c04083c50010301c0170407e03254480f144410015840220b440006d12592181c0c20200c00010481c0c010810040107010b00108010500d40c20b2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 959558624 1250 959557374 959557387
    0x70b0d2a08180c12240f060a030201081f080304170f0d0207052404060908010c020105010620030903030d1d0705102709020429030f1815040c060203 65
    0xc5039250a003502480c881c0b6406203094030b61041c20455040c4000310b81c60b410002c0700201c06408030528080720041d503006100e46c001040e45c604000c1e500c1c140c0358161030b000d03180d071114404040e034811280e09040e4050600e41c0085500b0404102500040483c0110803c516040058140c00c01503c2d5102011552111030b0b642441500442c00f40c09848054506030305114030300b08220344446440281d40d01c0700c4000034020450951002e074500c20344100034002e001d41520340c1012802c0b1603091069900003000e4110700c0300280b001070030314400e01c004042281e0404940000003411a0310174050442d0f00c56613000001a4086100c0f4a0100d00ca4090080d111891070407000c5100d0b00304a034514002c00180b04245101c000044800c0b514980c045c020741c4800f25210400c010096009008401c00a604800888051044000804000c2001c001c0c41d41c11903d5940c03074203a0303a14001d00100c013410103158000700c280c1d4040200b01141080f41031401920304242c2451600224144c002d00110f40003004007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 959559874 1250 959558624 959558671
    0x1b060615120b092a04060f0813170f0c1b150301060509012d0c05010f02091e0105070f0602120601170f0433060501030e070b0d2a08 58
    0x203541c4043d2000540031130390825494182c461070b031400c00500324007000c0340100b4500c0c1e002e55958292407650b22640c0e0151031382c90f1154a0703484c41c400010034410140c0700d034140b4002031030080d14039081c04500c21824400c0c0d010aa9007021150a40b9100100341c80741703000c0c200e1034000c0f000d0b5401c40440b1034a038550f5040500013810f0b4400d140b007440c140a80c0c10031000c2580c004619103c07034920300d8064110742400034140101034904910081c0e40e00e6082110704c6500850034130891b00c19200080c280368840072841208420805031603c01c40c103002c014407414000c500c100900712181c62140000603914455041190780d5408040e02c03c604120720147c824000d4040d10039500d80115140d04807159a40e56807903c0d4130181c86045010205001d0224031001d40c004d04840d400c41042d440005001058941e0011011581c04461a0540d9440b10b001000003140601c010501e1400d00e03080420315141034a055204942c200c0901404ca91190682d0202c140e88050700c4e0390403411706030141420540c0e2210 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 959561124 1250 959559874 959559889
    0x90e280302030d09031205070c050606011d0108130606062012070f050f07080a05010b030d08280203070903120e22020c15011d10061b060615120b 64
    0x12280000c0d0b03440e074900d41458040c00c8035071031070700b0703a8a01440b2914041800805507103109e4001c5626104010115040f98042c80038808100048584ca030380c0f8960100044402480240203c00806c170040c0b0098045a5103015850183c48152140014089a42c1c11011440300a40500c081600403245922001280404448000d40c0249100c0c44548a0b810004c0c101401c14078000c500c2e1048210001c8c404001007980804a4002d9000b000f6003d8101c05240d100d400e000141400104088001602d540a101441503040c04d2005003014005104100074103ea0081da0303c1c0010842c120310800c20030010b08a01004184689848506001d015020444441b9480d4410f20f036510800038001c1a980c07540e050b00c51000c40b40040381c4e40f42070301c41c00d13442680700c0c20f01035112783e0307281e0148030f20016901003092401060300340c01c1012803601e84401291401c000c0f00030600c859980310210808112a405a48042c180c4d09114640c4000a540701510160030b006040508034102401207805075941c0d81e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 959562374 1250 959561124 959561137
    0x50408040b0901051b0c0a0b0c0a0318030b070c141626150103050c0a180c141b010e0a0f1b1d060406120228090e28030203 54
    0x104881c2c03140300340b00040e2100e000303032074140020050164030b00e000e183c4002581441d40360155203c16085031556440d030014440d030103400d100b41d4419607807200064440d180c009240c1702510005503040e500d0341d803a907543c42c02c1580e00d40b001903c03061241e0184030050303508a04107401c0d00c0052540311500340500d10201002e104403986c090210102052101003e401e0441120b00c80c07007038031000c0700c6444000c64074100a0000b56214440c1040c03c540d41e041c5075946605480e04480584000c40310f49081001800320401d42c9800c0100c401404001e200c0d005015004043c101c00d010340340012085220750854101d85521070181d4410140c86011443c640514030740980c000d26017a19107044103a03c601c02c9034080d400840e0303c0142480c3d4100d0240703071800080c013900f401c41d01130100603a030310040780032407040100103035010f80560310034451010071a44c210401072129034864592035072885280c08446201c0200881d5402807000b002e1a4110000402c01044464078503030844905510000d540e8000c81c13 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 959563624 1250 959562374 959562389
    0x11b0201080703110a05030a060803030601140d1b0804060b03010501060912050c032d1501120c0b0d0c020f24070324030b060a08190213020c070e010905040804 70
    0x5070042000980301e41c104000001d012130305141c2e500703003810004005500458072021a1480c20201140da690040112401000140c0d10141911802000164294041c000c00d81c00b0311356444160f600303a170035103401c5501c0b48482e44a843c0700c1c2c0303014101070040c3d0f180c85c00c903d031003079150030018030180390444044015640303600c0c030b81c1c4507400700342c03a05900c0d111100002d075925107c0c8203104060703201c000044042c0002c002044c0f980c040031a801c0103179100703458140d0f08a6010040b0040c0b0600a1021003141c0b81402265080c40c4a03a80c0ea145009543c8948802a8410b44446608103199010000b00d105003540f10014141c40d600c40400440c0010a00b4100720640e8900001c0b03442c10740b00340c002e01d00c0081086061009080303481e11a1060b544d039807000302d8608800b0b0001644515200c0880004c40342c650000e002041c1200c2030098039a107d142040746d105408154510141c43e10344050404c0c61900d0000709105130600b20300f8291501c1c140d01c4040a542060208400200c04805031811110a07 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 959564874 1250 959563624 959563637
    0x504121407020a0b070507061b0f051005040309091416030504051216061a03100f0207080403110a050306090c010c150507030c12061a090609090405010f0506011b0201 73
    0x100381003a4401d100e000e0020b503104004800c0400c080038810010480c8a00c80d1040320b824990f81d440550382004600c03280040180000e5400c008600c0f00310010000c0c910410540308903034030303030380360301080380d60a68041e40041e084050501218106201d07807242c0c910710100c0b05407186030030100c440c0c101c81086003040800d9110400701d42041801c021001c031803c0040f85aa440d20000342c0e03402605050010156030a5051010f40146190400605800890045c01030110300c040c0002000252004010007640b45600304120f802242032500544080c2d4841c800c0c03200e2413008202004072402c62034111a120341c00000502c040e290000030aa40c81c40001e0a10060f20912810440900c21800e201441020b0810082203400380e0305a00c0ba0510003001d0715801680ca10301c80d450011600580910203080e44100340c48ac40b0180104041c000700300d4010981c501d0134894101194410703109460441d411380d12080b4820941410340140381d40b00c2028a8102d02d221070010300495042070492002c0d060014 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 959566124 1250 959564874 959564897
    0x10b0901181e0b0a0f0302032d030703020718020a1b0501110f0a0338060f040e0912090a0b0705011104141302040311061305031002030f0604050412 65
    0x225030802d200309407507070540840c45450710380c007600034000340e4102c984603000001c0301150f03444000b902da0056a401800900d16062589a9a44094044001c42510b085d9002d00c000341c880040000300401c0d4486d501070a03a1928040c5490304800c803000c0c540f09041d0062060340c29965129820701200f00481803011448201800d005004088060030704e080c0030f400248950150141030024101c2c2010342c0c1c0c0c1008030703200c5803641e41d4101080000102d40004006000501c1201000007110003d80c024469803a00c2c1c81318004010580c05640809803600da07000411080400c140b04445260342800562031804038a00300081d45040e0364010340c03079904000f24005050110035407001072101e6100c07071b1944c1e40c1d54854030f550969031b00300c42c40548a0304500321843e4040340c40e402651300301c0741d118084181c1502110208500f582101c83c412800c1c80071224000b849503000c02c2026440d0002c030800695070f050401001208881c024000d50080381807034103000c0040d2260141254040c49072038085403c00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 959567374 1250 959566124 959566169
    0x60c2001051911031630200613050601080304034d03120f0405090603250e0a0b130f0f06080c030d020d0207030b060604090e010b0102070602010b0901 66
    0x20b03925005600140700c045440026004030308510701c2214000e401c5454580c0440000074200003040103070541c180d0100451411b540d01814450044440140408031004040030140385000022501e03064000c0201c9080b60601c030007481400d000d4050b42c0d0266103402e05540b2840d0b00400c1d4404449400c6a41400c0f0980c5c9606401500c4444900140510044000540040503070b40b04403901911074007841c40c1580c030540140c001c13150605a43e43c2e50358241481d010420000c2c927002007880e50180600904016150005080100f22442c40007a40d0b1000c0e0805168508203000200a02c0c0c1c01441c007291008150745102c1068801c4120507008106a8060004240504401d801c2904003d0510901180d452800700d2120301082042c0d0854011b000c07070940483e501c80100300c0c810056013143d4803d02c08903082d600031940c00400a00341c3c0f031070681d5488a000481c1c2d261409980185d540b807003501c0b02503074140036000c024140c500c001d0040300759110014008000606c40c03411198407038001c00500c0c1c2c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 959568624 1250 959567374 959567387
    0xf0d0803072105040f030f0c021f02010212090715080402061c020910030501080d0507080a030f09020a06030b0f150a050d06170a06140c07080c16060c20010519 70
    0x1d08500c030b00780241d041c10300e00010040d90b1844100c01040c1c503030705a601010f1003044921010340e00103040284880c21784000100d629084001c5004554003080210352110035000154010282c0000820000c1d00d841800c4608203036140b000402c01c5091000c2c400540d984e0829111282c0304050340d01e01c800d410f4000e2070000e11510341c60541000850303480301d40b001c0e0160322141c1242d03405420389051042c01d00e0304070781d14031035454000c0c8100d0091000079080c5100350300006450546040c00035100030705800085c1c044406a000b080060748624141c800303410080d44040134407500b5280b04210400c0a1030001c07240c0902c0c00544108100400c00154024180d00a1002440344441c080c000741d600a106a88420440c1429a41d2608104401d2852075642c04050703c1361040400c0c1608065803a50b40402c82e0380003040000b50b074030030700360350000800441c0700c0600101400c1e1203140c0c202156207800b00c01c5111894405480d41120070a41000303981180486892000443c10068200f4042c4819200e4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 959569874 1250 959568624 959568677
    0x60a05060a0503062814090c0a1112040329060a061409060c0d11030a0509010503040201031401180e010b090c090a090501060201050703140403090e0a0b060313020f0d080307 76
    0x1020340175540984140841d00240941d000341c403040400149807000e1245140080d00d4125400034104610243c9034446c0844000d115600b0055a04121205000113803e8000d03800070380b5280810072481c80c04640003a0325400e903913003180030300c0e50030b00d800310010380d01200da13200382130602500c240f1020302e445901003140c281c01c03002400f40c0d8540e440103103115607850411102c1c03000b042c044484844944000010703161204180d0f40c60515045148004581c0e580019004234145600c480c104000b4120418400d4013a26402a0f2003424100c0d12140d0b0040e02c00c404d12041c0e240e4900412444252100e848031607002c00890510b40d40e485d41080400c0c0d600b072940d88003110844c80c200001c41c0c50b90b41900071a02903019a6410704c648910000c040b003000c0b0b020b84d8001d01040c5c03080c81c108804218200d18583c03000c1814000501241e4100c04111140e008842c0c0403407200c6102c800101714500105480c216540945411000505943c0d81d00c10500c8003504420500188940400c9465100c0842682 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 959571124 1250 959569874 959569909
    0xf0f10030e0a0f0309060c051002090616030309121803020909282f010f0203130315050a1512080403060c02061801020a20030909100905060a05060a050306 68
    0x80e10601c03414000f141c3c80804204400050000ca000110140701d00010100d4035000710141110b010030070203000083d4014460786802a00c00d00c664813228003070b442440215030094502003032501161900000f10040716852106000d0100d0100e8680f8004010303420540f03a0603901c40703040e5112100703440d240201d0341c40c0000703041c207461076401d40c210f15442882d4101c41c443c44229105141120f15869003049165020b91f031880000c140c81c080b90b1040c0410601583c031401528075010307081c0c401102d44291a0801d80d040c9056220106100a1a10034107500c180d29600400c225440c000c072034440741d2031520641c00b40f449001c0c1c0e09010b1204010840340210307840380c0100000d4100c850003035210f41049606804084c0100ba81942c400018001c5904040c403650300d1200040c8081a82c00c802001100c0354280307031005000d444044e4440c0c1070254010600d00c50740c2c040c000c1c6007031500d405881d402002c0720302680c5002020081034465405070341c0d864840342407080c2c1700d50301c2030040b13a0004258050b6a0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 959572374 1250 959571124 959571133
    0x910091a040f030809030a0c0f032706120905060c0d060f060314090a050c0d0303090602131712030c0f070c03030e03010b091b0c19050d030b0f0f10030e 67
    0x700b0020300400386109a8400d803130f003141e00e641d40205692240511244007000c07500d003031690000103034003044810a0318400d00740710503020001c4880007110381580001c1d104110f0004014003001d90080d54404024981580600141a09564080e10348401806044403200045040050800c03650090005007840d032805030a1156228030040151043c00b5001130009840800310326070500104010001300c5d0004000d01480c4040020302c100ca1a88420541c10159581c0e60480000c06030f00050a881c041c43c2a6040000e051866181e042002c5618213903059024404601c4403689040580742e01800325040c90782c0340d415441e4404064400e017000240a141e02d16004001c0540100140d54a100e05a008019110042d41840716540c419180300404480491807011a0400c410080410203000010345000f02800c1807840400c0c0040c4504032040d80211004950f0583e0520600c204030804940208030b42080d1004607900f030402d003000314010703101c2040800416000340c01c007020070480380b0200d6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 959573624 1250 959572374 959572381
    0x1d0a1a04120302011e200f0c030c06090f06040b01050d0f020409060f06120c05040e012306090c03010e15010e0a0b0c10060317070f120302071a0910091a 67
    0x80c001d0080c4c1d142c074603041710b00042074010303294544111041c1e807050045100b00180402040385a40d001031149903c00d85013000a04181407081c000380050401c0e00c0000c0c24242441000c060170406442c4100380503910640401000c640600e9001341101d00907074422603011b000d0304200a1030500c001e40a5082810080054100b2000f940403050201035103800b00b081d1303a250609442e503d4101e0001a058213841d0078103006620313159000c150640304540c000650a1540e003696601403441303854005860f59010100409802c0980b400d0f984076441900d40d500d958140b000b1440c0c805400350880003004d00c140d007081c03503503406045a800c2c2840c004040c1d401095403000250078551041c251080c46001d01700100321051920702551090b00c1d84240c80078a01d0100191801c1c0076006141c064601a00c4421b0120102e100d4091a9a80021994000d80e66030701a0030003208003559451074012442c000810002022004500d06e400c07003d02c40d01c0800c441946050490050340b00c604800c20044015027407 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 959574874 1250 959573624 959573627
    0x27091308090d1b05040c1d0a0e16080a060609030821090f011b14070501020712050309010b030714040f020405031207021221030403050c1b011d0a1a041203 68
    0xc0c40f15060280103c5201d503900c401c1440151464400410701003031568800346e854602e10f4680c072004c1840a400d440c400c81e83c5451214050105850851070480b11181030080e0340d0340440d0f01a030060300544240030080c6003c0009202801501c80a0f000c01d43c04100c04894031030407140d0500d40450f403184142d080c21708100050b11002000c4481c0001e629008025000c0b404016603281c0d51085070310b404010001d91b42c04424650321480c001c640c155802c00003c400100e80e031244841c408a030380e44040d22803411422941c00c60305894500ca11a9200407010080c03115206580d40d0301403000d0324041034031481e51401c20068040c03074001d43c0d41400380110f200c04c8a0850000780018500849100b540d0b40440382000e5101c1355021030442104c07001d000d100d0344084000780116041340c07280c031f81070341f070071018500c2a400d180080381440781d84160030b030f8041041d42c0e00c0100c030490341e200b03900300200c0c8a0034003000a803030214601c6580b58a0704070060b20001103c0380c2003550001d00001c003003000503a032907240 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 959576124 1250 959574874 959574893
    0x609181006060f0201110910050415090501030612051f02070c030807060c0f0c0206161e11040b030309040506040b060a0c030f05071e110604080327091308090d 70
    0x2e9200010b030341584002e0058030500603c2c8202450b100703203d1402d4035031b0040c0030000742c801c0421004d0100406c000070f40341600000d040c80c003100310303035800ea042810200010705844480d441404103582c5a0b03460804180301160000c0007001101190180c0c2c40c00000c0d103000390103000405403100c0d04114000090200380300c01402094400c15080110400040c400c1d2149009a40851f0028003602035102c01400e003940100300410540107410840c0200d60b8500c2c5030655000c401d6024440d6480a500070000702c0c901e01c0210702401c407000c0c000c4034000300119030b80c2c0c0100403005104503200e00200300709442d61340c1700920400e0090146969003480b2200580f007070751242800ca00242c0da260940c0c440c2d81c85802a45c41c0c0750b5000003609081c80c0200400d64920b00410015198101100683c140540e562001440203060700320143d5120000e000510102105e10a405404040d00c09a5503c1d10354030030b8452a484220301554000042c614140307040b180c003d20304140e800c0508415400e040c8001d031034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 959577374 1250 959576124 959576129
    0x1812060603051009260d020301090c0e0a05180a0f0903020303190b0a0501210501120b0c07031403090304081e19081822140a0605090609181006 63
    0x1080f41c0304504001e5004048590501d406070a0b80b00700007803e000c1d00b0030780b04441c940f07041642006003030665144000c0205e0344283c1c001c205041c0d6690094005a81040c08440c40e00c2c81241d08004042c60305012400e001911100744410741c0b40400000c00094003540318640c03c1c04140c904200d01c2c00d481ca00655179500a07105003581001c180d41e4104e40b010703540981c12024a01600099900b89030074015a22280d06603c01401c14580400e1003064401d2031290600a000c002c80155030095282041e00c0700c684041c000030021007082001d20042a04450440c1c0380b8141000b109941c4e64138110440d0450250b600842410300503010620f034401d0b40b981d508032503028000143c1d048002c1001c8110591046400c00501035031041c082c1c01c0c400d00041100694105014103200043d01400000c00c5000d403d200100708465520b121100d0f680d81507203d682d510400c4c103603082101c1130411300019454403004100754414210300c40061070400060f03011041036503040040b01d00b9560b80100e0040a09000d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 959578624 1250 959577374 959577383
    0x110601171c02032a0318030f0d08011502161509030f11150a140307180306060f06091d040f020603040501050603010f021c0b0a150305010510050c030a1812060603 71
    0x405086607113103508200c01d6188070800007145409082c0c440f08000004403113100d070703050150144c010110032042c1306518000c030b0380b580c95810703d41c100424100407201354000c0100b198010440003071806401618542601c911723000d42071849030302070002c80740310080740c00041180080c0743c841c1c000c110380441030138441c01048481d850f07242000b0406500300e000720001600060351800700c20301002d80d00002550030103032504c3c001c003071240c0700304035003001d442c46500845d405540c800c001c1020b00404943c8101403c80e606d00710710224903000c4213421b420030140400f2410f080880200e0b08200c00600003280440d03002d807200303899290600b0502e008100c100c441502075408c20000002141f2544205e910300001d081c984c0e0707008070365924003d008000c031410040d000300c52044042909000e0880e40080c401c1f00c0c0c0c1e0041429818030081c40244c010121070141071010610101c02c4201d400300948100c1c01c0c1a02c2c0c80f070305413260003503401312005095105e00072075445003880009004140d046201680d015 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 959579874 1250 959578624 959578657
    0x30f29041e05060a0f11041e0603050403020304063e0616050d02090d0605040c2c0103060f0f0f0f05010506031501110c03030d06060f110601171c0203 66
    0x34104841c04001d007120004040c1d802c40e00004260440c298449a010141d13030000050750b01840780110140e900540000060703803a0350340800380c030201c4015404054545860148950300386030394007039034134015405050140641300c04d10002000346048604049081195180c0c00c0c1c1c59400c03107000e2160001c02150b11640522400181443d0700e00d00400380e03111144d0b5856242103d02c0c01000020741041d0912a400003008010300040389042c024031340294041c0c0f000711a5140341080d000c440741061461620080005c074500d0140344e020301103141c110381c2c002c1d60104040900641d0740c4010039103a04401007052410f40024007194086d40b00d105c10480414041186907284c42c100304c02404103e0359520b0000d25203040c0ca030a03510610b85c0481e40c5c0d500f5411034024526900000307042d40c0003040503100e00c0307540d0703103040000d01e9100859200300d80341400e154044400b1075901c1925540e05010700082c424041080c21890300007088401c0c00481c220122504081c03507140001e44a0b407013441003010b00c404 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 959581124 1250 959579874 959579903
    0x804050625210207140409020a030c0b0c060a0c080f0a0917040f0504090c03020609030703080304050d1209050c0f0f090c03160f021c0302040e07080f150a030f2904 72
    0x2e403060507201e032841170308000c107003002c00c1002030124103504a030270200c1140000002103c1420380030140021100032503c40ca0f9903081c0038a040c500610903298076060bc146140b903903030004001c40c0c1201c085003409810340c0e07030300c200300c03001d01400740f0000c011488110014101412000241042c3ea01d83c50680884a030b494042105481403110060410030076160108014684131000301002ea50140030f9503180c42d0b0720342300d025180d04211402c0e15660011401d00250340d50081070704002101d422010410011585c969542e941000010349004200c1c0c1c000c80d80140d610520f5a03442e60078003c02074080c80c50107108001c51030300242d03809124410180080e03140305000f01098140c0c8141980200309134001550f1403030801e011000c41d101816030801c40030808501610103207100d50303650344800c01c541c20035800300c8589c0c51005044007420314140449000503500c0b1500303001203039004446180251010b09001c11414480c001401c0518802c020384280d0100c01111680704900501e038204140c036 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 959582374 1250 959581124 959581127
    0x70c020f040b06030604050a110703050405030d030c1d120d03060e091515060f04090c09050906150705010b040606020d020c09040b24090c0d0513080405062521 70
    0x9803050349843e0720502c2840060b85038200390340a03d610070b00020b80070806440c183c0b0b0b000c5155014100950000e1b40c0010148010304041109007440c08491500700041032148000a00e400350201c00030403203003400c95100d802656040390300c4804000d50300030348503001d03800c0030f01400070039031840303084400c0c0326030030004600340808030741d84d83c0103c1d041d04940c1c00b42c1c2d1400e104082c485007485440398802d1041c04103503504415080035001401c5d1800001541c86200f00028080807003660106100384180d00400c2210f0f107882c6002c6a2030002c501189407210050b2030440d000d40040d8a813540c115141c2280000c0d0a0b50008440f60706515030340a071600c60100e41c00344500390500f19006000c0402910118180300943c110380030305500301c0380c107684080101c8800070b07011546c103840d810b2480e1000b2451001e41c8503c1c3c49055045000c1851400c0c400c003450390748180500492164074850034000c261680c400c01c41c48195000e100d8400d41c02505031559207406209151a4180d54019044003071154540c0c0303 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 959583624 1250 959582374 959582381
    0x3903060f091d030a050912150f0f0603010e12160f050a140105060603070804080909160e010c0b07081008060408030a0b040510170a06141e310b070c020f04 68
    0x60113954842d0716040d40380b01884486803414814400c51320411240f1000d5281142c0828058528600c0701300701400c001011091014000d0310880c0b19034501850132148a03000140d01450654441c4509e4031075010b0b040300d28840c0b01d10f6502822458401c042d280810101040b0003041601c5015410a0300361150302480c2210743c11205581c105d541080840c018502030b2480c9035200c1e00c160f41e114601140b01012401c1e10303006507aaa8140604100d84d0020310342c000018202002081c41c3c444444a95500c841d02d000d50064540340600c1780035401b088911902004640c0601001c000b2a4000d0600d458150800d9200f101e10350200341c584000031040746052b000b403074050303101201c0400390a41081e1a80c07c0001503401c421003144141059040012801e01800b024030303010700c1310b4688034949000701d1241072034607500b00d54280e219802041000b915609040c41d2401c807071100c07813508100900e00b540090549446c00380c440c03c41d400400c03500d039521001d41d8100d188241d074004080380d800e0091100740c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 959584874 1250 959583624 959583637
    0x8030406120203040807020303070f0201080c120c09060412050f06331906170604021c020c1509063c09010b10050408013903060f091d03 60
    0x90540707000050100120b402964029005142c000d150070015800203103150300164080b02c031b0b50b51604500d030644da048842030350b0120b1619011403400714000c0d81003d064800400300e100002c0007140440481c0c4402c3d09031009040002d85039a90414035043c119a50481003c515019105442c0040e0030113005420071103640ca070080035441850341e00c0040b03501c41d446030280305c2d0f044980404d29402c0841c0c000034500007014291039100c2e40e042410404817007141d00800b1240036500401800f56a0a003800380c0f01b8400040714801078680c10011400c6090111500d54030f1904480030042c80b110100200c1e0060041c030700d000101c1d89808600070401020b510108406d403c0400c00c0308040f08145a0802c2640d0010324003000040c10076911001405001e4402c07520800038602180c1402080024895070512442020303042905007044541d20102c9414003411480046214040c042c0c684d0007504031002405110303184542a54444a000c0020711500c1c140c8500c0c0207080000a103c0900403081741c55 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 959586124 1250 959584874 959584877
    0x905010e012303100614070803070f020304080102180310061809210903120c0519030309061d01181208280b310f02131e08030406 57
    0x124101100064070180c400c00d0020480160303104040005040b48001148103031a034001c070850b01d17814021700030f20342030820000c0415101304000c80b6000c1808141982c2d407000c520b1424400385510150128154025603125034255800845c0082039654104c0d14103108450950031110807608400c2a1403d0380c6040c49000b0345084046080c00c0c07031005503003049075102c0c0a10545400441c02501d00704880da4065040030008200074014001c1009101d001203102110349400b24051105864440d11846444200c0d805807500d82c015404040c002d8014102e820b800442c10800d11800c00d01d000e150308800150000294a050400303107644260b1003180003055004400c42c07a41c0200c101c03043d00c0141025020724800070341c0070740612003031100c0c811a071856620200041504440078003808261800019030701414554030441440c00d02c0100e2621141d950000030101740d400c0090004c80c024800d41d010050034011030403010070310f40e02d010345440d0130034024400c6400003559245800c5c0c803406a07009020 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 959587374 1250 959586124 959586137
    0x20301030215070f030f11070305060610080f0f0402010c06020a0c0c060f02120708040305060108160b040602030307030507031b02030301080714090a090204020d060e040b0115050d0e0111040605031006090501 91
    0x40100c0d1192101541c80d40c11410041c10074690140d1f00c0e40740820a50084032036a0043e0100700a50030080c0394160035130451b09202490b8140f103400003400845c0140246440304504d40010150785c821804c5810164000d40c04641c0c401c00043c009050100c0c0a500380d07900e2625881c0058058440d134040d0440003d541d014041146860310220000d41c8240c0040c1c60f5004148800310214030107000c0c0500a014a01c002e00c00c3c0d6a103000510442100c0e6888000c1000042c401000340399000300c2100e50007042d919001401c0c0c4e480300800c0d00144102030000000024151401c0080ca40000007107041e180b04008807107159540e50a0000101d616440c030300c3d00103c40001050803030490703070010322010344018409130401c0983e14000040b0740159001e038901c0016801170000340320362094864054108801182c50800441c4005000c501c105204420301c0d5030345400f6890460800c1d440056603241c0591030b41c0d40c5554441c0001c040360008e8529160320400f80c44001403060094000e0400c45c1d0040c0c6426 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 959588624 1250 959587374 959587403
    0x8091e031e03070b07112107061e02040f060810031e0c030b0a050412020106080c12010b0907080402130e060a0519090606060e0a0b040e09071802030103021507 70
    0x720788240e103400703a036003584400d0140030006070619861a01c24840d03542d940484090080c00c0c1480c114000103c0340103810311001110701c0700d20707103422200d07000e030000f0010444032848003100010070303000441051001c0c070200c0c1c085142442100704008950321591500d0494640080e0f0504c10704030380c4801840e100e4080ca204505c007d609025800c0c0368014000f6500841d582d0b03e41d8030304150304a6102448135640d004000070001c0350340155018031f002e44002c000c01070030685619071701c420780030701e66201d114005078640c4400400d40103030b0074900024115900509000e03c0c007030302a4005a40892003104070342441c29800e00c8511401c2d18000180c2c00038a065100c0314204401810090240c0c1201410303e841e80e8107140103030060000c040d04c10180019818a811002007000300d0508801e03100c0c2c90144800c1018010b004159130a44903000f140910070f44131102e403140303040710130303440b402d84002c84024501c0161069405503040303030f000740d44482010010000034041c40c8500180102407025a41e1320 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 959589874 1250 959588624 959588653
    0x18100f061a180d120309140102180f041d01020703031805150a0f2307090b0403060b01022a0901090b0105030f0630070f0b0a180e0408091e03 62
    0x281880311006003500c00240f006440320008050072405800100b074444150408000c110b1500a040011840085041c82d151004084d00110301c0c5030b2541c41010030003070780c4181c2da40e10303884401d4045c0114002004013440001c040d0103500041403e4002c2403030300c401d5001001942010481540d40400640513200307108000032034412018251904140c3e0744c41039a0b04114481c070604041021b80842d84201132900020390290900003040c150800102d000200b0401207400d0a80b07090b207a001c1e80100e89000c0d00c1b00101e00c0c1500350104105101ca6802c90010000e030b28801c1e602c0101015a00c00d03413180c1e25141010141c40e2550480c0340044c004200040c0c0c0000b41045554220b0002495582c050282450b0301c100c80708010b40c2d1203900750050680c90a0b0150401142e001800c1c240030720f4200526002c1d01389464020341c84450709000021440540200182e001c40004c5d040c8810100d0071030605007407070203954100900241c00f81e8880444400313980d030014022800b1040003030007040c40680c4140d5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 959591124 1250 959589874 959589907
    0xe0d14041a0403020901090207060507180e09010906050106091502011103010302010e0a0801050c0d0b0405010815070302040f230409021f030209030a03080f25050318100f061a 77
    0x5080441e00c4081c0000710050b0342c1e071020203009160000000da1241490f0501d0b00c2101c5026201805100e1064041400902009051001c440344180229280c0d9101e0a001d8003401868000520b10382c500000400c0c1c07a40c005c21007000781c8459500070254907100301b00a900701c80840d56191503200c03040c401000158404c1c49101a10b1802500320720110b81e070343c101c481c00c2d00c07001d0f1000682c05030b000c01d001a1107196840342e003400200031070f4140700c0b9514103c00262189605108a098482c0c03800c0022032090107038044500400400c102c80680769541d54241c280c2504050342c0505041c0918048101032a1078001c4214440e0028241c001c040310740000b44d1310110341c080341501817580034014000d4a036000e2142d22012030280d00e9045407890700407040410200010030708815030f00c0d1082a421481c2c025508050414201d0600d29a40c1c2c8400c0c407120a601401c580303000d11449010380105c1c00311070f44d4110400141240700c2c10b0104944403003658004604112848280c12814000d40710100318100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 959592374 1250 959591124 959591159
    0x14060f04030221091203091206060d0b040f0b100512060f1504060b0d090605071704031b0210090303081b1204020d0b0129090f1011030403060e0d1404 66
    0x2000e150040110100f0b401101701040a0042d810104484495080505500000203000000b402070351070f0207c001180c51582040c0900002d2801d40003800300b054213071543c001c2642140c1c1014192030410302c924003150030741c0a05030150010180070908401d0018105000d80039441c1d00408a41d00e026104220621001740c9d00c0c0d2040d240c810000c2c4403001c28000700a8504a0507000c14184110b023004000c0d5500035001204100000480802000c010f200d01a003295242c58480680440b8501c5400b03e80c0034010069440301c1c070003101c03003074058010200c07000300c07407007900c46480560740d040250042c0e4001c0010858440000c100d8035460307994191010360700a1000b07002d00000529901c0700804030800341c00c60845000001444104d80d908082c040240f45031840100345000e821030042005a01448002d034001e246048a202d5814002c1c44030008550300303502101d4507655642400313130250000407040802c90195002d03400f6414401c489140128142541013481c0514210307c00340da009024 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 959593624 1250 959592374 959592433
    0x1090b0d0210180b0c0115080a020a0303030b060f0d020703020f06060a0314030c01020c0304030b1f150c050f150903030c03011e0b0a0e03060f1b0702040e0a14060f040302 75
    0x3e0000b088580000020b06040182030000180b0000054481010111103070400790040d4080d102100040e038540500b5026250b05d0b2a021402840610100d0640e000c0e820040890f400045414020302486070301a00700315000c2e508645210030f816030406d0721188190741c05c54002c50142d10601c003082d0049244e86c0e0070000b8104a07450702c0040c2095500b260002400c0c10050b41001a080060014903120740d5040304403144000700c80c5040d044e0040d0075440c6071040c401040c14644588100c140150b80e100344e6140c1220542c1c00c1c5025548a8079203441d5061002c00440040c6000b044480320000f0907244101010301e04c080c69070f420301c1807811141250702003031480894182c00c00300341134440a000d0b010301c0794151985524090704100f05400c088004040604d41400c0c0b41c100b190b00744c910441840070022000da01076943c030060021401800090703800010510886108904102e0a0fa604042ca000075005544203900c50480100107132200b40c2d4082c0040c0d002e0800c1144001000d0360308950307855034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 959594874 1250 959593624 959593667
    0xe0102070e0c070212010c05030622090b19050c090d02031212011706070c0803150d1101030e0d0801092304111306082d1501090b0d0210 60
    0x1550340c9041007400c111140b4900c0d1402060f40350440c00c01c1d0b10303034600d00100c41c030007403290310740320100140140002080288180d104e000b00d070400d5050001d0380c00300010342c41010b11841400d4208106c440d4803d542d0303841d1070700f1070700344010485d112486000c0c050f1049240701480d04041c90100141904416810b030707494081c40c000c260940260f04020500e1151200c1d90443c15032602e2042540100c80c1c1c83c1c44001a00443c04009100b64800c0308030440d25480702c070094030b980300c03e240c0c4601802d1207025207801040300b4541000317200c914113a00d07500b003109923014019400b001070125241c000547c0c03580c010848520050000e202150404442410554541c0075000b00555011503800001d403001e8901c0d00801341010014185841031004415103890148001850300040b1641d030608507006004070030031040364142c1243c01e0615901c928409030300325188a14440e401d003c2409007032041c1c1501300d2604144044600f00540c640321000e0300200b4101440c100d4540c213842240540394000c00705243d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 959596124 1250 959594874 959594879
    0xf210e0c030d0e0103060f03050d0f020708011a10020c010c2907030e06100b07080c0102040302031e010b1e060918090a020112020c0c010c08070209070c031e020c010e010207 76
    0x107041110380144070031030381c50000340104900050219005074020341080051001d061002c0f980006407050b40240501c1e0200d040c281901e8100d0400c0c440c2d800c42c070960b50070b003070103502c0081e06101d4205e060300044549411880d40c1c84016aa545540e0f100710340070800c042e4850021a070044112580040b558040230340c0115140410b0a03140c2c8116001c501090362814080c8a10008021099000c0440041503902c2c41c00c2031482403041c090300c038004092032000141c01c8070104003901641c00440d8081c0848034034500d60b8842d21100d900c0c99006055070340c6004d41c500a2440c05104030a002e8035010801c0740081d0800041c040554000ca580303035080b00001405580d08085160b40038071610301ca101920711102d03688001001f1101085000d000203005101c00780c080400407621507920340090030581540d552914040758940107111001e03500c8080b0104100e20f15400c100080342051290351a00421940d541d0b00c00a9500301229030710040c1d118022003d030650085008209489050040794000765 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 959597374 1250 959596124 959596129
    0x20613080706091a0a0903140901030e16061206140d051501090e1b060901080403020a12031409160306020d0b0405040c08160806070c080f0d05070f210e0c 68
    0x1da4590084070001c001c00c1854920580112900360051700f040340512904d86142c80c0103124a054945040180344001170b8401d02d68002e034000300d200803a141c25114260000301003a10000300510582004c45c44c901d0889081c01d599100b44d405503141007007450710050209080c8010000200c00032212841046858400502594100c4c5d00801c0c0302900400c1c04503241a030345043c400c1254400081032500c40c0b01e0f804540d504810f88510400c01c0c41c1018880e80c8a00b0308904d08924100c02408803440d20310342e04000d5500d6040110954034031528001240c659200c8140c0e1244072030700403803c246003000140006031140c2c0040c03004030600c11001c80c4071400d000001d41155001e40301100d982491001c2000186400d2104426901600c032000d081107186c80346491311448001c21503410031503451036860401080d5001c2e2810780c40c5450449488212188240e00100800d54502020561035050b92050520079100c42c00e13407445911646040852844200c030292190841e400654000c0040d18040342c1c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 959598624 1250 959597374 959597381
    0x40f17220f050105190201110a020a1a010302060d1d1e10020705060411031903030e070b130e1503010e1609090201050f070c05030d020f0715020613080706 68
    0xc0c00c940c0581150008180105100400305a0100700d01c080304a00030005681c006040c1d074025110700d00e544903201c0e01c44108078010b10300d00505200448010032000400307030740022840820741c030440c1000320700320030156000c0c0c907030009102c000e600c520100f080c58000c519070f8106581801a001a0b01c55155840450b02d0030007581c1d1418122038180071114140750724003040403046c1c4014012086140040740e8403070b9071711032900501c050511000d245104481352400c0001c1d00c05104011184580d409040c50003d0242070a00711001e950f1246840120710300c1e8115046070b4a503881e0301017160969142c100c0c80182d00c54028091b0206100d0f00c02c490009031800c1c01400f5201418802070640d4840c6401c100005400c59000b004c03085152034903900040c0d812000301c0304c02c040c00c2ca50082d2140300501e4689181c41e41a00000c2e05402070b607803400c05041d00051065580c9880c84182c17007985490f070340180c00c42200700c51a400140e100ea80843c1c6250201100c130202c0300e000d000c00501e000c20f143c4030745054 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 959599874 1250 959598624 959598637
    0x3020909010e0709050714031f120203010c0809192316170c01080c09031509011410030f0807060c09060906050319050c07060626070e040f17 62
    0x41e511440802070030344003030180320050314140504014900f4002c00090204034201403080140c1c9001021503140f1f641c08404000030300d24405046001c2d038540000b40781d070303048030300d0f040b806513090940140d01c860240b10400d00c03034a030b064014a00d0011100d01c503030f4040e007405810b0710bc1c1c400c1c0c1102d02c0b0300425000c0c2408150144d4400500b010381d0100d041200410050f070000b162003800c07280000714000c000c19100b1920b070b02403800203100c0c0c9400000080911400c84c42a0381440740c1c00c58281c902a410030513070300c200c803540001c01105441110000101604568040f0020100c0b03000f40002085141c048004a000b2442c01c0d05280140d510350003150800d02c892408a80506404c0140e903501c600800302030285490101e046080030028a032465050140b1401c04a454000190710340c06d0036026640d0054008006002041d030314458648012981c5501d808400400f01103034000c20b000148481c2190351215240301c4942c5c5980342e001c0c01c5042207108503203245411040700d00d034100d0303100607254 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 959601124 1250 959599874 959599891
    0x3030411030c100203222706050d08070b0c0f030f0402150406080a090615060c150b030d14090d1a07020106052805151206030c09040609020a030209 65
    0x40548800007018501842c5041e49403180040084146065501005561000122400d0b60700d0b103804484030b9111050950708215240c5030407500300807481d52000f07090044400c0c950f10400c101501d500910a40c501003000c0540018000c01031040020b03c50381907194440c90071686541001490009860b0681c8251410280b81c40010141300541c94410302011090400c000c0007031800e40b61540240103003d0081040b8401507480d0022418031141d50005006094200c4520411039202d50303007d00381880c02c00040c1c4e010a010100c000d403211091082ca20700d007070000c4c01019141b0b00c900003100c0600440300720780d4002c40b007408203050740d4076000b41c420006032041042d0171034107410311000700c10000000c10788011681410300c00c2102d07413984814036504072240a0011841d091103052510780c01078650149410a08015404440d030081c1000391070008860340102d0301e540c40384410159603a1401103003d40c0810040d0109002460307507400122211700c042c14052003203569400003051070504655801c1c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 959602374 1250 959601124 959601143
    0x1605070e091f0b01080a05190c0315050d0308061c050318010f09031211070f0e01051908030406031e0603030806030f0f071e0b070501020702150a080c0a030905030304 73
    0x15502c015900355680694600c800410003541c807040020700ca114081c4c0820710082d0303a50080f601e07030060480081c1c283c4450890a1042c040380040040040406054a190703071102d5a45c04240c6203480c85050302956055559842540c031403d08004109a0460a42819203440d000041c00104140083c05e0a441ca04004080380d4000d5000901016141502134041101e00740c014400590100c0e04554102443d16042290340481340c3c9080c80e04110341c00011201203650800150a841030b8a482d0581d0000d640d540241100148402c1d080d03900c5002e2004180c0061009126851195200e03218070001928008030041c0009000000ca855a800940018140e601000f5480c00c08003e00c003144c4442d000100360100800800315195a5103000350301e1200b9800c5103550001c05d10700325400c050415101c4466640e0110f03d020340c000c1d40849030482c020902c0d6000003601e207514200745c8121602e40d449561140d900c051607600140e02074103d070740034183d8482c4c060005c5030041020314810381c40388413035a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 959603624 1250 959602374 959602393
    0x110c0c0f031203060109030c0906035303011212050705031e0f0d050117030403020a03140309100207030b010e01120312020d0603030c0501060504021603050922021810051605070e09 79
    0x200f038410000410001907184075058100140155086011401c050340233412485200c100c2c0b082d044010400488003030001c800030803090122440281b0b50341c410000250309403006242942c00d80180e2a000d00070703400c1880254aa101c0c050145a050544a10101e1a06606654030300141c1c1110240d608929600c1d00148401d12300904041c00c40c810820040d400c240c6035600044041440707000060010314442010070003000104191509540e000b84142100421002d009603142840d210a480f080032500c000500d840c0c000f0f4156042e40d9230a03d10218050391f58406480f03000383d010002500590810098200c1d80444c822040a140300b82d40302c80c502c0115040c01425030380136400040c8514410401044003510883d4400c07900384e0706041c07240e1502018000902448482e13280140c003038900e40004842e44045038001c2190220380d020100c9000702c1c50080c010034010391049440458010000b044440aa039490040b44070301c90400ca51f42d45883c1e0b4040c410030751051701e4000041e40804205c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 959604874 1250 959603624 959603633
    0x305060901060929070c080f240708090708030c1b030309010503180a05060408090108160206061509030709020417151305010f110c0c0f031203060109030c090603 71
    0x203140140050314200c1d48407402c05a541d01080c41d090710b2050a2649035040c03515484142c425122000d811090114402e96070701130003034079078180003010714945c00f455542e00c02c03000e04100100c050607594550f00d50303e0750300c0c6030302500c4c40394016222110b50700c0364500002e090202003000302198032a130005020b0103001b111103004d07917005116000348039420502500c2c0c0940d07030040690f548110184088010340f002e1440080c102010394a0162a9006400400c003d0001002c004c0070303680004e0366100d00590310f00c1d03c044228000114903600603007011000c02c10b0b0707141c9850000c000041d0715042c24681042100000c1c54200154040c100c42034011408025204e502c44000c1c6103540c6400c050402008603401c00440750400621030081d0130011101201840401d5128070b50302e0b915940200b00000d02c00c0d80b0244680c000003000724040c424424107400c41e0a0140d010b240001c0003500400301440046405030064000405541c1000302e05580000803940006920000700803554000910741d007942032 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 959606124 1250 959604874 959604889
    0xa03090f051e0609190c0f03121e200c0a03260c0a060f020d02030f01050f01021906020d0e030f07050105070c08090d06060f0e1909030f1d040c030506 66
    0x140621180c0066040201151011801072450745d1080d010306045446407402d80c0b03856445800503d0550070440d00441044030104600038001c8042d1204000c0699440178141c2c1015285884000030305c224200c6420b074020742c0455941441d01c60f00346ca800d00580b01c0880c0005100b5401914802c1d8091300155841c1d0544207018003019a04815a24251510344969a50660204002c01055940300c0c100144207060303040d14a0300d0303560441555641414518030344800020f0080d1b03842445840040040c96000140020640e0003903a5084100c0c3c4007070b2039510007500700141c0c0028840d151a1000c2d1848020700092080000c000c030455255610b6041c0305003120001803909090298642c03039072010a01d400c094440c50541190b01703c0a001c4c0c0382c81d1500240000d41d00c11401c150800102140900140e61120300c143d0342c00806617050400081d01109030703007d1420160106800c0751914042510846814948104c20500c0b410f01101c04400325081310460b2008800013503071141401043d141c02c40 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 959607374 1250 959606124 959606173
    0x20708030a0b010309120e030106091805010b1c08070f1e0317060a050d05150c09011103090109030b0403030e0307080702031516050912070e010303121505060a03090f05 74
    0x44c0411180c3c0d0160f5a42041100e20f004000910500d070012001c0c0f65001d40010001e4180d030481800280400c0f0003007c400c0444010460340340d401c00413026054207101d4160a04079410381c880c1910101d15803142201580b20001c03d4079411048900400415203103140f1423200da024071030250081040b0305005003103850748000440d02501090620080c0e030384e007404100540e84121070300d84940c04986802460a1160f8521984e11321000c0701b006030800c0381401406260310281c0f10b0760002181c072442c032134503841400d4000703021803440c440c00e00c0441c4141031202d61161080c02d000560b40340024500c5c2c034540040c07008961013000051318204508040c03015003603d2035481c0e80541c0c14140f2031440d40742254540301c450100840803c0188569076910b0000c102e0905810a4490313158580c110b00d0f641ca082408145d0210750100d001e107048580620607240b90100e101c071810b4416090404001140c0d1000e8070304420903850740126000b03d020b40c1005980c6902c2500105044940107038144148840346 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 959608624 1250 959607374 959607377
    0x50918040507032909030901170c160807080d1b0201050601141e070b04050c12030717070b1303080601021203040f170a020115050409080a21020708030a0b01 69
    0x240140000240d00007101800d40344d00010304a0455040380c100e050885025501c0c0440014010a0190700320002c40101103036031003a038500314001002001e540c841c0000750b4008a030401c08101ca264a0445003818244071445030151601d4044a610f840a4a42001010480266840c40d03150418407550101001051050000380946e103051300018000802200d0b0041d091500040c8640e40008a181d450043c2c8001144d1240ca030035548c180101c002c0000c8070111028410401d03440c010745400c00d80040c56109039402103140084560392000c001c80007210016006c2414440b4a00040703030120b20510404503d4401d030300c85502c6040c010541c03d8042e103041c0c103640041d04024000c4500c00110ba41c402d801c0441c42d0038800e03061510b40301a105066800c00801340108441132529410b4000c01003a000104150103044c0c1c465040000b26031038510020000b200802c2000c003041e02030102c4800100a5001f1a180340c0e018200090036680002c0c41220341480c0082002254101480f8031700003004203 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 959609874 1250 959608624 959608669
    0x218040305190f02150621070902040308090a08060c190207050a0801020c010b33040504050f101a0a0e0111030d02070308130c230a030f2f0f011407030509 68
    0x11b004100f00c49003d601c042c601c119005090020328108100040c01040d5a02c0115980d0340d480c14400c01d19040200c5a900c500c8100800103608040000e52038003801c080d201d51440c100880058441245030301d048007003035000d00d034000182a80c5840301d050081800c10000340e903a002030f80c40c240c01c64401001c102d20a03070f43d401030908042035a416040303088a00060809010344808010407041c003680d445194021304000410a0702811701982a0181150b60020440551101ca452032001c020752000c000914040c840405e20a20030424128072201c107060405101600c6070203a030955104c1c19032994180d0300021340004141d0300500480d401200002041d032021050380d6000784c940c24030702c02d14001e54a44407043d0740c414100202c85440c40d0008000e0113040d81e40c1d1800404600050506039086c900048410300244191b20288800b50741007043c1c00003a010700740401c0101c031000c12543d41080008100b85105200950007080721500946400d070b15144042d04010020540c1280e5070101d004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 959611124 1250 959609874 959609881
    0x31c090302040c170a0e1c0c050a0303240305030703032d020a1812030f0212030f15060a090905100e010b03010f210b150d150c05070218040305190f0215 67
    0x380400d26900c0d0044c243d07036207000507c0350f1a08454028040b034000d04617014440303040e4109a0140d00841c840d0b00d80801c00481c2807600240443c04050398407006d00281c10805c00900040c2c03181d40600c039402da20f04550440c0e00020987c65082d0300d02240300a0030242d000a40c41000da400c0700312590040304a8442055060810300c0d02d40224003181030050502540400107840c082c02444080340312285400c00d1501c0b03140032886081240e10a5801082c15903c4a948060700e0800d001243c80000c601c0d20b0340c0180a08e0880e0507002050300816440c142c03020310304081160004c141d1207074001e100c7c903051561254101007101c140e86140da40410300482004030110307042040c000142a6a5400413000381c002e40d90031094000c41d110007145568003500c0d40740e0030410000d40d1318000618001c802410449000d19071000d840500c5041c20196000f414210311110296402001c030303604c50300c2450b00b41d00b40084c010351145020745e80c101c0300002c075400740c00d240001c5504104401003001250540300b06401e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 959612374 1250 959611124 959611151
    0x1c050a05010513020a090504030201020c0609010c12020a0c200d140c0f15030c04030206040b19032016020a270203040308070e01090314210306031c090302040c170a 72
    0x1421b88901200251500001814513000b9815104155600c10a5460070324144d03151a000304a05032500303000c24620080301027003900c00d1003580c07800f400c0c946421f600d000e07498450f080c42e890450320301590b0025a41403070700d85442d190000c148032031180207900301c0440c0345503605052004a40159004240e14900000d8030303514044012120103e003074449030350381c0b0341040542007485240c1002c2d4000b000001d000440c41045401808103203e2051b601003002c407000d001f1020794440041d4030003403a54900400008982d4035006000000305c1601d20101c0078500e6001c01c06910150f404502c25000844015951800c103d20220480748005e504520394506990098100360002d080381040041d6200b10780307e40e901131064500a1500300004041d80c3c04452074855032501018401802c096204c81420210312102c2d0a036405032500502400075141810484200716034455900020020800d8002015803980d228018950905540b8440e8907081d08004000790700001e019843d10354580000c401031403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 959613624 1250 959612374 959612389
    0x60c0a021f2003040b0a1b12091704030b07020a03080a0b0609030a2102030c0c0415030b0a0902090c090f10050d0e0105041407030507060c021c050a0501051302 70
    0x45010480d00c1c00c1e0301d010042000070007401803088020700001c031440c10074a000101441c452403007143c52403a00d03134032064030b8001d50701c1d841d900c0b601284442040004280c0118450807125107001400140710040b0780f01c07850320980140700700038031400c009414024085101049036001d5180d00042a54110320b5a0091101d08020101c2511690301c0411240d96a1050102c51007250300604640610a060030050380c1c0040303100c101d0f0f0303040e099030103408802e034008425150200c03008006040c88108410901000c0c0c2103034002103401d04000d11005c03000902c440c050038002c248110000848003014411301400c1e01001e483d07103921003000d104805041d40c07021002491400151002c46080a04681c10768a6000d02d401011f41c003810100c1d400a282d03015880740e8411800b8013041088141c81e41c01242d00c070a03507404050116004580284041401561003d89044c4050446ca40c01e0040c06071104060300d803002c04031030320b40009003901c007804401d024440e044104e412940e485151950b0000b49603 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 959614874 1250 959613624 959613643
    0xc030b13320606070c030501020309010c091401090314070b0d0203060a05150a0f0201110a2724300e0607020a0f020301090b070c03080c09060412050c150408060c0a02 73
    0x83e10002074410400800014920003103520200964881c14800b1405018008410b4200d00242d140480003500000f2246024440d05c8183c50f46402c140c1103407105e04000c402454581d9152180b407070009086007090b40240b104681d41b03c40181c5070704101041001006443c1d0101c0d10038159040e03a1452040d0360b0086407103a0b0300d10b05211502c0d80540d0310907409050100c007605016180804c030144001e030414088503100721036600030b52450000d103480900c2aa054002c00c1d050b9040c02900a07400c11318400185d007c450142001e00d460404041c1d2030400398a495808101d200d10800509581e03c184e02a030754034000300501810451034518802580c40489100141220b540d0084880664400703604c1180d6040e086000c0003802e140465003c0c21070303200c4040480c00209030710b0004001303400c80d078141d0300c564000030300b6940b0302403411b00e5001c180c0314030f600c00380d819008500c0841d051b076444400c5402175100ca18402619540f0b406c80035802c004000b0300d455045682007048803070142d8045951713000e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 959616124 1250 959614874 959614879
    0x10807050a08091e010b0301060e0907050d051005012615070c030e0402040611060a181721090c0f061b10021810020a0b040201030c030b133206 63
    0x407aa100b140c054548494404140c001319440b68031802804c2042d0062200c0c104280c00034003405503030712600400e01c10100c60302f4015420146081c001464a42e00302d600c130a00800c1158480941d1884840840c2d4081c0c0c09118101d12005500d00c24214001c0c61003024074400c13025000140320f42100c0241200e00030550303000c0081d41c41d420400c0501506001e190404082e10454549440d03520180c114000c03030742c0440da1486020f0000d4020314060180000901c003100840c519003050780d461404143d0f4400480540c544240491640d030400c0c00340d00d401c800c0d10851112810300746500c0325800c20b014800c5041c05402da142d207512482c1c035a941201c807404400708204140b0310003034500d6400c0072684ac0fa01d052440c00011003030b030605411880341800c0701048808108800c80702c0e1040c2d9803030a2844000302181d0100000501540c0241d10000908000d8240821052180700c0090301800c00002c00300c1005a850610302c003d20454011001c0c0100d025010005403000c001c041618000000c022340d1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 959617374 1250 959616124 959616137
    0x1605190503072d032d0506040902060d0b0f0a061706061b0307021306060c0b0402120d111209061b030f0304060905010e010b060d050a0e0a03080f0105010807050a 71
    0x59103588a520000b002c2d001190f40f000c09106107200a41c00b840b4070098400000341050754451441003c40c076a031a04a000c034580d00e440c80308416510001c1c0c803008203510303401503403104010b0242e21401c00a028440700d1030000680450101d0411440c40c0300c48510a0191040c1d000600045070800d0081c20300406400d080100c80e079a171070010361184596185521006602c0411154500000014103011442122a90146000f0306045001c4401d51722500740040c0140b0090004113440000c210f400a00147c9440189021240064901030305403100310001405d184106898010901010300b11024580015103011540380014102e80142904102c039056100703201054802d0800440e050840309121302500d034501800d164000f00300480342540e43c0d5090100e42c1d802c05006202d400d41079a0003c1c0942e003042d8076010024010080100000c0145603070340d450300f1003041c040001c409468803940e200b66607880d1142c0c03810069003040c0e1040b4184141c41050001d6680c0040c19149103a0b15803030001c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 959618624 1250 959617374 959617381
    0x403050a020310050c0d0b120f06101a0405010e0a0f080a0b0a0b300d030c030f090b01061206032109080105060d03110c190815060a05060a02030c151605190503 70
    0xe02364941388e51000c0e0300e403090482e041c03840900890124401c0d40802c000c0d07010641c0d42d0650390011b0b0300b0300c1a100d035004d10800c8240304642c0902ca100443c0940504150005902c40b802406c011001d500a902564400c0d801801040419447c50360301c040c81c1034090002080d003c000c9151000c21790031084040101e6140d0002c240b4014050b203015000301822a082640f1000020b00204800100140000d0400c56000d601220600400240b507034000b00182d1203a01c0c0070800c55040c0b885c2c104010303215231541e100001041041c110031401c03040301e2501c0c1c0c1241c5142c41700035042e942d007a4441d6025905040801486680d410003031486141c05041c81c4108980517041d40d41003100c9000720301e51040304001141c5c0400041c642c00000c0d5803003002102c40120f440003c01e1200ca0080f03075581e030301c40718242091005040c88005040709496034012642410f0010882074100b0b41000168050030740c4d00d07820002902190440031071882040e0402601d000141c4149900850071000350805010000010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 959619874 1250 959618624 959618629
    0x614012105010f0f061e03020a0203040f031104180b0103030e0f21010f020c030403140f030403030806150913091e0804170d0915140403050a020310050c0d0b 69
    0x64014000c2042001990707102e6168052441d0300f4001d0a42c1440207010200d9103900403118100100e4103c0d20202404030600003c9000e5403001c134060086020505c0000391304401e105110001d148941424001210130b42d00b808121202c00d070b10165440000d500c00c0000c0b4120000346d42c1900d401d46425260f0f0f04a44022641c05a10003201a42201a05046801403000400c030040040f103150020301c00039000c1d10001d4180d01903404041031a8004000c00c1000800101c42503040e10040030940b01100314060095065411503803007500840c4e282000c0000c00d182401d080001e11904004d61410b2440c2100441c20740c80328504005009940c3c0c2d20080144189681d908854103441110415652018078244126820622a00b4070385401240e0001410502240b954180c004603a1405801ea14000a40c00b54450b06082e10081c0540302c00c0701082801954010b0002d503002d10010001c0906903c14586404845208142c6c07c40c076000c10300840c00344c0c0c0300c100c843ca0a21500007240b8480344400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 959621124 1250 959619874 959619917
    0x605090406051503150a08190c1d07111c030b120601090b03100504021c080421050f0105040804090e1c08180303010806010e0a1803090810061401 64
    0x4070b600c40c041e000049500003800f802944100b5802c0c0c00312401140311418810b06a4050080459540090f03002402421100001d900224040c004c0441d00541d1400717800c0c844943c980c03600f440c04071004208155a0340201d50543c0c4a40c00c14000c1001c2038019a14a00c2041d1701b004031802c041d11000e0070601607503440c0c0c031600130603045001c0d9605940d5580c10a401404078030800c3e0302034003c03c01068818080791107520311554003e002403513000c02c50f40c40c50075960540041142c4440c2d05102c041003220055448003038482ca560f90108201c21a03080c00d5180010f003c84030790300e60381030504100014500e5000d540c2103d209c8440455003040040c0450b06140340020409600e0180400d0f040b00194024001400f039081e8000500c2c130b0149600f000398030b031300c404d018030301c1c00340c0c08900100310a01080600d15404905c845000919110f00703611454026001a01513000600310034080c84141e6080c07040c403c1e00b036a021810084107142c18400e1003500a0000c585050002c00c614a4080154400c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 959622374 1250 959621124 959621129
    0x140403051c120c0e0f06090d02040209030f24090105130305130b0d1b05190c03090b0d061707030c170c060d0c0f08070c120e0a060e15130605090406 65
    0x1051016103d00d02000300301254000c2001d128151020700301100d030034850308661000a0280100c98000301540038000694030070055030b505440360840410340101d0905c904048840700c420103410b86107281c04080404803010b0041400c80c3d24060170311107261548506280450f0340350400700e80303230310042d0b40c00303400d03a078091b409500301a1000905461045c4160710444904040ca41030401801741420100c83d140501c000303e904085424050f1118180a4042c900d00c861081c90003400c0c003a200c40c40c4030b820760449140c11b170b2440c0d1280e805102c031040c4d800c1c00d080c42030481c80081c520782e850742e110904a03030b40c1c0380728a11807460800ba01f40014a41406018004140500030540d140c050514a50041c80c1d000a48000501d20001d44540c60f48180c500d04d02402c00d950381c8600d0540e0302d0329481c046081c2c4507201000c0c00741c019030242c41525900200300c014141da4540d44800b104220900c11440320b1860380c605219000c01682c600043c1050251081d140c0c40d18100d07840d0428100031500802180c1c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 959623624 1250 959622374 959622407
    0x60f11120a0206060a0603060e0408130902162001090b0d0204050904140c04060311041805060c0a0219050a0b0a06180b030d0806091302011716140403051c 68
    0x1d0154203454001440c1c5008840503185950300f03c5e5641c4084086a48034040e0300071400814020030049002d003070180042e6000d074024501d159a96038030b0b11003282d020810041064a4516079541070015054040c00c03100c414107082e0075040240d10000b403600380785000c0d4040795000803c1110041a9940c117072801340602030014152400e1a04003541600c43d001141e002034481c0e00b0283c1c4403418640151001c0307a51000351080d0040b160420400603004181c6843c4c00d1003580403031000442d20401100c0e008400d40080250382c0c0050060007810841000103000c5403803240d03c0044001000081c0d000c4415811411002c1c0546440301c1c0f00001e8001c551100541d0720300310181c91441d106603441a0a40c460440444070340c0e80b803114040e070b1a10400c590309544203072043c000078031300d1a8040c040320809105250805400f82d112000d9451040203a500020180c0103002081800b50070910704040a80155490b5003001e14560f40d0302c0ea184500f640200300b1107071228130300c1c280798000d54402040710800d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 959624874 1250 959623624 959623627
    0xb0f120103031e050a0509040911040c0503062b03230c011d0d020c0f030102090409060218030303310203030a0e01020712050a17071a01050906040501060f1112 70
    0x1242801421501001801108111183d2801000c240a0303c122807004545840b201e040030744602c2000010070400e6800d552400c00c4c00c00c440a541c3d82c512440c0071088030f544610385c44e0705001043c00099102d090100c01c40414604480d034001841402c10301e03406030b061520080c9412103480350988014011040301d4036500214125602c0c01064025580300c1d056807048080480030843c40c2581d5039802c080c0740740940c2204800052500b00048200e00200002d40094034040c0098042011a5419030b000d40c2c42079800305010a41460203c0652000c1400b107009500f54240508400124030001c01d8003008410b1008109420f403010f51003030500d50741c00400352a00d403202c00700b02030191030004a45500500032100701203544e002d402c4441c080a40c00000400c144e45665075000380d003901e42c0020282a020901c04000010701d04411803469000320001003060394503280501c000408090710692003982480010b012581e842034076120030440a18200c003000003071030665070404066030010710f40180d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 959626124 1250 959624874 959624879
    0x5060403050f0c0906090f07050903030703050403060b0d0305031302031e0a0615080307061e0c051314131a0301020a0c0c0b07050c06030915011d0a060509010b0f1201 73
    0x4203844282c0c005903810f07120328502020400c042d40d50102c0d0f803141e1000c03e00c0301141e201410300d40c03403d81c05812810722918250084c0c00003072964020300c400b1400900000350a0003000100c2c0281e8070089000c0c0d402540003260303a50040c20754000282540a4000140400800d556040000024030303c241801d0498a8612000d50f1391580c0d0384d054152549400c10510007202804020400d080b685000c0285080694594a0320082d0002c0762a000c0400c9182001ea20380c200b01d88180a00e8001d2074444980d940c0981986900824981e40820040d10625640407440e442d00b80c55400c0c0d2035101b00c4002180320402d40c054804081509415405620114151403512741001480c45281e000700c2007414010f5a4000043c40ea00c1018001007080c1c00481c04103289052003c05590446540c1d01500c1c0081401001d041003008242e011940003003406880204000b0131302d01e010707000312480109102e0307542000e011940030a418401c0c400c41d03231000540720b06001c0c4504c0c140c511813281003146a95079603 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 959627374 1250 959626124 959626133
    0x9100507020f0a061d0a15230702060a0e180a0c0207080606031e19151d06010b030604110c01050618011d042102160603020408030301030209060a05060403 68
    0x4006203401c9000ba420281d20000034074110354204226400307039580c00b001403251951001c515569541d51504612118004140d16480800b10300d0340120b83d6403051022001c0c2461611140101440b03611084400c00c003110140c0c0b40c00040350401841c074149819841c1480000c62940004a0301c4102d0070b4460b101070292409035074001340100105a0300302d400742501c0b070000544400d01a0707009030f415404540b080f5290309801c8003010418003214151440e00714040c40c041031160061400b120f00c0581e600d54100400d00e103104059515200345a403e030b80c251028015561113406000300c9d241407401000003046607070340c1d4100d1031405030300c401e0440c0c84440301d00e0b840e0301074401591018415158000300f1110700c6240080d1a040b0303440c0144480030b00f10241c0910a08040144c0241d4501c40a6085000034240d851051030700700c1003c0c1d000384899012000c1104045900707402080030940100810081e04038000244c03410340360102c40380d1206031149070005040104c0b03a84010340240300400d0000900 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 959628624 1250 959627374 959627377
    0x20c010603050d18030b06151603032d0509030c070303030204090f0506030307060c0e120d020c090115030b0303070203010c0512101505090424030219080a0f08091005 73
    0x242e00c0750040f0303205007100340401c0c1c0350080f501401944440400e4004c0000c180300d04c200540110b40500316048050a492418000d5408000c214124110340c80080c410558144212100212803010308500344004414000c0700d120b94050126100d034890005c00c0030030300c1c103004480c0780c0f944c010100d40e40d1a03564030740a0061342141c82940100c07403400300c00c240c81c620103005944c0b00c0c5000a01440c80e14205640e103600401b02c0081c2001040300c10341088a0b541c854181c0d404020310850000c010710681e1000083ca4180e01400d00c602031480d0340010042100f080002000c45152401c0100c0c1d400c440c0b5000c00d00e140034004003e0b51641c2030100c0c140b0031940040042c48856220b140d185480d6a4100e4981d01d821007500c108004058402c40d0203c2451140300608846800108081148400f00300d21016448100c02885070b030080300301c0108214079000380c10200b01da40f00c1d00000c56240c0382c15240ca4032541041c80c0a0300d49450001c103441003020000890340c0f00d0380002d0881541171036800004005 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 959629874 1250 959628624 959628629
    0x123102a03020105010506130b0304030c0b01181a0a0501030c14040e01080f120f0a050c0a060b190e0408090310151a130501030e19050a0b010515070f110301020c0106 73
    0x16500e4070001240c6c07428400c0c00c0f1782110013615540c10959103044000000c9500043c030031f80401c0f0b058010b110004010f01e41ca13a00904210010141290035440382c2d20445000800d906038003c1c10303114600c940c0c3c90702403141d002c403170003400d000541920052043d03408102940720b544200c00005004217011042034034440c1070307c50150860344811103e140d1590345001941c1b034040303486402c1c081c05404940240080440d5581860400c1c02c20031030b1010300d441d000c004103084a0080e202e002802c40c0e81410024412511521800d46220b645060352000044038090006022280001080c0450340c400b00911002c1d41032000c420000c81c1801c40840c0c0320b50245003da141590000c201ea0300004542c01305803aa40740c0c40c80c00b0400610700d030000641c000c0104100601e031900828011134040c41c1c888000c9544903004502921401c0003602e004401c0e840141c1019100b05e03408441c90105a821105a584039944608640300c040d2460905002808245403441d81c075600000750f00580401c1074100d00308 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 959631124 1250 959629874 959629877
    0x1211101120f0c030b03070f0e1810050114060f040306090203160f03030e1819231909030507080d090605090c090106050f0d110403020d0c08060123102a03 68
    0x2900301c040304054845076648200c84254502030f800740278030b20794210a590031450403514421115052090135040c107040711211110710360742d440100074403050200b00c4400c401044070400e252680790707010001d240c06140800f400c0c05035207140c0384003191810042c40004402c40c03042100c00c0369580b45a02880c0b038950004038002500c0101c000c5440c00d080e80c0c902c0c3c1e112170800b420360840c3d64800d150082d0111032001c60031000c1c1c941d02c4500301e6140c200004c1c554203641d110f403070f0203e240c800104000c0c0703103001114884861500340e03030300c020a9200b030654400139408040d0382d964420070303c80b003809081030b1440900080d14107800d10400740000280071000307540c00d48a511781c503a618002a1900d0066140c0904001010000a404c441003540a22100c0e180505424241501e94010074082074000500704c0d001600200107105c1414100b02c080d0040c0004540c02d808640310707c040740c01e01900892424000c4e0440910001110301402c4074200441040c0385803c208080d08000c0c00781308410410940 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 959632374 1250 959631124 959631131
    0x209013005042405040c050d021f050909060f0d1b03240e0a020901060e0a15030506120a0f03080402030c120d090e040b010b0318070f030b01211101120f0c03 69
    0xc0c040d0f896000d2503110355009000c0600c903610303000c140200900b0340366040341e10440c2040303e00342c448000410060300c02c07000d41d0760603140c415000902c0724403100070385501d1150258040000855803406502681030b60300c489100955051144114001c0710b5541004040715032085c1034072241c10700b600000108440602003800501d844da00001e8968020300e40194200a14038018410a8042e00d0803116100c005801c140c521951100309034482c524074032030742d00000c0e15081400400d151001072241000c8406c070161030ba44903a550b818113212503000d0002c05109400c1c00181c25960309010520092030701410080c412070110641d1900c440c5586080004101500c10200301103d444e42c11910039030b80588400c0040e400d06d0000003882d040204440d000b204109442503140f030042c03000b000140920142122080d00303510305090139007416040182c2c280b101407262070b40e81c0e400c03c14620700f90742c0001c1006003202c500070048410701c02c040a44801a410510142c0c090b000903440301d15041070994040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 959633624 1250 959632374 959632433
    0xc1606021011120402120f030d1a120303161101050f04150204030515100305070314071719020604091103060f1507080a0201090b0a020a09050103020901300504 70
    0x2680540101600c419411401030f00003801428041d851b400c2048020003281c80006050340b145182d030f404502c00a6620703480754151859503800401101207020100e51501e00310f908441020343e40d010003401c2500c1580411a01c200890048080102200d240300c02842075182c950b24103000c0030000d84046517044120824121004090700c01e440a89510030041d00b03112488200500ba9240064614802002000b0300000091002c201a5008511a04910050600c2c82c40d12600349070306c56000412004825850801c0b1030781c04507100881d2506c51006004504540c00820f00d5406690403d42c2e00c103180881c0d09410341ca50038051480703900c0845482c004580c400007071200c0606400c05c2d12048510501030280045e130000040c084074004c920001a09a441e0349420030124402d44e01c0880040e4006960032021b58010248400341600703081c203600c0c00e0700f210002011103d0f4080d0348480c0c51520390f030303251240200d8481021400c4404ea000d1089041c1420462540c044541c000c00c1881c5104103503 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 959634874 1250 959633624 959633651
    0x8041d010b0a050d0213091b1715010503190c03091b06020a24020412050c030d0509040c091502070806130b0a0c03090b04031805180109020c16060210 66
    0x4442d04001c041da03402e41481206a80040a904103880300e00c85030407507001c081654085403150389048903044040801c00484070130094a120f42c0505a820040c034508100102a0040c1034100c4458000b860403503565560503000e1148080145c0c4071140140c100805a004168586c10038080d1078054841c040c201d011480020040c0c1d4840c0c131582000d42c01090180000c92550540303048031140084018141100018481c8201c1c2d10542000502004402036041840800c00642c9603821007038004100c6200c0d60100640f141c018500018032894540342030f43d00356480707a0842001002240003200c03a5074680c0300080c1d119030700750041c055203120b403070002042d0480b05424882d100ea0071011810281e201d1081940250420006050601d920b80080200040003420824443c41c002d40d2405003a48164180908400007980720710b100c0c0c000c1c0c003058480304500701d04840c11140c2000005a490110000c5070341800059900503c41c0f00003803800044868020580c112400c49281c01000443d40c40c1c2035 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 959636124 1250 959634874 959634877
    0x10e0118020c07060c0c080d020303010f0503031602040c2d080736050d060f0c0c03051c06260715050703110313080703060506010e030604120c08041d010b 68
    0x4144001c0e4412042007050b503001c2d000c2c081a0a001b203148203402a201d190b500d03d44a0720104440041c3d00003c0108000f41c0051801405444110061031520307004c120b2000fa0440e2506001e0310455441010301c1a050180d088113052800659000c90b10600030480d80100e42c1c40c600f24030002c203850ba0002056a407003500c501907a0402d407085402103110f00d100100c1e00e09140c00313851880c00d40785003002c6020b940700c596010f003080c81101c01040108a81600f0004d848009105105208460740b1100000f41c01c01d05941d205c042e4030401d8209980784510034000390109520081650300001c00b4078060a154440004014280d007080b105110303680c0114041d030f40c01e030309000d00010760207000010000b0710032082041c404030010222810480e01e43c1981031310750304952200545505c020300030810490315000301ca43c08182403c00382001c48070800860740b00c0c0701c010f0008180b8890200c01ca10a140039003480103002d40c10110942c0c0b16500ca04d000e0040f00240300b02c2d007048044850002804024280 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 959637374 1250 959636124 959636137
    0xc0512070f080702060d0609020a0f0f050906130b03010806090607440108030702011205060108010b0a0512070e09151011010b040e0102040f0b0403080301050f01020114010e011802 79
    0x100818452080d1982c0700950040300303040342e001d40100562174030702c082070088201a040d800070050382c078000c1e041c005c0e0210310540310100c01e00032844c42280c011900301050300c0f051b40040c0c03140c075a41c40c424403102e030b410601c4e604500c0d20110003000110b9216400130700d4610820003035040b0ba00a0f00d070964240c0781d03e00c41d0303400c24045c0300b107500c802280002058500c4240740d1104c1040d9600100c00c8143e414800c1d4260030902c4c09030f101046001c15581e001d1300c41c0030002000002008039017800c00000340b01c2c44050066204400c030000700960b490348120b040344c1c40415442c00e080c84d54140100000c2458140e101281c4c800d6a020006c200810300b02111031960540080050f881c1c040900ca0581d0410b1800c42c40c4a025503880020702d0041d15103014076600ca0401800042e60303207051400850a00f8007a4016880c0280244410300002d00c05070300b104d0544000320b900021036030200c4c00407400f50820302801c2140ca404500002510060300b0320540c10f84190764042c007200104c00050008900900 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 959638624 1250 959637374 959637383
    0x6030c0807050f01050d0f140603101503020d02010504150810050103051521070e0a1103011401140409090b070f0309051c110604080909060a03020f0f0a0f03030c051207 74
    0x6580f4848643c02400280300d082c0e00000003040000b6041002400c40d110051140c3d981b800b00f00400080e450240184c41c0110702080c0200b019000c9181d0150301c0c14000d000c024050880308280c0801d581c0240c064070700420034480313400141200400001c141c008180e03240d03400e58104c0c1030b02254960290080c58820b41815000020700003055013005001006002c0c0219420684003512142c2102408000c010701100c80303c0c26118200710840760300f11140511a10160081800103100c00c010074a07415a00407401d11b042203e01c0c442c012480703410702c5981d0003082030038503100310f9008105a18985520030310f0540c0b210382564101c5d04041d42559100c402c001d115070030103848901c1c00281c0d444020050707112071910f00e41e0301c0110b040040c609041650162011440403074080b40c145003600f2655408175069807414181d524550114a0104c00d401d1400c0c400c046450482102da02d840c41a0b030014859004c3d58503100340d03030381806455a805c000c1e003a81d4601803410000c054810754000c0f241040d500 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 959639874 1250 959638624 959638639
    0xa02090f0a0305030915040f06080924040b041e120905010504120b0a09050d0203040812160605060f1c0308060409080703080c0f0d14060102060403020c060a03020f03040606030c080705 81
    0x1890b04000c102c40741c143d406c4212042c10f00000c04d418070511580b42c003a001c29104d200300c0f400c1181d51a032408c60b52804451200e059141d841e2103250311401000d07001a030054400c0c250791194944003004801e07502e410711041c110b4540031300900441c0302e64181c6040c05074540c07000c0b0355141c40045459200750b00840380465000d070588000626032262007030b031108070b02e41c0001b54100c817a6603280c2494529070320031b80180e00c08a0b05001045007030003c0860000d6040c120341c41c02d404005242d02046e511103000c1d000c0340d40e85c80010680d0300c407409074000301c0308010116217004c1c0b4040c00307030307a2601c0507004150009000200080c1440c1010300c600840ca036040994603007000684d40d0103d503010300c000c000300c016101c188a01e01612401e6006484a41a00c10001c2411a031942100520f020000e00e050b045511101c14000420b4000c2079202c580c01c015982550346804680c07098010b4441c08801d80500d1100100304401e20215030310080503244200c0082502551750b0510319135402980c02480e600061 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 959641124 1250 959639874 959639887
    0xe0f01031a07021b030f0604080c12070308060909010b15030a06061b020f13090524070e0913080d1506020a0c090c1403040b010303080c04030f02270a02090f0a030503 73
    0x80e40c003003c1e41c2d00c1380080440d1010100c10300c10701c0c18440140c90803160140041000710f1907600910640e202e1440100f021414000c064400806031180902440d01404080010804803030085d0801e0000c400050601c1803d2024190340d0341c2c0684c005c5032144049072900101080091080c40201c840c89459042c08000300521780804c040d4021820b050755004010381c042c0d0040200034020300035481e00850142c0401c10f40c500c0c0c96420010003200c1d075588500040100704070a40c010840160000d403d4170030481c0c40e82c40e012070031940000c100d00a401420082030901c00034401c0e4120903850214442c900c00c0140e5102c0c4241d031f40c0d19070014021b110700d8000109100201c03981c0e00141d4030500c01c5c54a44413401d90301503401d0184c3d2003543d0a603000c50510005006242d08820160342094118500307619142c91503c0314410301840c1c2034000c0c400c03590300880719070303001e8181c0c0c41800e803034100b8000c4481e0382030050030780c8000e50201901c04c1c0156000304185009140001550040b650000003540c680076 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 959642374 1250 959641124 959641153
    0xc080d0c0c0906050a0b130e040c06030c17131e05010203220c03030503070909140f4b0906011a0f030a150b0d0c1d060f0a090e0f01031a0702 62
    0x1007000c00f100c0014040700100103555521410014060340c000e54080814ad81001f034020103a503042c0501c402880306000e0701c00441c0c00d20558059010042d41c0b4001d070b0440c034515001c05040c0d94041e90902041c00c0300c040b2030038004103500131405400c10754001c6000181801c41803a16007041c1e5000b400404040b102000480c0c040e400850340280d0502c4c01c40c0040d9203031407026048a43c40184040324001c40300c1000301085504010395049890902c50440e80201c0c3c0d041d00b041d2505507010b1550082003192038280e03a6100007043c01508054079061001890701c9030f103ca9441c50244103440743e95170304c2c1102101d188480400c442c9a0400950411314554540f10401d02a16410454000040b940303a4001104083c0c800940005900c8000100300c006103138100904207805000e5000d00e000d103820300c0b203c0c40e581e01011101c3d24020b40e4000303038403000410001d4480d40e501e40d00c042c04030079094040041d00500094014181ca01c181c450040d5805aa0460440c440044407a14050382c00302d40041400e2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 959643624 1250 959642374 959642377
    0x60303140a14070812070311250b0c03040c0e15040b12060406060504110c2d0307030906030515091515120105010e060a02030f070c080d0c0c0906050a0b 67
    0x5141d1810301d4600c0d0454244150600d0340821016600c500d40401da03480416000c01e80b051700f14543d89018048070b00500540703502032250ba6000700c442c1070024254411a510302c1c90144450790440381c415030702d180151000e10160310072503044a00c50300d6800007140501802e003019000c3c15000c210720815a0a91040c40020318140000030340c04105400c0c2040001020888107100c0c40c402e50020510078601000c1c0300541700e02406480412206005403101c0000001e484150503401610b0721008075a040d04c94000100c000741845018000040c003034050581000e4040d00315030003035a040110340e030303008812419807050054482d070224811340401d8446030480c1c141080100300502c6500201281e86400c006030380002d14284540200100411271503070400140a000c01d0140c038407034904040b03604000c0d1240709028040411500100b2404140701e50705a000014286480499038900d2000780701501d814481341d0210b41a0f23090303d40200e40c0342da880c080d1204480c40a06501031050428020b100d29 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 959644874 1250 959643624 959643637
    0x4050601050d0e0c0a0807061416050f0a0507050604030210120f060306060e0a2c120a03050f010b0a02030409050414190c0f0e060d06110a2106030314 66
    0x40000c14410344401100500c200c0c80f0b0b41ea1900010041c51902c8401d108004c20701d80d0000300c050b00106400c015050700064920300c401d2214404c01e943c1c0511094000220f000800301806501c02c08541229100d00050321200c454020340c02c58510030790307032010000588110b000013900880c3e0180f400380d8450080a002c0b80c5910b10050201d001c0a002840404072801d81e4015110591180790802040c0c00064079550011300410042c0080411180480c1c68031844024001590006103d074852440d024005940f0071600c82200c01d980701c080760802009800c055641d811002c1c81c003000050180d40034000c5a0200c0c485030065400c1a1424003204000c0000078016152072444403008804050240710b6003840c045000c078901b815440c50304115085000d1074000c40d007a0b1041d44e00a0009507003840c1c0140c1c1c01481202e420320600000d203880300151021110680c8440008140e00c102c10303800103582d69000380040001d50303030b010817072501e5400c1e00c03141e10019000c40c0c8070b030041036114001c54009149 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 959646124 1250 959644874 959644877
    0x6050c07150b0f270627090c0307090507180503060a110f040b070b09010b150d150f2c04031404030b010902071a090d030522050f010506010504031104050601 69
    0xf01a0500310105030f0340c40c1a00c0c10041d525900075010000800c40107800e0790000c0d006c1d0355508450054860180440301a03101c000015021840060000c5504005400e0a400041d09945106585404100150030155044400300d44a011641c03ca10142c030b08080c11508010002d240c41d455411900005041d071102c48021254200300380c9240c1c40c4010028001007541d54038042e600d00e03076800c0c80c4220850140030410240d0404070706801d29070364031515890b0200002c180c00d940c0d900420400005180d60154100c54175074a000005894000c0c0003107000300d035256243c41808604050150b500c48400305e203000300d013607100c03804280440e100b0315058400c407190301d81e0149015103c1d03c0d9501049400d83c03200e020160006224030800240e071401c00e0003181d2052803031100e070030b003031507a1134403014120009070415545000041d10001d101807480e81000810a0050304407038241406910380060401c40b0307032503600700400f040c11540300c1c42c1140d0803203412004160604001c201040040c1c00050030711760 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 959647374 1250 959646124 959646139
    0xf020a08040803040e071407021c02040f061701110f0c07242d0f090510020c1509060708090102101107020f0418060e012706050c07150b 60
    0x1400a003280c00100007600c0074000943d2160f00c2c1c54613080b015980100580700f045980224540c10f2034400701503170a03141d41182d0391401115424880c0304102c07800c66000e0350040c1003903001d140640841d803245080d940d110f0408800c1e80c00844295090f52021100810100001c0003079480742d0740f0a00c040c100307881c44401910701d910358882c50700603408903c1c0c0c86048800b021785070748100250014622021a0400303150045450b8158642050603000d8600d1082400900c5420014040c441c440b00303000352800400941c02616a01030085da07034058000494060f004000c3c040060303801c00030541d81d1100d4010086441d100c040c1d920894103411140c040c6056101d014080c4402e82c01c10300516075588072500899840d10105c0c01080000380031070b50181d000318034124404c2c650310311110300d001001e6017000c404101c0f809800c3d20280100079008401c60514400c4035013112040d08010142c00080c041c0001f800640c0f16074600c481c0f80d2085250081c00c01601086880c82d0642c2a0018480941d0003022030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 959648624 1250 959647374 959647393
    0x50706091506030c080f0d05040e18010c03020c0609150412030e03031312030510210c03050606100e0a0608150325080a11150d0905030414090906070f02 67
    0x21003a0b600c9504102c5210b441010148800d407010040414608103203001411304c5240a40050014840c6000d071030103040a11000510000032584884613000c20304008011028442d10018000d402405028070710307004000204801000c0065800d1122002100c0d041e82c40d21595284001d05d0a0300441d14241500d49183d00c241c40320900155100d02c5e090107050350740c00c900389404142510030f000e0744401d1600c1c00040c016081d15026002c4251801001c8031000745c18140213006038082086c034010100324058030003004000010580314040e0b40140d9203a031100b160547c3c1940c0b41000058610342143c031161003041402e204180140d0401c800d043c2c80300306080c0d5000440c2c00d0110000e92035003403001700d130382c607100c015042740303000c1c005010206c00b610102c0701c03640d5122481d050030120140308150500100c0c402040750070445840c034070503480801090790145030040d1a600309104030003070b0b0a03811440d0780070b5040040d24681310b2441c90000e04030b40d40c1d4041d004c0d100c06100c46076a00c2180f094620a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 959649874 1250 959648624 959648663
    0x2120a05090f0a110f12070b0a270905013303020421140c030601120201030e03160618030e090702070f03150b0a03080d022d09011103090105070609 65
    0x1c840c0f582e0050031000140d5610780180710000302c5012605008212090f80d9403191031010503c842500c5103140d44640e505100312044803800c41840841c02c0f0071001d01d102c1354a00081d40460000c40780d0b01d0784140080c6c0c3c0d980c084101038103d4010302c4520b40502d0036030381c005621900b000503600800c1782030050a143c2c540d00b0462101d10240ea044e0f900c1104581003000740501008010108070105000303100624140001c65101c03803041c407501842000c1c0c249810308680c020f8100440301f4032110202c035260b00141e644640c4141080d001a0b650714a08940420310041740003980710f00f503400d502da505a9001d40c10a0145545000b8540e000b14003403503001142481d03581585600030b40c000c444514628000c4488202240c00c101c2e44144180740c0e00b24204000744410041d100001d500020058440210516034006001101c2441c4181d03000b41404884890078034001d080300700000c3c2e071001252030700c3d14111680d92042c0e0502c42e0201d9020b11800c000100f00d0f810002c1705500c1003510610f084c442090 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 959651124 1250 959649874 959649883
    0x306050601121a030c03030a02250306150609060801060e09100302030714040b0f0a0b070501060902030717060109142b08040314070b0f0f07021f02010f02120a05090f 73
    0xe10701d0031600741400f450191604000051034400100c000d18039200000c000030399200080319010040c1c02c2c2c0e4500107209113584d00110302c001e54000c04248001e03c13062a0049002106001d0b50005c61756041c00802c030b1902c00c0100d5030580d101502d03602048012482008500c600c014107552800071416008001a202401683d00814007400c01c2c4080e000040101300c03d07a1a0310100900502ea035a1442d00165a480150000c4844a0140c030707030340d02c0007828502d01608c1540c0224100600020622600c20b9209110019003030380320b4460b03c416113483d001119030a400d031151807490850728620516610780b0004402e42c0040241a40318840e0503d1b4009014040c6a54191007418012400300280807040101180c4145800c0140c1192800c20320148014060114401c01200002ca00c8521100d0382c08111100701c0e8004003444c00707107080001c0150190b491100b41200550800c410324481c4d90190082d2281c0209c0714240301420741d191481f80d0010140108458524415114807500c030050070f11 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 959652374 1250 959651124 959651141
    0x1170f0a030527032112041a0702030c0c01050d060e1509131203050a0e191127040614040b07031b050a0e240904050619030605060112 59
    0xc940325141e00c8429245a00c110050800560640c00390707030060f040756070100d01c010204c54400303004096180105401c00040c080d00810100030040c1c8030030322082c41030303400003220380c00304002c0d54415980e541c850403a107a00880390380640c1544407146a00f11980a6000782100c00010400011580d564185480808005403200311410507400c00d100104d090045070390b03134040900741040c404e440d01541c416000c0d0800c1c0c4214405c00d5a01d6011070b401c0030075900100054920a01103480c03809082200340543c0700d4180003104c0c8005d030041d05c9240c0707080c10383c1c5202803203041c0603034000001d070450801f0080c2e09000b4011110307207655000d110145652011201d010314000c0088015506e46540054101c41c1905c03218629030101007103a01e0040da01908550f07110410b45031441d030069006011510004548010881c194404c181c44c01c5001e4040010b4010414200c80c240311540ba51014807160216100b01403507101030414060002c50f1480d00102e4001d9018585002801d0550284008681d00c01 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 959653624 1250 959652374 959652377
    0xe071b12051317010b241809010303171609031b090615020d0305040f02060a02070b0f072108010e1f060c0510110412050a02060406030506030601060302030f01170f0a03 74
    0x80809400000d0f0901c182d10b0700d19825610a0350a0307608808400e1905400140d102403031100050034600c0031829024408144000b611075001540c41c0d25003e0051502903066000520b04100061183c1c1c04060703d440310807010b910fa480616040d47c8500c5e0350408005040c1b148001c03000da0005442c40984140300091004100d00c11070001c05502c02400d1240c100404800c2508110602021483c21100402d000c2c0d17049940540d640c5054800341d06000c00ba9004160314500820078003a52070080c4006c1c059a0b10031898942011040044040380c0c10402c1070310000541e10a00600045041d00c0400d908110000194540d89480382100d1080c42d1840d0402c0c4c0020f00c11908031130400c40c1c1041480440c014400d01400056006034070096207000781d01c203105e1310070015142101072102c140450081c0300d4014010310354954130313080b0180c00b601c425910355010b80308210000984504c41e2090341c0c00303a030700310210f80002c0c0d2034450760000810900c481d0715690b00401000c078210120410440c94164403d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 959654874 1250 959653624 959653649
    0x51e0d02270705030613020714011401080c0105030108030a180b07031d1e040b0109120c030c05010c050a020d02062208010b0109030b0f07050c0a0305040e071b120513 73
    0x812141a03482030020b0528418000c0c107000f4820f60350307203082c0e611910261000c40107803581c0c030904005810489200301196994030702850300031040c01840300306050380c00b14421100e21000c0d0b403004556900c801d200b500600e070000d0011581d0b9071b200e181c118410001d00842c81070599110f036110300d01984540c0c4114042140741850078122064031400390120301c400c44e03403d0141000d50411505500418014510699840c0c040c1c06580c0e0049140d017024007034109260340d442c42c0901d4400340040c2140001c1d03c2406940400080341d6104511030342910340d002d07000e400300341d480341e0074809001d40300da1040364462014000410003200840304803000101c0d19503c075200900e07000344c0b2404c4440e490360942c104500d2600070310100d080e000344184c10080b021a002925030715450115010b000f002580811030003142c0620040c99400006801611200f41e4182926151407205840c5010020410f0b40c43e042c09000303150101c1e0010a0aa41e40d0f000c90801514150480390107190444040e041510320040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 959656124 1250 959654874 959654929
    0x105040b0105010306060e0103150807030503091e06040306110403080d020a030605014b020307031205010f061110050a240b1209030405030a06051f051e0d02 69
    0x140c0d0480c86005100a08080110342c1c24407100a0009413052055418580c480c3e0046c100c0b503500c82c004a0041003a0011b80c1c0c65141c1340d203040b42d200c1e404082d50902c160000d0701d854005000000390310b000d6620003800c82d0710300380c42d660714400a881407100c0c1c600c05000500c00000810060801401c41d401a076034010b907130394560385014084806a030490f90400034104204110a90076144034a500240004020040c10702c507803100c200017151002c002000b1820003042020740340c0000180446502c60b441c3c40c41c02e0602c10201504031030702485040c0c101242d8003000c000b60b600030034289030070340d41e02d0b019203007000005480042a81c8040e00d03030b1800c0070740d1882042c8514140c5007101014103070f401c800607501440c11510203d24050603800203050704c245000b00700c410804100711401004090141c46022031039040030300080c8012195404500a0050711400003408505100282e0307000404a1020307200f464074050300c04c090060401d401c40c0c506848800035070354102010581d110581506e0a0110 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 959657374 1250 959656124 959656133
    0x120b03101d1515041d010c090801050c070b09031b0c030106170303071b0501290d12141b03040501021207173105030f030702010503062e02010504 64
    0x44444000252580150382c01407a1444200729054111a5002c83d6200380641400060700501340084541e502c82d0340750315494910340042d002460fa4a0003515940c5400383d6584119082c0e40d0304980d5003490034020131501e00050301c100c048a8020142204503400c1031811601c3c070300c0c4400c2110a00700da5501c01000111903103024000d207000f4084c2c00b44541180014a28500d40d0381c0400340000742482258401180300340ca012402c0f56859410500901818214017841c08100619180c0c2c8000c904e4501041079107030819440c03c1c42801e40c0200d40e451460101a41142d084200c140f0030f5080c00710410082c0300c0e6141100300101d1018001003e15a1a4548000039103060710000181081c0c410a02800c008210880101203400300c0c0d8800c2c4981c3e90400302c42e0021118200044c00c480011520201c2040160011031482035980030342c101c451110444001658030f00448070020700041d82080090207504054091214400d14007123505100c9500f6203802c0c603440c0c0f8007200000182e542e02d08200c10301 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 959658624 1250 959657374 959657411
    0x70e0409231e12040b0c010e060a02030405060105060403021807031104060801050a0e0c0d11070602040e060a0503010501180b060708030c070b060a0312030902190617010b0c070501120b0310 83
    0x1401c00c0d0080040c200f14166020361070241e8403d00c5503815001c19405207404007034000d45660503010064078840e00d04500200000d400070b5030283e0f06846020004256810b0290032641540d80042214803035448140024034500d90007000e42c010103032515502c0189100d0b0801a0000e000d00e519521410360408042c015406940e03840800c06403070764824400c08215650860706400f18903040400c07000003400d08401c680c401d00300001c0c02244002400a0100e0840e0070b201c0c02030408440801c401559901058261007003801241c0700d14400c0d0314680e43c1c00441c0d602203044400081e0465090010644848685070000c03141892081000a101c000300003d620010b40d04c140116031340e0600c1800d50300c3e403207034400c100e0729070100b0726681d0802d80c400c1d560384511f0500b603040f4014814641c1c41d00d4003c0103020000341d00305048131035001e50020601f115500c0944421904a40c02000010701c0c24004590201c080540d101100d99034513442c19003610300b813240d480c4000d006500031492038500043d03640ca8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 959659874 1250 959658624 959658673
    0x3050f03090a0e090c150405101e030b01020a21110109030e011202090a03050304080d091203050906070515072007030b0c0c15100e070e040923 63
    0x46030010880710060b603071a00221000e80301c818001d05642c2d0303a12250302d840c11410810301e035880340d40760130207410314000034000f00705591094450204030300d680001a2031200545c0c1d2108400010007442710394561207507000c40740c8088140304651a46401d0f8032580302400694030384507800c601c211000c141302c0b43c10800d2000d0b060002c0380208000510764030b00038008800d00444904004081d54140d000340c1c0f460701075402c01100284580b040c140e407440c00ca6920382c0203101c0c620880c084c1101544485000e0b20b0308404841650041d400c1e0f0b501560380440d01d07a0310400300581d0100c014802c103400700300308000702c00400022510240b5103003070210300546903446140e581c0e2260800351140d00390301d17180070502d4411242d20801030001608c840390503102c1401080d0414900303100e0f8a0703055000ca011880708034000c1c0ca0b1410b6101e031441e100c12228140340701c00c03544000820608802d25036282800c6d406002414003072542c1d800401d86003039200304040c0304480b480380c19034000002800740000e005d146408 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 959661124 1250 959659874 959659903
    0x20d0f1b02060a200d0b01080106051804090503070b011d1b0d09050106180510050d080a180321181202130b03013801080a0903020c0909070305 63
    0x8482111100c000d58680d0014904814681c40e902c0c601403801619035101c0c401951a6201c545803e0304002d1403006200c00f40c07500f80054286d400005016005504403919401e00f4440c00391a5170707010061102402c280c10045179144020010303540810120002035004c1c042d000300c1c0308908880010402450007014100c041c254001e8a0703659440d94407402125800703c82440d010810040ba402c015004000c250700859403004500b80c07421401c130707040c3d010034450032111454401c10703a00c410030700680c10304030071008002c264100b0605407030b01d0181c1c1000c5051071a40068281c1d85441c3c0e590080d1160840808507030003201c608280d5045031b082001e01e183c89403814280c0c12442c1c9800b0f00d00403004c091060207409540c00003811440392240360409801480064000e2080586246d80d20558103d051f4482c0350820100021454041d001040c907080100140e40c0e0070340603180d880c8010001c0a031030404a003035104015002c80d0507102c1401440c4165212006000d0292a5040444c10242c4e00d211220 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 959662374 1250 959661124 959661161
    0x602030c040e06040c2a05030406121811090a061512180b060d03050706110403020330030c0d09030f030b090609070c1e1101030e0d1e03020d020d0f 65
    0x300340d43d2000031b10070300e60981c02d00e4010360484075009026403641c5d43c00241480c0000580458a46d8100d003040301c03012100b0030204400110104118410308194a00a0440d10404041c4049180031345d1801c1c4c00a0a48070005541655024450717610784080300c0f101d003c16580382c0b00105c522104c1c8201440c090f030b500ca000c03001d620aa513603101045030051025201e00c0c29882c0c00004d052181003620351182d0700003810403049030749180c1c0c5070701d075000761000704e121f031007040c80050511031803070340c0350810701c00c4041624002030701e0003003129054000800c003c0d906001446050304d201407601503403241c00d0298580720445100040010f00b55050114518012a155030038130070962909010590700c14054139200800415a2038105140e0000c561846008020848100240400c0d8001001d02c91800d8808006994010a100c0c0d01c421050b50280040760310104602184040c602c03001d0000c0c0b42c18a00145821400014202240c00805d001d40780c3e244e54516480d0444110302c03c040400c0c03075404141 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 959663624 1250 959662374 959662391
    0xd05100f0f03061d0d0302030c0702130e070f060801410909030c0312220302070612050f1911040905220b041104060e130516050a051c0602030c040e0604 67
    0x1c507560644103103070401b00766000001450500c80704061b11407465004111410710059400e09801078000200322420500400c1d600007442560050b040c8100c0d4038649a211351070b841d02c4010125401039076404d907180300c1055280c2104c424100042c203a140305c02801e414041d117190741400700000c0b004050b155030343e2040014034030b0b00c03c0010903140d03404042a054105680d03820700c030140800c400c042804240454130421070401d90003242c4003040c0e60559403460441100a906030080c1e5200381c81c0000031a1740200441d00ca207020b0141c030b0320303180c0300104d0110711042813501c10f40031940700341c0c00020140e40d690280080300c4031140b05034601c082415903060741c42c0c843d1746810f030510340083c1000744400341c00566820b0507204e9400a01c010030034400c44400900d0003186a204100307143c41c046800e40154440300030440b0603109d004090700e20203461704004e46c1c1040c09000c144010019450100c981c0c0b00c2c4150009440d90006511138a54468070548841ca8924270407411807018208070700c5a400c110300e0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 959664874 1250 959663624 959663681
    0x10914150102100f0f0c080405100209100804030c080307051e090303090d150515040b041116052b08010603090b0420090a06050307060e060d05100f0f0306 68
    0xc5000400e0440f0002500010160000024124048814102402c180d5180d080940040b081c030311a6008805032152521400c03241000c81c4100541640e01401562140499511400c60f550340140f1a0509111210b81515940b00c240c208580c10400550005040d0f80f0301c4000700c0420713410408100038030b4105481d000000e43c40c7e00070100214000d505041c080e03000e0005c8d0f184000c017104141c500802c414140700e4070319903c1d0f2003200c4020703000c0e0b81029414841424076200703000100c401480f00c0750500311280e44800d4094041002034030362340724880861512030503180746001114072940a002104d101c1030000f40c0030503416406441410f10302055007000c1440c20201d203074000e5106100740d0058003110000b01c0c00c2c551421800350011000c000b00f1101c141030380d1100051f00c40c01c500301d0f81c106940e01c10440e00c0e19086000c4039003100084c440c00c00720701c0d010b42000750001e0b9841e440c41d50719500e690031020700b204164070149003031201038410030034008148a00c4030041c50452a10990314000c681 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 959666124 1250 959664874 959664883
    0xe04060803180d061112010e0708010504020a03020d051509221e06020d09051e03090d030e03030d0c230a0c2d02030106211b0905010914150102 63
    0x5811120604122800b82c20341d5041e91884003254850010080ba02002c106108150082c1e0895038504005c400080f6031203441900ca2403140c94141d072841040d84c00d040910000c0c1d00560003038002d040e003e1164010f003100501455125212a24642c036210326107404005002c1030140024582c0165a0302d1041808008100a24855044800d07810030b800c070105404815140c04401508440c40401c00110352405600082c0b0950f014004481e150405070b0304d1505135030030000d88482c05610400c148202c030b00b01100c0a4101d03038002d040241d8404166404642540d03c40e42c5031641d00c42d41c8148210850707401c8007078425107000c0b091415040168400c0e1035015880766030069010711140c03100c000b0400800002020b9034041d49890080c581c17444949043c0c240c0c4a95000320b06c41c0d402c0c800041001d40b10120b40706145201c0441203403061741140c07a003005041c3c1403891005416104000030446003660300980b1300a140303803500040d400544001d1041618409810350315880c10309110030b151603a0018 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 959667374 1250 959666124 959666137
    0x9020906010c030c122a110319030e06090d24050601080f09010e0708010204060e03060c16050a020904150b18070e030c04090804150309050a1401090b040b0105010e04060803 76
    0x40c0d40a40c8101140c006503401c0e0444c0c100c01c01c1e00f1600003410301d00700c8035030b2a00c211b1080c800c1144861010b030100400d5110a2041c0c86007e65511a000507004207105900c2506240809000c03503280500d0b806c0400c04001d02e098084d02c0480141100d2580031042d00d0988210b604503200c20089801c2060008002c0310300608445414400300340818003480b001c0d070001030f00520100440c0c0d8825600c5007140e01130b400c07911645000c262411761418160a000c1030044c80b6200f03454000d498040ca07002c8501000070102c8081d54284500813003900140c0300c030342d9200d0240307002d4801024100151999282075a401900c403d01405036500368100e1440022800c9410009c0c50030602e80581205011074036050024000582c0a4108105d000612000b08000c00555108564070000c103040d050080d0151002d10500501c0c1cad503c9514540003040410303907044500c0000c80c00200740881c0a40340c4c640303011020354059403401c85180040090f9a08200480008802075070b06004041c503180d40b0603128020740 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 959668624 1250 959667374 959667383
    0x1404050f0111031b1e0303011404020c031201120b0105030309030c040b01020f120a080106090803070206070309230108220f050321090c01030b030d030f0609020d09020906010c030c 79
    0xb054100140c00c0620039504001c864581500e06005220003d0b60350344105042c0c0c004a400c2c010594100a0001c4101d0303060b00c131070300c6044128060650074400290b21004a8140f0b50100f404138440e80780942c080c03e070080200d5070b2000d40060442c14031040c0300e00184e102902c80c0c1d00030131003204262000b1480e2420b00c20101c0700001d05a99810041c0d09100d071100b030300805030192010000711503060401604e003d0807a03035201a0640e803540010303180c49072107004500c810f90007800044010b227070107030081030050b01c03078500304049035680c843c982c1180000e611015050404a840068207507404003140d94098152440100b4088400e0800801014101e501800d030104003020708013400010402c4580301c84401c2d009915000440c40400761a041c25250003d85028041d03042580e98840c2c0034100c445507005028003190f088034201039004000103202d04910365241c0c500090f414400303201810000a10b8072010038805101d1040000e01000103065074180800b08140038086503000e8020120a54030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 959669874 1250 959668624 959668637
    0x510030509030c01111c0902060f031b07080d0b090c1b0705120f120703050a0e01091505210f01030b040602070c23031506010c030309120c02011404050f01 68
    0x400018600710700c603c04100c805507007485c0420300300c00750320f400514a43c511000301c001c40074040c0400c40d040d50354150010358401001d000040b80d00040800460300703d201640c00c1049190142116083c1c0c1c3c0010500b5101c07080045420103400e85a40210f20030200c044032842c0c5140b1305010540514000d40000d03000c030860710031100c4101e00781004041e01400005080b030309560100004d25a807020042000030141c000d1092100100e12400151016903915440d524209203442c0d00403a150210b89582c10304118014100007a002002c0c1c044034a162080d61b1001d556080c0307204c0b044507000f07141c005030000803040400c00400040800039281902c1c0d110041c002992242e04004019000d07c000240c8000c0c0317415000071351034000404060100b401d061406402e004404200342c3c4411050551520b0001010000742c1c1941c410b080b140300ca64424100000d03280d0706a00c504c000d42d9210401f5070b0220b4005a114025507801c00007001030350780c010300603d00d041d0070480852100e40c03440b07040714180981c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 959671124 1250 959669874 959669881
    0x2a0c180507230d182001020307331505010912030e150301080307021206160f02250812040f0e0705041d061e0306010506071b081c050405100305 63
    0x300c04125024544200d00510020380d4607500c1512441d4558400c445c014030104619002d815621403501400b030301600038600304041ca4860100c00001e1071584000100982c41340701c51944100d040d075400c115840c400040c905141d00e04200c462001d5008641400390956081105040744840e110b210380d85482c181c00a041040c02140e210369440e041d1010386070001c0004070784600d00001801e8058003c03108080c119104011007600c0d08415100d1441070351550201e00340306401a2a10300d10003007075204a602440385500102c4c101104054410462805d80c4405c20040720108411680d140c002031001c0d181c81e14040f454400102e1074800c0d152903540c0d21001441c0e8600600989005060008460440d0801f005681484050440712980708603100c8041e40344002c0e01d4501d04c49802030142c01420240d0030700c420084070f44c2001030120752800703150075503c982400100a010040020070010080c1030346400c03017864500d801c1103014040040070701c020042661a40c031402c440761060700f0005010348 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 959672374 1250 959671124 959671187
    0xf0a0909080c060112020f060304080723012f0406021e071d07021002041d06040207080c0f070801050412081902041d0a05010b07032a0c180507 63
    0x2400c0d260b80214011000001041000829100019071080b54420081e80c81c04040005074002034030080c007803040034021040010346040514040e84504c0360580f040d60544440f8500b03482460302e481c01c3c50b002007050708484170039041c2500040708888100c0da00f000d0401c00002d5030780f075000e01d170003ca06261400914400c1c0c014441c1d20090704c01c046d00c5c144a4181100c0741e10a2600a4884800522480c0940c5c1420b10491007a20700340c0c0e001c10300740c1807114550311006c6004031700501250742c400d0b400c001d03240c001462070000b000d400f069500a00549208100250b080c086258850310840c0d042000f00300006501c054010740c1501c540c1400717140c64803684100c00c2028200c00040300c8041c4000750200e1003100d0a83c8810010080c0c3d9240038003582c441c4250300c03d451080c422024004014401440068012000c600707000d100309004902041c04005000c034210700d41142582d54035500002030080c1d882d89548003141540c20380e424481802c0c42640249000b030614106281000d40c040b1110001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 959673624 1250 959672374 959672377
    0xe0607051213080f0c0f010c050f0f1b0708102f09030f0c1e030d0c0f060203010e0711030717031e0a150501020d090302060d020706180c050f0a090908 66
    0x290f070455940b58692501c100308000c84c1d0701c0102049002d205101c03038070750040307414011403d6131005640e5103030400c01c0d9080c030841e071504182c1e1030120340c0900b4800041500d04181407005031550950043c014646003031500d504104901890b441c0d81c0707060240103c000c1e0220740c03a00e003259644c0508100e6800307807c90300407810b000e64484141e02d0f00075085516055680000c2a000b0900308440c51643c1200803003500361058089031890340c0641094400d04075043c0a140c1e2007000078011648018103204c20341d10107017280d00c240c0281402c600f048091014180e030246030b001c003000035080114034100454032030a918808591f042c0c0301e0400000001100c082c041c000082c503212000c0040c1c4003500f03028440764081e0a0300340c081c040100c42e00e000001c1c7d56100168203004044980c50300b0700c00c00d04603000d00c003995001c030441442c0320703400300f24040002c3c500303214002c15444c50b0f580f004c0c801070403171900340404401c0e5440544510901c3c1110104d0381c0e202070061003291a00200001d240a45191001030b9 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 959674874 1250 959673624 959673661
    0xf0f010b030601090e101a09180903070f08040305010b0f0303070209090c2e1707050a17151305011805100f03080301060f0203160f051507120e06070512 67
    0x250131017101380803202e81010192410b690f110710107c003140101c10007580b018010760052036800040140d40c00070005d520300c4219084584e407800c0d60b03d403002c0b54440d80307104100c01004864031440064104140442842400c5031401c08907401e41e442200a80040e960b40101000a8400c000b2000450101401041040a54100544800e001c80410800c0c41600080240b0b88000c20213003005c04604540b007107000e2030590151f480e441c0c0a42d00c0b504411611604440f00e0704050050303001d43e0120540340074901c40c0c172074403402010304545840da04c00d21000d691100c450448060405005100c0403042d03a062011880c1001e0001505544049102c40500841e500801910291100c0401840795000c003d40c140d80142c3c607012084489a101265240b007a608101c240700103004010b00010400c250000b04540a20b040311421001850340c0c80100000b6200c00780403552010b010305a00c1e089002c1c0b010b11041c03050103841c203850404005003951241d80342c4209244840e00001d186c500150202042 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 959676124 1250 959674874 959674889
    0x2c0402041b12050a090218270304050f0d0201021e03071b08011802030d0e0103090803010806011e030314090d060e010e07080a0507050f150a03090606120c05040c03060e1009050f0f010b03060109 85
    0x78808d0a480098a9074468090640600c501820b118000d00300f0540100c000c682c1a401400407411045890600d800e00d02d07081c040714001008184042100000110041c3d514159052010b034a820640c0e800c458801c0c1072105103240020206000d80c0e408120311b440c10080741490907140c0322500048004103454040201040400300002c01d08800015107a410307100c461040a0640913a601c0c124030baa4214800100000d1030810b007072143c0310003007014052480b0003902200900680c0c0d5920025a603103003c61404503075503007440c1344200e1030410803040149420b01c06030010800c1c0e521035584598550103260300500310725010664907292003a202d4404141c258250f5250f0b0380e1310800501810700b1810554031035003800004100e8500d1480d803400384550280021000a10781400e0201510700781a070081030564911000a00c40c080c84100f5111340d42d000c020701c00b0a8180520041110b0014261107185164002000302a4044000303ca05603241820b0f410f44035a20000121801c41050b0005503 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 959677374 1250 959676124 959676181
    0x1d06040906090b0103110c1b041407080402010f03020705061503032203020a0f14090402010e032b1403011211040914072c0402041b12050a090218 64
    0x1810b0680c651000c40c401c1c40980c5d0921008803204840c102e80e0080061158280e00818034800680800c10300c0d400750b80d030b009480031034801402c280712807068004807032680200303007460308010447d0ba000381031300901245420704600b03282581e120386a503240e009241034207459a12580090f01d40c4c0030001d890100303192568a03100101086942070b81d0107021702c01240915841c135004281c580b5201d20000a40758517143d5800c044900c201009a4800b0203041a030500a800031240304645050060400e408010f003541200c080e642040403100c100c440034600c0800c44e50040000c400007d0208403811030b184980c00072032194040c18142854400381404a622074a0441d04408010152030750b103403a5036900003510b4a40d60384031003c08600d150150150401010009030805102540b01001d80060002d480011051b045200b06400e502200400c1c801203000d021a080101065020706079101d4241c0805010100f05503000c03036043ea9042410024030700e08880024940c24410380501840c1e80400e4584 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 959678624 1250 959677374 959677379
    0x3010303050406030b2413210209180c210106150e04050c041e050d0302060609010f14040207060e0703150f0203040c0e0c07080f12090d1d06040906 65
    0x1074501e0340305200e01d40c040780c1000c4983c0601e14128001b4040d501e41d000140854100707501c8a401c1540c00600307034000075100c40f80046088104840404843e080019600030305496074010068006001001300c04c1100b14845010070003400071a4080302000d081c1d8000034038071429824003207888031248030141198a8602d002885c1c92900758040007d4803a07444100c108800f0f20180419034400725400c2c5014541000704020001c0002d03d407508007010340317251812003610b403000211108017840301640180c0c0840180b012a01d02145454010540f07155004c1c02c1038070b090a1030811150704149184500c0d4046080818013040303802c2426413600440c10380341e01e6a00c0e4905000d034840300102c40d054036441e06403440c600303600d02c1c82160b00a6810030542c494092400380412a04130340200f580c803070b9010500108002688402c040c02c9040685800d40c1e0300e48950304045000c0c0c6000502d80ca00c0c030f81c80200b542c2892600000c4000c6072104501703c40000c0400e41000c204144510b40c002c030805032420400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 959679874 1250 959678624 959678627
    0x30906032d060a08010203100e060d050f030d2d05071b050618011107080c12030103150506010503011503200c0f010c030204051804060b130509070e190b0d050303010303 74
    0x1514400c0c0c01c01c451000002e40c44d0a0b42c40e00301e000c11902d1040341c00282c0e2083c0040c1c888500110b80c0a14002c16040840795256034003801c0a0b070441c60204079070700220701301700c21602c10300925803503803102100040d170b142508942c04a4036018984a842d020f550b030b004185018444d1b401da010301c941c00024512802a1454240d68910048840c10303074040805c0071080d801c5406014a0450410030740c42c1c2170601803240c42e0515241e001400c480c0c1180300c1d2003100700740301556002450007580504113030f4011207000d000c42c03426150001c000d00d040020400050080c11011011007000700384602d030010b10741c0304803a800300305034843e410040d82c184408501c0e1018004001201416001400d00900407140440d40c01d5081c1d029500685902141417954940482c1030500d40940c03003400380901041140744680450b00c110710401d0004003060300ca0042001450041149a0050818111070703042842c08100c83c40000340000391201d5150307102e04640b03902c0d6407050740903803a4a4001040c4c3e41d995a61b481c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 959681124 1250 959679874 959679961
    0x141305041e03080f07021902122e0b03012013030b1810061d070201020f03240a05062502060c07030b011703121807030308060a09020301030503090603 66
    0x1100002c0c91303042000103203400e2011420030b895003140502c0030326428440c2c2c20410303034032508a695907071403103100901c802c80e1100200606000100d00d20003ca4844000d1900c01600d00c3c0c0b000d00350090303061481030352100900e0700410070390012000b18983c5511140c070300e090311107042e540080d060b0301d03140313080c00200d140700c1c03048188440700e100455580401150440e0240d903102d120310050292003034151215402d0b0200c086a0050803840014980341740c172842c44020fa0000d90b46040410140504c01d100c052128040850100c811101034449074134120008002d44210a140981131401c04082d4140c4c540070f11902d144c4650082100707440385501256207586900c1c0384421f4071212103081c00000e0402d03c0b60104220b1048950140d407804000d6002c0300b5203080b000d05000f0600d0007140100e001c1e60418441c00380910308c039035544015414100b00300400409141c0009941c10b10420040000480000448880c614140c51181c2c890b9102c2d100380d0240030701a070281820244034060808003000340403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 959682374 1250 959681124 959681131
    0x6091006120b040807050a0b1005010f030b0a0b0a09050a090e060606070b040308070c0b070807020c1017071b060609060e0906130809040c0e0a141305041e0308 70
    0x148208891039035100380e5890300d00740410141c810340c402004900480c00712001004140d0050003140c0c10807016a44000a1500466400c411060348820600c003030740c0c1c8040f0561040c0598038040c800074540b10b0000c2d0858440f480f442d16070f5040040c1c17220b11503025086400050500030844043ca40c0c1c0da100e218043e00469540c0c40240c014540001c10619218040c0e0b05c102e07412490000140e07a8a036800e13144001c0280000d8180001818540006507102d54158440c034000d9440246508005074013910b0407070010f246510840304009410000d030b901c541c0303034201002c0039011040c00340c846103020b495161404050b24072446000c20840700740100354205c5004c60343c454808100c81a41c400100403640300580340d403d107581115001c0369007100411540c0003007600512045182461810002d011102d620501d100480c2000c1125046440c0484011340107007030400e50350301c08844d55000651581d61617800c2c50300c40d0b030340c4101003800e0100c0003c0048014403020b0002038000c0342410094040c05044 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 959683624 1250 959682374 959682403
    0x405100e2d1807052b05010305010c02101a0607060b0a0308130801090305121005060a0903030201150b07080a020a050a060501030b07111e1501090e070803030108100c110609 76
    0x10103a10030100e02c0c490900784140850740d1540e0400721a1840c0084090340341006881e40400300e41d95019018884c81500c1c002c40c442e20001a4400c0641c1000c2e04103904034440301c0c14a072402035100312641441e0780d429411070041b90340315640c21061038008028401c1d203d1154020125074004000c001106008010a03500c09400300c0040f0790380c181d01400c2c0c80d461000280000e0051144013202e1501804041d0055a112030104901d501e810108610b03421091141c000a62581e50400c1496028456031403816080002101c640d820090800e4540c0300d01c2d070f0018050000010104030f414821f00803801c0850348241940e09462035400d1001c0982402e002c1501c1c6500081c010880e10303401800701038032070b1034400040e0010000091400889001c07560806100d400713644c1e00b00148a1801803003d01070035900400294400d801c60041346800869040107940381d10400042c4903e400c00645200181d030109008200011201c40494800341c40b200d100c02c4920884003030101d440000f2070440700c0308000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 959684874 1250 959683624 959683639
    0x90402161202060a1a01030b0f03010c0332060f03072408130f110a090204081506060705071a0c0a0506071e050d110403020603010303020c0907050405100e2d 69
    0x206405981202c903040a201021140d01011751071030750081d00301e90148440200300c5100b000d5100c0101342540d110400e00000281d032a00e4070300110350b6440303400c403c0d51422521225010501c01c060100c2c41c4001d00b00500ca41c0103000f50300c1c255a0104241005481d94000910100f00070101d6a50156030950541000c40d04042c0011003a601c50840410741c25000254942842116201c0d1600180c821034116009400030601142c0c55407180000c0c070080100100411595904070365200b01400098100c81c4160700420040020900028000b021b0350000c0029200c260801ea0740c035001c0344154070915035103006d005d0340710b001c0c0100402c0303007071084202c0c0d111804a50b1800032041c440f01d107281c81110100f9800d2103200600482c1d90f2081c5c1e840c6410341003542c134042d101d8000400c15042680100c00503401648171040324286564881c2e0814940c1c2011800c040c00d01c000035540d20041418241000243d1750442c001c0d0b5107480c02010082c0700e000c809002c00071348041e03812220071440b02c554000c408 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 959686124 1250 959684874 959684881
    0xc120a030f1406090403020304170c03070b040f0b0a03181505150112021305060c1609110301050409032a11091006080a020c011b0318030f0509040216120206 69
    0x10140102d410400078050140318a82d580c4042084550300940182e086100604c400300f01c0c41941e10030544041c428100030980000c0040806103020225004044a09018001048560708004c10714007615112810181c4552400030100e0081110b201c0004498016001c00700500c81c1d00c040407101041c0e44030050101c0e0345c9032000c00d400c150b2035400c502e000594100c95481010389990180c020401510707255800c055070307140068a03542003516020650382040c07007101950001301c0c8080c2c0050046440a00401960b244401518041407040e01d000301d0321001a80101442039142e0740c2c0840203803154030218116a4182c10103801807907012202e900c0007070382c030310442e1600d400c01d98801c444480e29039001d9400c1040881d0b503c0c0340540714080d10398090048043c0c3d62428081c0812008406e0b180c3e05914004503c01410344103148088441c0a48008030f07c80030a5024840600e00d42440c10607075900c4020601003002031150701c40080c0c103400c800c00c1c0b50041000b141c0900f6404450365084810310745 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 959687374 1250 959686124 959686151
    0xf1505040305030c07051e010e100507140309010906090b0a20030406090c0f061e0f08070503130209040506072c01180e0f1009200705030c120a03 64
    0x1441940e000e404a50180006a6100a00002030103100e00c103000751480510310110a0250b000c40c45401d50181e512012610000b0400f045103011016405400307105a0600c6000a0a025041b48100380000000000600780c2142500002101c40d445481001440350750b00341803090700802d0b20035400d524103000c1c408440c00c07160b0020f2080c254505000034a10780701d80d40c801000b0408100c04076884100c5020024100b0041841c08000b000c032515000756990b0300c8100c40c0d498540404030803061110b8030b0b4035104103c1d031254100d648010a0b04216079207031223102040c80c614040c020b009610030303000300820082040101c0c9081c0218090b468414404d90f82070b019582496040c80d040c0440c802e14400f400b681d600c601151403481c4001002585404e46800410800800c115403024520040b2018030050703950305050b8400404011004006031400d40880b1810f9130880c500600601c1c3c808504001481828404c680001c1400b1003100d50840c1c85030f50050181d0003d00814011038600b00a191519 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 959688624 1250 959687374 959687381
    0x50907051b0a210e09040501090203061006020c060406120b151c061a031302011b06140c040f050402031b030f0f0c1624050108031308011404020d110d0f15 68
    0x3c489501c070703482c1400c41c3c0000c1c089018001402070782c0640d25041041e016842c1440281e018024001340c0d4480a03051440c064078142250100d071f4098917080004000d134561100002e065414491808160ba51182000079080030288001003400d250010700f1240d43c6e8801c0c020500d0003034901a00303002465441e601c684c1c2144040702c000c41007000410000b0a0050400d10425020784141800c085003c0710080c502c80318805400300b2a8a01d03070701e80c0c00c4880c280d0340440346940400074401070b5141c40e040107890712545100f4450079000d42d401201003150f0741064203181e84209800c96017291603141403018000c8070402920111034054482d4007082501f21301d001224240760361a00d0600051210740d5442e050039014207240d121081c030001407003c0c0d06070b480c042c0c14004c2180c4c0009685513a9105915064041d0b141d001e003050368503025204100d810131480c141d070300680403501b8404c20400f41c01d05a501401801c0b0581e800700c0d80210443c01c100d244501c501c14980515a5201c00304281c00410084 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 959689874 1250 959688624 959688683
    0x2307170102250201020715170112031710091508010509010501062d05090f2d0303031303050a090b040801061a03130b100e1e070f09050907051b0a 64
    0x10380082d041404480c990541f5040001131500d0074207a02d02d0303986000c1c40b00b40000e07001806001d2110380c140082c1984846004000100c4c0c60f80c0ca1540d00f0702500600e051031051084012840c0c907400000f2603001580300c614018040a0000d000703614261078040c0c001c0c0000d00030342c0041050b80d10044940c50003003030150700c1c50804900c11825441140d4080e01c0320703045a030183d50701004107404281d00b900c9162242c840c007408120246008810f045010704c1408200a0f100e0080e03009108110003000d5111010220b1034244c1002d40d56502c2d8000100c900340d0080c1c02c18101c0c10720010300002e00324815400841100c5008800001010071002050002c4c442034440c0c00c03000c01a1111400401c200f5900c042e0801c8441c82d200d107185507034030030100c007407801160691003030f01045e03103080795041014231500d60224240c134205400c00340390340d00600200868001c0a00414000c0001007015004004407001c0c0690241d0390000d0b00500c0c0c3e400340e541c54040d58122244812414560002542144584003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 959691124 1250 959689874 959689877
    0x1b0d0908040323031219090303050103050c0105070215090d0b090f06130b061e040e0a02040f0203090a0b101214120f0a12090c060c051501032307170102250201 70
    0x580800c5030180f07034170903002504060392151700e040f10041c0d1082c42c1c881e103240c551213a01c001c00d0380d615501340142031881400c0703140d0510000300300007401690742c140c85281c507001d540109a2a511150040b4401140c4808002e10500021080c0462017400140340280c1000020031280340e40c0d101045440e120421000040124030380c680450600e15003644614902e208007012503e03103490140008042e6444c50390108110340141c00c0800c02d5040900a06960602d00c000552660404c6c00d4070940c1c0746288540a4008003000001c10076140074400c3c2034004004012070b80d80c0741c901a0600f8000c0d9951424031501610400388035201500307080c0d023991b9603109040c1019060281d1034005490788242910500e2929940d80020000580080c0c45600a840e480c0d480040d00455441d1152811f034200582d0101410341c1c400400006403040f00340000000c0d4140c4d5001e22207518000c007840c100b05170300240d0214900200507002e43c9015405400e2007590100d1450081c01001c1d92407002c00d641c1c0c4030190 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 959692374 1250 959691124 959691127
    0x30f0108031303290a06050406172d0607050a08100f060c061b03020301180203011203050c03070204050a0e1908092b03020d080109020a081b0d090804032303 69
    0x1010561a00700c26000343c103840c2c501c00400b4620139041c841c0340d0045070000b070211750340d17036081c803580c109449607a01804d0202089111010f030800000e94943e14000070300340d100e0b210120740c002c143d0300701a0420f01e82001001c4030310500740503030041c01b035401040301d000000d005580090038644140400f038048030b294200c84480f07213092400442d0074420301b082c16255261074004908040c00003203114021902c60b81d5005882e9410441200b42014401c040790508a00500060020340d01340986011748903410304010366139002040c038007802c501030100c01a501c10702d82030070080344146030780140304c0002d0750340190344031000264001803180003040000740c8144014010712244c0d0070080d0400549031a002e03040c620440c80c4c1910003801061100301240140c204116800182d504000703858050400b8003020340c20403c0d11100202619401410945454007149141c220b0100c0c14007181c0304552901801c1c041300d84c040c02d02c07480c0b03588544000c03200700554241ca0780c0081c446140d0010128200d20103503 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 959693624 1250 959692374 959692379
    0x2103050606030f15010e060c0a020a081f200d050411030a031d010e09040309030c0e0c1c021e0c1608030a0c05160303030f0501080111070206030a0b0405010b030f01080313 75
    0x4008070344e0300c403502418403030403140300e205503501c06000e0700032003008000808180c006441032203116070080c2e02408141e0b101490f4910094483c444a83c4800452040002c1240c0c0f101009900c0c10820b0b40442c1c0c01601c00212540030000682041c1d2246000d800c0c40d00f0781400d1304042c103682e401d401c68047d00040000d481112030a01c0c1105046400340145003842d002c21691000492491003654201c0210300100001c208001320182d10340010681c0d5520000c0c80d14028121813070030320400c10105000c01c480400c0b08119006641915508502c41c14941c00140610644418544c0404021120751050240012180303468002401c103a0762450040c5047c42c0c0642000d440480c8110303800c9829000d07902d000c8680c1c40141194400850107030b60045103030302c0d110605504407041030b04220301690401500c0c070044002c0c48119906960306030341e201d5880c5d5455002c1e8004044032400302d0f904c5402c1c8800018240c5041024600070180545003005036680e07070300c001c1c1e960300c210041500c6145100204 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 959694874 1250 959693624 959693641
    0x120f020705010504090f060807080319020a0c12051e0307050c040b0607150b030307030f080708010302010e2205090c0108010f21021f020d17060a0915032103050606030f 74
    0xa006d0410304d8003180050f1140c0e8414240b10280c0c001c2ca147e0350010456555490094103018442ea14500141c2a001429101e68080240754010704548040c2102d00d03800700201000045100030050807104030142070b09003915200e500c84001030380c4030300c243c0f202e9510764541032140008034400140808d260080d00d0b50b403d9001c1200d19008403000781da03802d4482260300d0500c01400c20910076034859881c00090b01014140f0b01d0040c10b004100301014005100507600400803030a1440200e035407841d803003e0f00c03845408000fa2142c00c40c801d581403005018501034001071107103180200341c032103c0282c2e0702c82c41c2000201026100e00701e050356940e550400502600291000524005400110280244081400c000300100b51040040c0e0190311908010380d48241400c4d05080309044503032047c140240000c0c0e011a180c003d0902581c2e88114064503204c480640500a641c800240680c0181c0400304280a40100707480c0c0780402c0c00e02000402034501042101c0c03040c0c034050055646510395100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 959696124 1250 959694874 959694881
    0x10080919020310050a0c14130303030f0605181803180409110301150e091908130518011401032702061b0a150b0a0618050a03120f02070501050409 64
    0x30207036014010000c0c801c5840100d4000c0510940203118041545000001d0042000c481b512154815074010f00804040c66403030340d10441142c2d0545404580403c21280d0704005044aa10031079108140da0721400c080c44016203203900c125203881c0808941c040b8410119100d06c00c0c40b250410a406d215031810f41ca00d8194440c0b6851801101c0001194540e50042402c4500d0048190200d0290640801c0700c002c0f181c4074182c4c803100da4405010054070f8100215902c1020020040445134040303448000407c480c00c00780001c10340140b031807003000e10b01d45241203440b00a019401000b08503a00072862540240901d90843c40c000007202d44d4101051150100c0c014140c01c100ea03c90f4003006072030b6003800740c1a86201554184e0b0094404c070075580c40c01d207540418003a6070041e65400c0a98040059440d44100c0d41181d1460070540b44046054440114194894100a42c44020301e50080140084001ea4071244e540a441d0080884801d0301c05a913200e10603c60355000800c10403060006070250380 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 959697374 1250 959696124 959696173
    0x20f030c09070c1703090c040615120f09020d1208070e0604032312180f0a0e0a02190c020414011a0c07030212030a02100203010b07061812020c100809 66
    0x1304900c51200d580341505146030700903115103170780c5e911040584080d0f141c01d20400005101c03000c0d44103e611b046e4500580500b0b640580ca03025155110201c0170f1242c0c0540021449580c028070000e42c041483c40e08038508013003a10301400013644500010412405500444c46d01e8030018040c6050a246555051074141c2c10307000154005018140300380080410820700d0104540101c00c0c50b2103000907540e56040d1b0a16000ea28447c4035000c1d4144602e4407907003424001c0c0d034000440304503642e5404600101901c01e41146100014824901c140c80c2c03603205c034010220500c222000d1003440c011480300040080280141c0e081c40c1034140c0c1d101512004900100340380c0c074102d0700fa1085507030b4035000101d88030010104405030f50400070354440e6059040c0985c58000112003021130655041080600b240c0c0075a800c0100a2580e85003000c001e481c2c1d00d5109614190f0066001e0070301465010000c2d01c6100810085016607280b2075891310050041c6901d40c030886d2008020300c41d600040c03403102501c0c040310 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 959698624 1250 959697374 959697383
    0x31803230c04051009200f090111030d05010f1d1801140c03041109070219061d010b01020d0c03021b120a03110606010e010503040609022803020f030c09070c 69
    0x191250540b900c03603004092103440c070b04400382c0c001480c1580035010346600203d1103034501d01c40c10385d01a0b01c42e07511050380d180243c000d54403034481540e100140c81880b5441c0040546110210f240da08a04aa410241c1a2100d50040d0078440c2d9070b4403503408201e48041454400360f00381030001001c105004030150f140c442e001001140d0500c000f1100c24114405075203000c0509000000c03c0103105100804505000b4181d401058074500304000035191500d18003003030f10006a060505007406107e4018003c54403442001107401140c1c1c051b100c0c000d068812103103002d4040d200c1d903a01400d00807241d8903603054141e0007a201030110002c0142da080180420709030b0020380d050041d64020300070441c0348040d512039150203800a9000030f81750328111001f48041c0c10400d13146d80d000300036640300c015680c11680c030020100e08250944000381072200c501e920303030ac0a040741e010540400700010f5941021a4001d499060081c50741c3c409060301c5156000368030780c0107180c0501041e41d80f4440d03403116483c0d6004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 959699874 1250 959698624 959698633
    0xa080a1a130b0306010806090607231903061406090609131509240605030601140a030915020316050c01020d0f0504050d2d02070509010b0703180323 65
    0x6010006a40c4400e401d10760300030960751142480c1c02c1c101000200d000d007290703000502240c03030803100d807583c1d528005000c0d10400103c003903080c02c000481a040164110b504402540720b014100c050b45507420440c242800003801d008000a10781c20440c2c030303058010405414145022502401c0c0009a4000301d000e60304100c900d41100c3e81701c20a03105811a4810159005c50b00500d044103640546003884ca40c0d07008840d0001160081240308500c00d0200c508900741039480b6607070040142c8107800300072050840f03080d0005040000c594598481c220182c414542440c0350310182000c801240000c5034141c641c11132081c1c540b00c0690059014214603003001002500d00440c6001031000e443e0021402c000c4181c442041c401000b1040c40241400c41651814010303030300c1410b40d54400e40303c9442c0d245240820480800c140e0a101b441032102519010b0000030695031340d16540b00881c0c1c040102178000504500320145050400c600c120101d0790056500c007140c035207000310104130485160409040e03104 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 959701124 1250 959699874 959699921
    0x54b0705060702271f05031903030b09040b2a1623151f06030c020307060e0f06372d05090703050616172a0a080a 50
    0x43c6403000c18140707813030001c4e900d10350a1466400040f0780201c014042c00d42c0100303009202e039803000101030096803c003c0346034049050a003000d80003460716030001038101550301e04000510105649450003041ca10300e00c404038078541c0089208002c8a0150101c0865040002860700c44541440d681c4c0d940c019070400b00400b140c1d600302000c0c415802d4014146801102d0b884009160a03d20075610442503c040e6211103110610f510741c08209009240034140e0341d41c10f0002c914401c100b0b4550480c3d000c0340400c44e101500480540d00c02c09058079101c05d100710701c0003406010981181a0f01a01c0642c00710000d440d10013951000d83c14018955a1100d030348000346c1840309104102c1008018a000c1e00c88051102000c030a826100000c00302089070b0711180302000014000101c41e5400070505192228506150000300c070000580f02c00a14103405003004c5c002c0458074a00c048541441c41a81c00042c1001e1851007240e5018007085180890441c10000c0c40694183d00400c00c2c0b070030f030803210342c04280 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 959702374 1250 959701124 959701159
    0x60504030633050f040504020f0d210e0a05010c020102101806060902030f01050906130f0b030a0b160305101215020a0207090f0911010c054b0705060702 67
    0x10001d880c04242d125034120821203820960074209602c0c1c0161401d001902d01038000c9800b00316400c20030b50042c4001210003040c8854030040c100303081c0b1100110703407228001e1080241f4010005034180e00c00c01342030b41c000034158040d0600580c0d840d81a006841e8103080b5207103800003400c140c002c101c18260b21190041c0011128495903002c3d02c4003a6005031a41049804904c56007c16000340b40600184002c1c0721050b55482e070404120421800082140d3b0505141794010b001c0750312070302e5058810f42c48604204888a141184100029451208010504071044082d280c094910301108401c0344428455451804c8146990324003841c0342001011100200000300e0388009521001030700b00c00c1080c071500d0741078041d008490300340100a100f82c041c291501202040161480c0341440428951041001000d11910045c241c0c02403910f0b00229000500e4010760f0050b0158503048100540207219961805082250481541340104491801d010a02c18076911407401a68040c0400b40f006511a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 959703624 1250 959702374 959702441
    0x90206030112030e0102010b0105161b080105011505030c090f0d0f11040c030e030d1d030c0d080906040506010b030603010e013201030308060f06190201090c0801060605040306 77
    0x20403410b40c2051840307042c2d00780180140b110551a40c1164104032941c50b041c0e034817006660305500314000c01c0c03030605618501422b42a050340d9540006e21222203001070046010f50006048030541c42e4120b0380702d500c0301001ca55030720003190307502d16081060082252905091808080d44800a850f004403c03101ea12500c007c10482c540c1191031804104600c40c0340e04090047c9589802130342010300003864030a0f035181d1203015401c02550801e90318001110840002c10030f0000c17810905040d00c0d9030b4064041259103c00350300082d0804210f8038400724080039000182248100d4120001d45070a900b000400301c041d40c0094491603044d03484040c14030b103440382840707001f08002c0c03075400e08a484024100a84041c44082c0d2203460810815401040804d411403c40c50348400c0440d0501c40003a410030005801d8020085900ea005210300007080784107405500001040d070280840850540d0303105109800d03140c644c00f80c0400a80103000030000204140c005100c8440c01b01d120201c841005050195003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 959704874 1250 959703624 959703629
    0x2601060803120c07151406030106060f020303011e150315060e100804050c04181205120f0405010908040801020a0305060f030d0c0203010b18040303050708010b161a0711060f090d120902060301 84
    0x2c841c0300d070087c000b041c6801d2050130010f02c41e90508070160903a441d00a910f0340414410394003a509c2400888640103070000011018200b03290000701540c014480c028010a030a1040c113510340c0802402041050080840042407100103055000f42c0404101c01c40f0020005002100c1c1440381ca041c0104944e01c6004480b5101e100351480202c140082c20220001640010854103005042100300c82504c640805036030b204c0462613603160540c40e2868002c1c010200c030364000c2c1c200078022501045030041074008105401243e90280303c2034540300e0410010907506600c19078035500441030001018044d9501854403400100002100f08480000c07a04142044442c04140c1114070b04000800d03804d841074641001881c6400703203c541c1010340d14000c600c92140b40103044c0300f4510001c0100040618280300300400d07114110024104550050008148014815035501032240001c0d2108901c0c56814400d09060009001d003507030482c8240e07094000d03070039003104050b2580000b0340562181e0004600 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 959706124 1250 959704874 959704901
    0x3061e0e1605100206041b050301090b09010c1d04180b0a020309190201140306131505010207080c0a03110312040b070b01060e0307030602132601060803120c0715 71
    0x144160041601c0d507600768241c0140e8403c01216031000001540015160341c0300d030303006001c48440300700c12020880d1016182e115650560178017a010b010801040102401109404000e02c48942d0b50342c0140c4802400304009c0c07111010440e41a0380034603180d00581c44040880e400144c03d11510b8540c84a01e643c2103032100362407a00003042c040720300400c002d144200c4421042c2c1d44048070707950b030000303101301200740c01d103d4a4007010020038902d59507030009840740000d551080003034245641108208541d0b512450303001d070096810019403190049905105918000c043c00303d92800c0d030ba41c131003052001103400b580603c9404001845045244010300161030f5071072000c0cbd03d8130741e40e00c0c2441c44040160441030030440c444203500502c0e180041c007a4103590b40b065003d83c83d0105000d0704050b20300180d0003540c4410403030014400f464408040c800140c074010300240301d02908c0d218020303a070348242d000f0301444110500000b540b0842241c00780107168459100900800b80c200503440503103923038111001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 959707374 1250 959706124 959706133
    0x10031b030b0f0405030f0922090c1a1209010b030304060309060b0409050c010807020102091005130b0405060724050c090f010207050f0904050a050a080703171003061e0e 74
    0x801d102444003010741c000b036484550065403509568040e102e02854440812850700480c20024543c0c884e0500d0f0854102d20280d01c0c0500100358000010b807054482c01d13600400030352000f24a200040c103405c1079680104440030300d0290000400b031780207c002032a40919540c1c50381d090140d80e900348010401030623039907408150721720542405000c0f560148400c5100d07034600302c1d00b10000790000c502c1d01801102420410040d80e0741c114103a0281c8510302025038803081c0000320451040c1c1000140c00e17100448202e002c1419121780780483c0a200328050b195000000b440b44a0028031220784034084203111046040c208400001c2400558406a460300c0d060000401c0d000c007d420310308a080d100c0d050902c010500185060007040d03030a140300d04164000d032080b000180c18000104482801c0a9003c0103d4000c206182003040c1d40341c000c0c1c0000c0380001c000c480e426040510400d0414081c464415481e03075410701e55a1f4210060501c0d032100d404010008a00c0d00311003440e88a1221003c100034040c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 959708624 1250 959707374 959707379
    0x10e030304030b180105160e100c05060109090b06031b151201121101020106060e040e0a0b01060203070c06090e0604020a030e0a2d0c15020f0f1e0f0604030810031b 72
    0x34255a8002d005e00c81c100d0704001c180c021035908c41048418680145c41c8413508200c1300d58115421a04250054124440c400c0006095801c40c0d10482665000741c3c01d2001c141c8481040640350301d401800041200c540680040d41450201d1a0711010070b28001f54520f80417101911a6220000f607000700008094048100c082c17202c2008101d0620318244020440941080009000b080001024500841d56541c000707202c0001000010185034000640703076065a5280d000039682e034480e460446c1c103c2c4545030f001441502550840f010740714402903650a0303075601020300c00290441418042019101c013000c00203a002800541c0b805801001e88200400c03c0e03103a0007080001124407601d40070039500000c030102c2da101865606442c60440c12010f0b0b4005184228a8040340511a840a0150802035048034000142c204083c4031041403d09100030321003001c0743c40d0280c084000666421aa00240c0000d00c28040141d000482000c0c1c802e010b0f0310398850803440b44840d82540b4071245034001c00d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 959709874 1250 959708624 959708671
    0x152a16030b07120504230c0a0f090b09010f0306020f070f05060103050f1203060f15040f0f06030b06091014070b040506010f061202090a211203020901020705010e030304030b 76
    0x4110b0284420750140001d080c02c2c3c0c0c42000103161b078035a100d801e00c1a254500d0003004103001060709a0002400702d001c046e15118481316021061080302642403600c5112409804d1081e00e0504a035101d540c03100006146842d610007a6010510810001c0000c02100c000500c0039881b603460030f8007a00040c101c40d07040d45001c070b241c1b408402c080e0200358402c0210b41200181c94044a42c4a41d05944030b000c103903441b00100d1818a1581c01c14135600344003060104d9a2004400d209084603d1034000c0c408095580c00c0560403540d00003c066006a0208020b000c0742c1400c43c240b01c41882c003841c280d1021b0703c280120b0007041d000350708111040145602031005122040003c40d01504a460f5800a0a441d01c2409410803400c0762503003064680200b100c01c103a645048450000307214500040340340c4a215030042c0c0315898003c104581407540c00c20a00c100380d1203071099814542040e0010030f54a420140190303000000310f042907505100070040400000c400540c118010841d07d0300a182d07107a0783c95034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 959711124 1250 959709874 959709887
    0x708070320042a03020c0a17070501050702100f060509040602090f0307150305011401020601031403040e0103030c03020f06060a05060c0f01020d05040b012108030606190e152a16030b07 81
    0x2182c3d420107005000c0403243c020701140b07543c2c0ca00d6128032940418450040a08100d01603401d0250595180100b0444415004900c6110300015000d003081a190448541170855096004858002c5104000240064007650003016030301c40080c110f0900c22212400689000510341000403040c281c4003440d5009509401100d016185184d16250741d030110b180000e5555405101c090440741a03200308100d07400f828001c8034040e1800d0b00d000d00c0e40d980c40b0f0601416175080440201d0041c42a00605c0d43c9850700416502e00401700103040341440b91810003003010b5a0022620551a0300a0402182400b2001d10083c0115008503201241034a410308104030b00703200c140c3c05100d44400804075019040003403110051410345c064492501c98031200d003c10014001e5010351002072550307140300b14145400140b8400e07041b1044031030b042e0b080c06050300e80a0754010b5034000c070100c240c444407203196a1650034006004091142c1100c06103035240084000a120650081e0340d0321900350180600154480c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 959712230 1106 959711124 959711201
    0xe061302180c040501110c2d0a0306050f100308030406050a0902030307031116080309060708091f090e0906041101020309060d0f0509070807032004 65
    0x4504202543c0980121400702e40407260200c2c094000103140007003000c002d8010550212520b1104d8240810144414089921400b00c8101c03a1038462944000714000c2d5404039a0342032403520300d045203d003d019071442401581052010400c03d5040302d0700181c0c410000a060b66560820310024000c45400942c9400300052550915502c0812000180c44a4080c1d95505030400320205d00b2035500d02c25a207554100740f1026030b140c6840c8024003906030244411520708503015000030442e61030168801c20152020060854695102c0c6000002c0d0041503910144c1d410003103d21a62048014002000d001010009a42c4d0b41d00c2481030b41d05144003d4051034594032420f40b1240501486a4a924080e240600040c00a200082d4040c2151299000380c801e06003140c680042075010748803040d4400308400040d100c00d481d10300c25031441c4c24612501010a4002d6603014205906131b4 = true := by decide +kernel

theorem cover : BRFrame.Cov 959532374 959712230 := by
  have h0 := BRFrame.cov_init 959532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 959532374 ≤ n) (h2 : n < 959712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
