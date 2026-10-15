-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4325
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:15:23.313988+00:00
-- url     : https://prove2.me/submissions/10cf9b96-d610-4f40-abfb-fce4b7d02dde

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 777697841 ≤ n < 777877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 777699091 1250 777697841 777697853
    0x31206031202060723030c2206031a0a080c012109030e030f070b030606130306020c0a0201140a0507060b030102211e041a220c0510112d0712 62
    0x803802c05c841410318604403040c0800320a0107880d4003000402e06581c58505849240c5505000115a2a4075003480400402d410b54507410a15103080d241e446400302c051505c0c02c0c4101d400300d5200300405034004007500380d142e40c45281100d101e4401010b8403800c80700401000b0f0125a4210340403004070300d0101414050f4181072220002284e400405800030619000c12584c0c0c0c0d01c80144040d100d0040000c814111050348202007000e990010400c54444044440d03c036a5100880402c0c2e005c10080101d0700c4107422054100e600c1d01682c1e07541e6605100182d0360f803038003070114510304d00da040d5001d20052000c1540707105075100d1134900c0d42800c00b4900b051303004003114005d00039051040c41007500c20400401c144005620580c1203c0c01c0b14800c642e1800c1d210340030882c03100c0c0d52090502e0303481c003035034248691410654142c4804995100c400c3d01540d60030794081288000d007115941100001150a0899603401c2003083c0e161131a0002c124001c804260a18007150405644e0340e0388440d140051143c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 777700341 1250 777699091 777699107
    0x61205010801020a080a242d0303020a06090c05060a0906030c020102071109060a2c0a090b06100504050d0303060f0603060b0f030a0209061b011a0109030312060312020607 75
    0x224001c02145810050a0003d001c1100108605840c03a00c070700030051840800345441c0110540c0864100c0c100b42c440c7c032040a005000c031500a9030b12202805079004d87c0d031700d910745801c895160b0010510100903542d85000b91403888400e440e80c000e038210004158990b00000c060380b10541c4e0700d0061060420001800301d44100d070100c0110f83c810301c0300c640000e610b032803428941e60003194584103542e0748400040d20380c400c0d50000c01044030b16000303000c04a00d8001c1d458028192011044407240c1d5516410300031904008000b8110303952000c0403842e641030034496510b000c244c51422038581926180070548808200700108d000a03914942002080e2500102c2e8018100629040c020240740c5500d081c072038050315000313650424000000c41c5146101e07038125043c0c80d00c0a45241c0c1c13151501c2c10050451600f03101420f80f00e500f06001581000d800a403001260f4005864a403020b03401d6460407181c0c0001c3e060904140760340c5201c04804120403006610144203107034024644c1d443c20150083c0442 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 777701591 1250 777700341 777700349
    0x20309060a05010f05041e0c02150c0a050711010c0b070905030f03071a0a06030218191518020d0501032307140d080d0606050a0e090402090703051003060606120501 72
    0x1031030100144511306102030b1100850b01d04440204480006c4030f160408071604406c1d00148516001c408046a50045034070f012080075075850314032580e5800301010240c825001402c000442c00c1100c0700000340c00410b014014801894121181c08031684ca044400b070083d20b0f03400c003281a9500c204800d2400300702c40d03815514040b01541c200340c0c1c0e550f1070101c203030140c03040740c00003c1441c80000d020040703603401700d402150000c114569103981c440c512104a03000b42c40032100c6030501a00b0710340c4901c0030302a800c528038405101c00c0c1c185140403440c50400c4080b00101c2a10341d0200240d46d800c007c82e0240502840c060b240781c031411542803010f510250702007815521250001c07002040110120103c12030000c80956407810504044d14042d0311607c02c0342e000f070b0707122460301002090b13159101c005400048000d850720001c00c3ca54204009041d00211002540900070500103409288260015074000e008107154041d13564803552042d06803101a000f2000040400502c004000b0990280e14010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 777702841 1250 777701591 777701611
    0x3032212090f1205060c0c0a05060c0a031a01140d060b031005030d0c1e03110a0308060910051309021504030605061003023903040906090f02030f0403180302060a0302030906 76
    0x3c0d070303000c2d42c6143e01ca900c01042c020502d040031440054001003840001c0c00c00303a00405032001071600f40e4040030b054200c81800700020b880d011048010701480f0b000c00b131010405031100c00040000c40d511224590040392450001e60721103600203038843c800e002842c060b10b01c0c0f8104500050030001031520b4903482d569910200601c0c0381001d00030800d08030303015404020204080d0310a22460405980b1132454407048255442207011100074140d00503005800f400c0c00f152400c40301d0f100c00308080c01c1c1001e140240c650025106901600606017039100c0714035648060007082d11200000e20620850b00070f5402900d8083c0c8810800ca000c3ca442c0d02485040d08031801c0031800c181c040d0244820035000007484103600020309203406074020328150015428190241200d6465480303186c6080501080e01c21446c1342d50804100d01c0c01038500d402a01c1c443c1006a05a0020342e503503440c1100c503040e60080408004146c48004005070b00c0c0c1800070031448109032400f5949040c01e905282c5000002090941c030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 777704091 1250 777702841 777702869
    0x2070b06040b2209080d0504030e060c070603020c07030606080a050606010336080c0a0201020f030c030a261021171c051015030e03032212090f 63
    0x90356442007029440c0d481040d01500c0700c5603c0b0a4240c0041c9107030000980152004126000504a26000607214510a9541d1403074481da00c1c080c402503002d00d035040300c5a5007186806200c1d1030b210303034007820303800401da01214095aa00c0e20307424122415a08001c1032034004410120900600b040380c3c5070400c03801e190400550703084030f000c026113088460001119501c4111544060341005600c1c030100c43d001400c1e603643d003a8801c140c036618510310004a0141c003c070009110202c0c800b2080c0c480d00d44141c3c001d07501c0c05806190403950005034084441400b41030340c071010b5180300e6440e40b051060b00540c2e0910091404c5c80d00700e0b10881c80d01c0c11042140b0000e01c0c10f51000401c00601d49040e008400314950315024001d6003641032400e5100b6402d000d6150108000340144c10003c091300b143d007070301c241250031481442c085007901e5400d2000c03501c50380304001080d01c40d0135036100d032600c01e860701c5024440c1038240ea9441a2524080035840001804104107000c4940b212040c41c0007001e6501492203 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 777705341 1250 777704091 777704111
    0x914070810141809010c030f020705030307030b03030f0c101b120b0a081033180204091b120b03070b07020f0901080a03021902030c0d050111070602070b0604 69
    0x5010003500511550640d41004111203483e000003800340d07101e101c0064031a5140040d0702c50b009214600d0010300107030800300403206002d070a2084a01c0c49401001942c0b450703a500320705901034400060204d40502c400c21041e180c0900f90300141500418260150031260001040c620544145111450b0700c0082004078810aa0300300a6100071600036510201d80075001a00107040c0c407116601415080c018401e004040aa550f40001c103046142d074001a1041c15820340302200c1d030704800b0380341940503d4003c2400521413012084003031002d038074405803038107858440342c8080d5100800300041e1204a80090440140c02c41c8031801d00c240c9031041000b0758000000026903550461184d101660f800244d84020f5443d800c1b00744810f4031001d0103441c01035a450802c40d0751592449401d40060040103034070114054084100c55403250002c1c01010380c4102c0b0420011039034042d5008545940d60380e504c0503007e1010700e011b00b0017140100001621a4054180601c1d5000300909a911503860140303840 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 777706591 1250 777705341 777705361
    0x50105040e24030a0302010609060905061e0310091101080a050712020f3a0903081807030605070c060608031204030c1a0a0b120c0616030e0a09140708 66
    0x96000c0411607034408070748001d0b040c410741285000340300e9806000380b00950f010301d44c05401140884584441c2040300300e03030b940c000c10200c580540b12240c0c00035003528500d40820701071000002c03000f0b000b002c4d210158100c11200f4222850036000f00da8801c40216900c0c40d41d038014014550041c0003103800d001510700894000c20050803c500c418007158041180303140040120192000805041c844244001d1002c010f007031241d0300c1c1e80300b510113014030503440c0164205a01070000103a034151540300058482110360340d02c0c001c040c04c1d0306070503100c1c0240010115011f8082d4a004865075201c0c041c0d201e20505055081d100780c1c1d00102d109078010410800155003240481d94082c1d0586402503c5101030302c1d00303040c240500e80e400e140d8803100070305101408400340d2002c41c0203481298025008001348241d42d40300d80c81590f113590b2110050040c441060000c00c52181018800c0c0b0b000340000392070400041c0e001c02e040c0c02120b1099a80d00043c084224000800d542206060401f11101d1030a28890 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 777707841 1250 777706591 777706619
    0x180913050c10230c06240d060f06061211120f090f0d050405040b090403090509090a14060403030e15040201030f020c0604050a0308130c090203070504170106030c05010504 75
    0xa5000d061840c41d440380b45881100d0700d16648006140b00d150240c10a402c1048030f4019060780d000a003d180081062841141001d14005448402907800818100200303c000c45400c8001c0d00c403507407140a42c4170040850310904016012603120701007111400101d401c120343c01504451584107040042129a03401408459400841c05004106c269501d60a8508003422200134032410302c981c1810420554002014105642b401d6404008020728134081002c0020180c5025010880000050005042c1801c58940c010b03c0300701214603101c20742d9200d00340c03000c06090703140361038103c030b802d1008050f031602641c00f0401d1070200a012000380503041d40720800001e030000703062590351203001400c0800342c1c0698207030a0028003512200d2425051440c1c0b100d11a82003200042c485500041c00400403881c0703441100d800c610604403030f82c14410020025400070b4048030a214080c4400200f00360a0812900030b0442400045810341c69807800340c5400c0110f40195051040c04e01c020300c8204e0729201c030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 777709091 1250 777707841 777707863
    0x6010e0a0e03040504090602360a0b0913060503150a0e0304270b1f0f090605071b0302030328020307020108060405060d02031c120204030f030c030302040b18091305 72
    0x1c6c8801c01c43c60036000a00c40c0341001d04007814411116880c410110310124200710344140e00080a6a03540100200d005450240481c519414800190142482500340001009880300007544944403400246040c1c4075051020103800c1d503508200422201e801006d07a001c4c2404011400c1134188000c24012601c1c80b96108035161498501640c01c0d0300c280c0004140312800303001103100c0c3d580107804d040c180282079042c40104000c1880c41d0300b9144507580344812a4525030b40c040c00c00840740c0d200f10104110001c00d00703120101800200159400307000400d0420245141040000080b10310701924581001c42c0c40c003075400900100d400340c0d030030035070f1075a100408641c005002d565400014148200400000e034040c41504081c0c45209144094181e400031552138940b505d900200d2040281d10860000a080c41100c004000020b8050902d0000301d500c00e050140c00c054403503400304000e4006a00d1300f01003040d280292007030341c04c00d0510281c1110b5007618005486905882d050fa90b58440c2e24 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 777710341 1250 777709091 777709099
    0x510050f100504180204030c030b0609150a0b070303020f0a020610090507080f040501150603020d0e1f110f07060204050a080d140c070902071b06050319050a0e010e06010e0a0e030405 80
    0x70185541a0491781102c0c050f507802030885110980b00d0030300001410302141c14034014200ea0000c1200d040c0252a20b030310321400105215901c50404181c14260b0700054400c40038585c0911028403c4001f02029060196540d03008021500d45803000d00d0410f805d65200d2189540390500744800c0c04e5000010075030042c1e0008007001070751107900d442c50041c0104030b2181410780b242d84010900c0c41d4142c0040c925800c0500341409180c100e820596200d20649000c200c00e41d06116101d8500d4500f03800003420150403402090504036000100c1042d60301c031880440b1782c0750f40054140b040d850091090780161003010010306102070401400f500e1800d841148034002c19011594007860742c0300b00b02280191503981c4055444111502e8003800f031990b807042015100c50845008076a140c41132056a01c145103504140643d46212105507009080280000c0b5401e92252681e0307030780320800d000e098200c0c0c5600e40182110743c54041508104800500381c0c0500c0d60502000780e80c04900001618103448080b1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 777711591 1250 777710341 777710369
    0x210021f140709080c0d1a070201050f090d021b0105090d1109160e040f02090d060501090b010c080a08090a02090403170c210c040e1003030905060a0504060e130510050f100504 77
    0x1003003c81d18081c42025010300c20b07c0305d00401150b5941074000600520401d84110500d807654084107465070703914800740c001680502d01d007100d20301160074110503503941030501500d04209480860070180030003805842c4144107500030041d505241c40c0d07481d40300084085a407208000198010036050709031a41e5482151580d03001c015507102c2d603040340d00344c2100034000c002040e210b150000c00f0342403d1080c140c1143c070703101006629500900511a10a601040c0c1901c1d01e102d20340b0039590100094550240c500c183c2c00c0c01d00041c1c450b01d200c68040c90003a26404201c0d00084006442c210004003502c07500c800a100000c2119295000141454122001c0301f040c0c2d510140c0080c41405039500c032007042d0b40e00342c01380311404a86444020690b40282e5801d1040c80d00c1d042405010310840c08001c00080c0204010040c007845400c1c06150b24030010311420303400148183c010300341c810507100d142078046403400030006c5260861080120305010b59410100c100c400d1409042d0b8021481103105126060b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 777712841 1250 777711591 777711593
    0x70804031107080d1d01050703200303010e15042714010203040809030d0e0d170720040e070e0103080a02120c070e0a0b0d0210021f140709080c0d 64
    0x5481d10044603640d1030100e69442d652034001d0f5030f64521480f007000c085114560442e05140c0003c113010039614040e10b8491500712146d0b0304503030604407420b0030002102807155039100c42d50148015802024107002c40c51a5041200d502c01402c2000c03107078180b10f949403140c0c080001900031400c0113400c40c01c2c2c0314070741104031904201007910b109030020200b82d48000104010803080d2406440e03101c40a074115511808000c900b49c170100c444594040d40034184c8040780d030005104800c0b80e41c55841586d211810b040c81551043c03040700e03c010b2400300c4883c00fa0036001490074144140d0900001d080c0092048520300301011200030b50601014180110004041000d02d00801c1015040401c9109081ea20454914819107070081070280c3c061a248440108c0c0c6030100d1400b41d22642c150080c80e002581409608004651481047e0744042d800740c424580300c1c690700780c54030282702c0355801c0c030108000c1040e81621042c0b010082c032140501005540600c810a4005044285090300740c980c08103100403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 777714091 1250 777712841 777712847
    0x11011e09091d0a080a02060906010e0105040b121009021009030b041209030b0106030c021606020c0d030e04060801020705010e0d091517090d030f020f0f0708120c12060f0907080403 79
    0x2e01c180500d02449807003019010070003a08020701d408440e9500761034494998511464542d4001e00c150444190218010310240c9130a0340004612003006142c14424035244032100d041c90003400929800940c1c0c1c0b100d140c15400c1a10b881c2d1a04240c501d41030b81c903142590360359500740102030006403119444002c0240c20f180540c8022000d1030300000327074001960b56040024003a101d0141480010302a500700c2c0d4007511041c403100e40035901c2940281c103008c009002030009600031040198108454804220350b540c45511501014041d4807001599420362820304a0a683e0f00d000d500070564400041050001d41c4202c055060f96401c000b000100c660280c000c882a1a02d40240450b0030107100611052400c0056410b19015181d24140502204180003000b28003841c0d00e0811000030401961301c02100441c01042c08506c5960f103036090a0000d0a50070302410119100310159400141c000c00303c48170521860307800201110002c6131081c200300401c2c450704c0080c24840500003014086010140 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 777715341 1250 777714091 777714131
    0xa0914030a0203073002060a180b030702070e09030304020f0618030102120a0b0f010f050c07030804030303020304020a24030504020d1a011e0e150a0b03010311011e0909 74
    0x1030000c003250300b40e5440d0710308519000380249200d0320136a04003111081c1d610f42c4600070485e80790000c041030f0070450050030a80e07540803500050036049042c0c0c000444c0c0c800c61800036501400b03035039005141da24141020000012800303403122050754814420000166507801c0c2200034502d0a440b01c50703d84400c0320002064010205880da49940085442891014403001191141141c88014040d50103480d09000f040b0221070b10650000e96250039181c2803500650081442125190490300050382c0c0e030321254083c3c0c00c103800032000242c0000a000c1507190010f4440081d1400c0d02d001094017000040c94002d2400455004045c141caa200080a5682d02108810495040f038142c4540001a8440030b95044003401108503c807124650341e4001c81c01045403c003030341c40001c900807017a06c805c201b548102c4031446407150b02000c0d0210105040d403008011718000d501c5044200c0720209090005003c207000c40001345101d0600c00c1b000c00e03400e5031001141d02180c1000d10005548880d1020100d10300e0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 777716591 1250 777715341 777715343
    0xb130c050f030f04110402090d0204230a091209120f0303021b01060f080d0c021e0d0309060210110904050601201b040507140a090e07020d12020a0914030a 68
    0x1a010040103880d8500480302c40c4200e00c1020017103028214030f0100700c124012402c01607002001b090040c801402c003540b1821f203480c40c0fa034072150b23500d200440750742d002d0f0021904888650389031000d5004200701c00c41d05036021150750800b0f1a49900b80700d9000b01150f2001006031654900038603920604d0300a604450a440c1c0558895000c04824200710340641014451000f02a5504000245920300802d400351802c00c1075403a03000d0b40303429400704049840e0001046150f4180d2150b01c8810781c3e159140422024425211050324618117140607052040120403c1403e03420030200c1d020b03a03000201101c0382d160080300c0c005081e455032001240c0d08480a0420883d44503000300000c42e4940015206482520400c00031245661580900040c0c8509440e00404035041c41c400003c00071503800581105481072902c2010380d0360311001e034204201c00303a44800240e0018168200050340c0405500e550803000e207815440c102403218010811b064034800c08103081c603000c0e80292141d80c1030040c41d10302 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 777717841 1250 777716591 777716617
    0x90f1b1c0507050a0806011b17190f020c0a05061b0f030c01091502161502090303030411011b05061807080102180a091a0f010302070c0305060603100b130c05 69
    0x42ca040c00b00a0010ba10903000035020821040020740d50f0340c801c446900d01d07a450440709005603e200d945694401003900700c024040d034000d000c00d5180082081c840049440d441d6200b481501d2404006170600030900348242c051b4000341c01c02e11542d21414112682080c0b40b03161550301c0c1214402250410500c0c04221140e4000000c94003480e150540082d00e2150103482c02c80c0b10b01c2c0168003100100c0c0714051280c000240394582d00c07004a00b00b03510250a078452103001505c1c0c568504002030440c1d10031030b81100c1c1203030180c4403920956440708030304501240740d480e644010f0405840b041c1d07864000420840c00c0d0b103441c1c030020700000001d11803500140904002903403149601301000f4019000510301038000c624281002440c2025401140d101c201400036000c5801e8500042c4404d0713204c18001681850f40030404500024a1081c81400940c081e0025012504285081508103020304102e01001410109a0821035550b245182c4660203130050025814803400b000b030741d060150a00c00041 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 777719091 1250 777717841 777717851
    0x1021603050d14090f12071a0d1a0f150904020403120e0319030503040f1208190209011707020a081c0609020301030816240b090f1b1c 59
    0x100000019103592a070190340300c2c00c0c1250f9000c0340500090082c040c0031a44800d40c512034860b14104110402030300200c410035180701c50b494100c020440c65542030780869010f40060a4145c20450b48107401d0141402c5460075409442c58001078500c90320b080030380b44125084545108031581a108440c02040080c20030b5440b166079042290410b54a1184200401c00d11a082d24192501140709080c3e107442c682d4001ca211005e45040315940c20040c02110010800b0300150301280c08072610741c0c0e40016640c4e42c81310902d410750101c03019504400620414074014004a005aa0090181c001c5402540e140c0d841c90394840c40100e00d04920400c003e090290005600c00e1108904100140c4110000740c040c40460356440d010b5081b44024440549988002c2c0300c102c00303006c45402c9500049000d403c00d000c4400d0100c81c0d42d801e1802107440d4050580d40c490b00c4038914140305c002035038045a0682e11881d03a151800001c43d04002d1034455010445c3d0000b080c4c0c84078401ca0204c200400d424800800c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 777720341 1250 777719091 777719093
    0x705070b0417090316030606060503040503040608270c0a0504110a0c0609080c0a0c050102070e0c07030306080115140a0308070b092806051014060c0a0219030210090501050a0e01021603 81
    0x446049176000954840341044400300b8400c5c010710407030b80150f500c0b0008620b40b6180c00c10403903c02d5000307041e42000501ca40130fa000224007104091102d81d01e014050260748400c481007208800c07031644614040c9041a9620740303d03400e05002d0301c0d001445410600400c01030342c54610000c121941008004840204112800c4900060707284d800c90300c2800500c0e0107544440069903145000c1c41641440354030440060210038118025140c00c80c441e007800315044d62685040307420f46000008c1100c0b4200c41200810640c0106050441c03a82030580f0013900c005e007580c5420259200f00c8601a00200c400000710b0119241004000f4904c0030b00243d10000d1212045d181c0342c01251450265065401d12000c5250419016803900494203e511480b85041081041c0070307180c4c11000c403070b080d64011650340e1405a2545010401103180c3c240e01c88400b142035204201c4a91000011041002102c1400340100d90308038044845208071420041070007000e003070040b441c08581c0348002410a4500e00000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 777721591 1250 777720341 777720373
    0x20901021f0203240d320c100e0a0312140c0d0f020607080f0c0f0309010504050d09080d031a0d051f0b06160309050d05150705070b04170903 62
    0x14003450214403141c0c40200700748581c00c5061494169185c0c00007856400c9400940c409800c0d41c40203031884101a110403104d410140703140418844017100ea00712079900b040500d00105110f003007407005e0614803d030701d40e4000401d60001080c00010040d410304460040154041c032001841c23a40b600c1441070341ca41d4a194a29183c4840c00c142d2001304489c1410361a40a0003c10902d1198a070ba6840360302d6583d64245410742c80d04050400304401c4810000c4800305696000194070a02e00040041911f00301072030700918103201c1007079210401100720000d0000c4080428540c43d14000c620740800c2d1403a82201a01079500e0303240c540c81d4481590640c01d030403c030b0301082904585034000d1100b0701c4a400075020178141c40000c03400d10341c000350030001c1a41145100038170b41c10040c005d207400812941c440022a60702d074a003400039101940b02c0c40e0760040c1150040700266000b01581f41103400c024445e40e50100b80c40d0003500090002e400e00c4510030308240c41005541300810024202c030303c4203d81a0582c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 777722841 1250 777721591 777721597
    0x6150f030c150e1332060f01030c050a2a0605040b1005010215090f070e0f010b090112020705010f021308160303080f04050a02150301170d020d03020901021f02 70
    0x1105400020054040e0070300400810081c51009407419445800130100e40c0020f005000c454140c05010202d900110880400842d800200001001c000d9042c140c1c00c01c0800c603400c1407410304160903c12014010b80e03000c01a2030614a990500c003206c03400220520150340403580c8101344030581c1100010a205113504094000e0b030013082407102644400c04a407003000c0c5603000740d901590111f086402946088010203a2020400342030310805c004e6239141c181041440d62050b42c6103d100310074080e1444401c1d0f1582c0c018035000d0302c824074190503407002070000c484905085600c40da020642c001407250030340103040b561079811030031951202c2a161100f02d003403090152641d03621400a15001450041c1e44e910203603034051301c40c5c100e2990795604c0d00004120041c000c5230103000e0a4680070068a8100702c414801114100550b101c0d0f04020400d01c544011000402503923101c0c101c20785000d80c0125a4256903681442c0259451429000503403509407140a090101045580078543c000381941c06 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 777724091 1250 777722841 777722849
    0x92b022802040207151b0e10091a03090f06040b01050d05010e0105010605190c11060922090b1e01152109050c03061005040b150a08070e0d0b0406150f030c 68
    0x308120b46d290b048440400442e80a82c17000100e241e5004810481c82c2c1070701800354140580c9800c4001b591a904400c1c0501030860412490340400b0051000140301480703074400c2100424010300d05440c0035120a00e200d44180300d1103014005008800041c080c0039007250304020a090028001565202002049680003000c0103220400402c60b01038103900c10000351985603002010314403d500006c0410025610140c0d01640c003050f9801910f035140d20010f40001c2c0311510a2000800b2111401c2141010350018504100000c40000310032501c0700101229054a1140745043c49050bc201c1c1c058800310860f285d500c0302510029408031980301280c00030202a4812001d40b80681c0e040c1d0241035a41000781c84064078803280c0401403241d402c044c3e120788000d40c0000c11914070f841414016400c42d03400016400e0001c1c5501081140040d0070929443c138110066400e944092855180d10300441c0014100805c03450303c5003691a850003c1d00d525201416404070704031641035a0345480b20343c4803e144a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 777725341 1250 777724091 777724133
    0x3030a020f100c0503150f03060703020409140903160816080910020c1e0109120b041a0c071103070509100f061b0206090307090203092b022802040207 66
    0x281144400e90540644075404146071105405d40e200c3d05141d06c01130444140c816005901000d02036419501001298000c00517520700603921070a24110700d084c0c80b410702d20780200c00100014001c9007400003080b6000040035a141880f02c409070320300942c07548a48111540b0482d203000c544418000d02c20018000f078181107400c070780c84d000c0b0814180d803030790303202804550701180a101c80301d1440f181d5200300308004414940306001c1e649564403044100f0720550181c4401821178104010408400c041409030f400500e0740c0101880c000c45403c04030b10400b00010030410745104c0b00700440d1001c00201c0043c090091042166150070710203603814078181d101385c80010414180004034280030350700340e6541a1441e450680110380c150240f128580c482061190144a52030000820545601c0a1401a9000000341504020700d80c504040042d00b10074150201c2130f40103001001c1500007403820210746c1007810f0414040d1900002d1641d403410420081d400c1400040e1002c02c108022a054903039190947d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 777726591 1250 777725341 777725353
    0xa0e160501111507110708031602040f060e0c0d020f0c0f100903020a0f030522090f06181e1119020f15130203010204030804050411120406020a0e03030a020f 69
    0xd40220383c1c981d884060031584030b54203008030300b1991240050b400c40100b408120b825496030340518901d0360303201c0030701021001d109090b41821440e040c020a108505400c00900c00c942c10544100040d4030054100d140b00240002c088560f8103060301525105000d0005107500d568400840984803180c1c1243e5840034040c1c99500000034507288240c4801301d405078020401e10340c10740d4406015041d814015402c0c802c2c10f0000c00142408118100740c1c0d1031907080c2d45850316140064100944612150010304241402410300c1280d41449070b8171500e5041d0b0001044400c106d0000951150f03c01748a0038416091416040c04514010020719500300c00c1d492282d0004c0d100d290417600c030400c00c2052500381d04048501784826003140c2d400e07600206100030105208145600180c03c81e80240d2040b11014400315040040c1d00c1c0c103201d11076034fd46104d41441d103085a100c044500700d9200800040000342d000c00c1c01088288502040002080082c0459070781d80340105001e950740e284185502910f00c10302c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 777727841 1250 777726591 777726617
    0x100806010f1d0f06010f03091202161d0c0a05090604030305041503060b1606110a020f070801022805040e01120b06120d23030705130b0906030106080a0e160501 70
    0x80641d039881031444443c044182e0700e9400c011550581030320003000170903441d40e0200d0046101c0c0d00d0241900303012a00245825446803c0d8481d81a41c1c81c0d219060205d0300d40c42002240a45440080e40030340e807091066661130003200c007610b850040008c1d00c0d82042020801008240d0041c005005880d050b4003840000d880e41a003c03800d40300c550140803001042031054943c1ea0080121003003101c0e205071000f050b0000c03501c0f0303c041c41c2e4000d241b1581c01a4003d403030550301a41c061040201604040740254607140c1183e000c80188400703061051100402402402e0480c1d1064003554050310101302030046559582d0038662265402c07000940d1284a00790108080d440c016014410b0100b24201400420b07024840942d02c5084020042d802c01c035100e0000d0740b1020000000750300c148120344505d62211404610244000c24a40211800410420402c4921b5448800b40d0741110540d152004041d070b11500d62601070601030002d50301074030840e43c4031a901003581c01c42c20140d55082c0d8880400c0800 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 777729091 1250 777727841 777727889
    0x5061602120f041e03050f010b0103050a060f050603040302031201030f14011e0f06090203040605041e031d0d0c062c0f0d050a141506040504150203100806010f 70
    0x2d140b0880e148440100b0040181540003042c1c1110341a803081e0320035659170349441303081c01c02c680c1d441c00030016591800f00d80703409d40e00f620401c0e81004600004000440c2004081c0c107400c01240078591090201000240805208000705e4088085112244055585d00e00d031168005001141c119800c0d00031046c1850100b10511030303001c2a101e83e0700854036884c0c110361298020031828004d040413540b5620040b4030460b290008600451065100190038502420318141050481109814442e005040480844e90121072602442401880e80d511021040d0001304c949031103050090111074808400507906400681030302080000d428003002c410027000007000c0c0d5844000d24190321015440403402c81e07040c208005812a0321a508880c142e00300c43d1684550f500c04881c00c560260f1140e00c54486100c008051140c00100541e014030407401c3c0b560301d5006c0603d40d4900380c0c1500e80e0100015842584141c0202d000780f43d43c0094a00340c0d42c542612810002d070300d004040c4014203481181448040c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 777730341 1250 777729091 777729097
    0x1603031e020706030b060438070506060f0d12090e0a02160b070c081b1009034d06100503071404020415020c1206090a1106070506160212 60
    0x49194042c14030541000c106030001e0110420854100d8070900002c1000c010070300004a020003401241e01d8006421507500303c03440d428409088002e5000e2003050002032000603001d411980850311801d0a0380c0b15000308070050007803400031307101c40e240e0807582600640000341041641c210200c0440342d40e03100e40c0c20341c041c1e1203462a40d0380340c640c00351015408142c4140c07000342c104403a80742803a400c00f01074035054080d402c000040c4004801044568490040c01c01c030b204070b04c1d1058030041c04200660340380034000d600c400b846156810880100d40c00c10b1201031200000704904802e0302000401d11520307401d0195020000320b0a80d109690103d500b142c1509249403c903070005008050083c1000c540d001f929500c0079605402603024040424010810408081c10390001e6004010740c4001a080020120070010060700d150481c005120b83c00f84081205075105800c82154480c0740400004a601441620b4002e05035008010a0085c0c0d004142c0c02c64051020030f07070803035110010b00160f100280c4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 777731591 1250 777730341 777730397
    0x1f05060910060f0507060b1512090604031d030a0215130b07081c020d0f0912030e19080c0102160314040e0708060402070f050102090112020f031512160303 68
    0x60100b05600d000c01388907900405c1c1051143c14003044010310203001c00c9450b912201180c084020201318881c005065024031548016084000c204a0505460281402c14000b01515220021608404d42c0352001c00200440d96030251920303405502480c402e807140d0f000096214003180d15800c001404162580c00c0c1c420603a0020269031400a001c14000c4040d481c9030711240d4116024440a442c0058510642445c51040000840c1102c0d15140c1218900b101040c0b201c02d15182000002c0d184500140d09650a50007041c40d81181000342000c00700d502031007800b1055503000040c1c1c1c03150034544d03d00e01d05800c0d00ca0b446480c103154010034005282c2c0141d005010307042c034010b00040d500b18498800b840d005030000d04018a45405c6072280c11752400b001105070b8003a0740000360100a944d000042040c0e41c208414110b081c4600280d0310350f080c1c84003800b011103102e6000841245c960350702d1561507004440c4030866198040084400b0f001d484a8841035010400884004200d00301c0344490610034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 777732841 1250 777731591 777731597
    0xe0304030506070e0d0b0903070b0c1e09040204050409050d2a020103052806050111010e0c37050f06070b06240c03090f01090503030307030207051f0506091006 70
    0x350f8400d08100c90b8070326a0002c0ca9070019143c0944800f207041558410700500c0507a0107140d40b8002070601117075028001c1c25100f545c080820884048241a08000100d031a400040a656500c04d900040107402142c025960003840c200100e404c100c800a6680700c102565120049114821000075502c1c05219400e03080c4903181c0100c484c019032003548030641c484103602550b959074002c0002c5145030f11210b500703112000c0d0364002c18003441d82c010325060140700000300284070007041206a41c1d20741741c01105e428007503410407454401c00085492000005c2d010f03503405001c5c5562508221000020728400c41e405030701b0200900b50700d41061780845640b99009a02803047e81c0351b11060080d108000031400b9040d1180f00a24100d510307003000144000c901c002c000316190f4403220b0030810540072110304603051002c042402c214a072400720940e42c0c400f10a060058a410182c20f00c541080500340004001015500241482c05441d502c014010b02043c0c8101d6025035560786030106031a0070340100404 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 777734091 1250 777732841 777732853
    0x40504380a092a0b0a0206070806030c0a06030e2b0f2d0e030f1f140c0c0304050901030c091404020a05040f060f12050d02120702130b090c09040e03040305 68
    0x314200f02180c4098890021182c0240d8a80b090340050f0840802c45005070004420304c1841a8800b01c611f8001c40b0490280503d03d5020b00000c03503013a0103104c1c00d000c0c95180c0d10ac40d005000e050102c1041001040810241c0345000c0d0390400100c0d41c40a02100490300513411260924410008121802c018440c9000c02d0888d0ba014201d0984180803017800b0400300a241e043c1c0c5032000d05c0401d8442001000420319001c2001d40544042001e0703401d100603a280519584d042d00e040251a6001399603941c506a44082e070203019400c6104a802494100d0541c0000100b005008007045044030b2800c4000c000390117040b0081c480000050318003035030054020405200034a8175500c910505090325000140d400c3e84e075000441d1415160b444100f0090b10284000f0078024180021100c80d461071005c3c1054075007042602280d801040070181c098640015401c2ca040c1c826840410343e410020881c040b05d20742a49815099442640da060007681811040324801a00006031801d03241c2c08409451 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 777735341 1250 777734091 777734123
    0xf10030c030615200f1b03241b09061e070b010f05011d030c01082205030d05060d031b080f0c0607090510020c040905010b06030c280e040504380a09 65
    0x2500b8983c01c0f00358180182c14010b80d9038a00000800710f04242e9208e061068a00110060071a06048100340000482004440004d0ba500d808075241c1080c2d07140c050490f081d2040455805000d5400d004201c0c04840d80042242c10400c94402d0440f03000341c1e03484040c07175003401900d008040451840c5030940d0004046180541c016020310382c4c0074000488020720340500c04c3c52480c12101c40130b425616034200040c0610158124005c465000e00c0503a40300d0406500c50741c00400c00c1308810070f0a401c214444260b402004001d80454110010b2000b0303446d10b55030805c1480362550f40603030701d62010031080700d0b00203000d0420300f240c2c442000454022f41043e2480c8018400078200782201100c85560320b0365503000d1940d132500070f940140c41440700300380c980756004d42c040440c102d0f0700da0b03c08074240008411240d0f15030040c10000d2603207042d200455039860318035010a000030040c0c41000802402c45029004418510340d46180ba24592480d4900b615200340d520100c8448020161400b0b20a40341c002c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 777736591 1250 777735341 777735373
    0x302091e0d060b060d020d02090f060403050709020f0d05090f060f072a0206040f030b060306040b01121406010605071505091e10021b06060f10030c030615200f 70
    0x104603c40081c140c10714120429a56a040341e00030070500e9050b43d404a400386960030001d602500c0410f080e264207241c6030460302c489540701320921a5840750b5400140000e107000a01055030036240300d000c0180b16030b003000808181c8035508003994500620490340003079080802c0c400b07000e0240300d26454090458152507801003141c000b1f41514042401c40d80c40440040c2c03501c400070401481824031000c131042c118500200d400b00e020308083c3c03080c4d03c1003040c4004a00d00305000c5045502c00000940c1c44a05845c280c009250103511524641c02540c1c000108203420a00404c1514030880035086804002000c0c0d00480340c060761600880d82c1300305150703811441c100761110441e2260200700c0e8004000300c196a41643c1c06400791203400185104d0006908004000c6a074011104660100040c0180f10100b042c20110130804000c05403161040e007100c60003035100d840900400c540d130000c006590300700038080c0844803c0d0001d011000042003095050b000c074182c00c0501040001d0004401d4040303402d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 777737841 1250 777736591 777736601
    0xc0a080f18011706010c0c0f0308040f1502060c18090c0c12040e04110310020c030702130e150c0d05090a02180106080106050f090607060e1207080d1d0d0302091e0d06 73
    0x115407d40354000302181400324442054000d6100791600d5a98500f412a41c5041c2d030380940c050318600c54600840340c1c8084d00451401c0e4401040303082c0d1511004600c902d0307180031680c01c1f0443c1d0003100316001e0001416880f401049488240c400f1038030715003c0240c90b199148a1403107000e02c5003444e03a01050000780d1203410b428602c2030003402c964003c160861b04404983c440e00d0103401e15840069150210300b1322030a150360700f440a84040040c0520b6020444d01c800e12100e09412070200c8000241103020250140e44519460000401c003e192039611141e44083c004402d0344a0b595100769681c903121644181c1d410381d0016551030340142d10700303c8181c415402c5201c0c000c503900380501000035981c80b103101501d40907004060210b9000510000d0380c2c10807000080103c480d910801252020601e00030031180c4034410200b000840e2000c01d02162040c4400014018890242d1902c071161030350705402030400c540c0c0403207020030040d070070b0b02d0185515412442100e0300440f8248482c0003003101a401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 777739091 1250 777737841 777737843
    0x6050f1b010905030d1407030504080d150b04082a0d08030a18080325020d050d0f020a080406050a0605091306061e1a03090c060c0a080f18011706010c 66
    0x803550b450b240c1d54903030454100003440c065a40d620580c00c1c0360761043c4241d56422100600341041142403e444104240c4144909500030644a1130b007001541805410a4010140f003101a43c480c1d480d10300042c0c41c0c0001a02c618003200e00c880780d03000d030740007900c0f4010307107448000740190848a6560b440e44090b1304014414440301c2d5461480c005004003041c03d41d0a26445520344603a01c2c90012030441d811000c14402d04004490740312406611a00000d401d41001d6181c01d00545030070b2208008005040d010114090050011501000c4590020030755030045201d00c1c5c1c280708550791942520b0880741e007849003990051107800072038003003802c15007a170b0329441c042d420100d40c0039102e5810100c0f01011100d0103006281c445000c02c051100c0c6001c1c9240c0704035600d142ca10b141824000da1f65a1440f904005108507000600c111190408005042c5ca66a1254155481d811022204070203a0840c4051000061522484044642c822074500c1c0086a4022102e052901c03a02e00450744800c441310 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 777740341 1250 777739091 777739093
    0x150206041502090a0b07030305070f02071206021c15120c0b0c0a0b160315030b010303050c070f12030f030c0c0b07020c0409050604050c0901080604300801050301050106050f1b 77
    0x70f901c550f038603612104405840000c0810380c1c0e034802443c00900b16200200304408210710440e802e104140d0203d0510308880700600380300d0100e415801c202c3c00912520a005c10b010030303980d901a4811074180c0005000460344203000240d5640d0395030841007440c00200007052040c070614180090644e50015280039460101241c10141e0117030b441c02c960007003d03035440c0000360082240d61080c0d94140221103410001003450b2201c6851a550710030414018000142400008920003a0030001005490020443c02c041c0200761640d07800d238007107007040801054001840340800e12039814007901030341c3c10b0805030366a110080c4400d600e46034600c0901801000c1140a200050b00e00342d60fa60080501e1140907401400313203401c00740f0b081441c0a42c01c0440c24090345180c0010841c880d000f007005940160000c0c41001d1082e10390705000751143c00210b844010944514042a0740d560010442d416128203800801071a62907445c15985401089a41c1440e010100680f0780c21000c410884440d030a1060 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 777741591 1250 777740341 777740347
    0xc200327030a0507030c080c010e0d03180311010f0314130c0b0a080906010603050c03040f03020a0b090d020606010e10031a0a080d020105011e140a080f0c0a150206041502 75
    0x15001070705100c0b1011050326140d21160f010710521000381c002e40000c1500b580102100174103000040c0c21040c04c002031600c02c0921030290000d02d80203024122485141450800c0c00c65181e1418002a0105826680c00100140328400d00680248192070380b50800142040ca01c0d60350004080d0050089c500484a0030854880010b0f00f0300d41001405031880991540325103483d1002e12240752180582c0b101042508000602075800341c1c00c1c044940190700404625030f4146581410780c40d10000d504000c040f01410410052004070116500c40040c4459090b241551200001103074038420100c00f15a01060b000420301101d4041d40c0070007030142c04601500030546100780001e070a840c0303580c070100d0a40c10a0305040485035082c8285800f41c081c1c50710107800c001e01100c1416180c1184c0c001c2c4034190352000d0000b407403503880d040303810001c0c1401401c0b156810754000f000754a800d20100c00074021504e400b00171503440b11004200e001030007580c1c020075090fa1261241c03420222980200c00c9003e41c20 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 777742841 1250 777741591 777741667
    0x102070308011205120f0c010b06040e0106260414160b0a0309030e0d05150708040f111807050406030c080402090f07110a0501150b030603060103020402030a0e0304090c2003 76
    0x141c02501b1344586038010383e91540301c01482242541c03800c000540c0700e50410803017489643e01c140031290540b8002c1c81c2000c5014200381200201c18100c050100c9540b44000c1040104804a00c0000c0c69821a42c00c0c4c800c4841c124031080d14042290040c0d034402e5206011a9103024481d0788040541030191a0100c900d410800c042900384026410540d125000f1071201340c044094400107507003204452070524410319043d00c9880d50800f001c40c000303140e0401604110b00d603594001e980042d423626141e40c0740840c00d00c400c1c0500389030b00a118140c082418a2a0203540038041d050f81d42c8600c0e00a0034400c540d507522010030040800044c6654144044a1080c1188610810403191517903c10400004c900405120b2855420405e03417214044950410070070a607500c0100e10b403811070798107503005600c82d02e8500000c00035005603601c0854a102c08030f0005964412508107101d1380300c042e200c3ca000c43c0c42c814042d01d80c1c1d103108001ca820303d83c41000403a03025100001011120409e00a0348003100d180 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 777744091 1250 777742841 777742873
    0x40b010f030f230609091c0f140a0c0b0903040803070623090a0618111e0d0c09060518070e010e0a14030708160302041a0a0303080a0b030102070308011205 68
    0x5070764411400340faa40c508120081c2880740c82c2a07000f098030340091450301c0c02c0541b40c2c0051510340c072188042240580100c1c103c507000d4129000b101c0c0360000340903150461f202004103030081485040d50300d007000c100481c04041c070120231241a112032801451038012182c403050054003007506080c80003903021041e80c8040c0d4403065134070700507a4403c018000350440750500e401500c0d48051038961074489000180001120b01c40891a80340e8140c60440c0400100c0301a00d03d00c0d60321064954100408406010800441c1c030700050649442d46410001c403500e40c0c088c807907114111400c4159600743c01c0b0104038468005c018255980340145030040c1580c3c050408540800103a80c050a140a82c14616141d5450140486006001140000d01945802246c5e60000312a244006802166510358036402101815a414045034014008903600d543c3c81c50005d12401089500790f0f0328a2a001d07000300c0500e0103001329100d048e090740e20326000740d0918a082c0032079140b0400480e0640b0807500e002c0300481d6 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 777745341 1250 777744091 777744131
    0x60b130516110c01081f0e090c040f020304020117040501060911030105010e01140f130801060b03040b010f03020a090e0c0d03080601021915050402031f0204090605040b010f030f 78
    0x60922080e075512091008050400c0c45070806650751030700310041c030518503640407103040d500c480c1c03101c007006515594080390301c8840c2a680007582400b4000b42008203081c070000d2005d030801d1050301d04020f00d2113a00e40f5002280010750b0002c0c0003d41e040341c0000c000e00d000d603015400c00c2c0950f0000a0060350341e08a4000c035a042c0d0941d0411090220041003150b8010992007140c070000c0c02c200d071a000c0c0940c1c000b034140c8140c4502e100d030f10401060032a0003940c030000b0034014100c020002c000041c1c80e0b03080b9001980040b14201d41c82e030004000407450b034ac509583c010440f0303405000142d42a040c0700f9080080d1038041d03d00500c0780709001075001a81d582e8180d054a8900944802c00c031390520500081c203011444491801c01d134260911540002d0004811070643c50740350b20001007603103c910000b414030b401c0d042420100d040c1404449801c610950050080352030541081050302d03078400512040c1c50000c0e01e014049003410000c07503240741c0250002d030380044034001e0000d40300a003400c119652035 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 777746591 1250 777745341 777745351
    0x117010608010315020316030213051503040501060f03030e011b0f0f0b06030a02010504140102030f0408060a050a06080a0f0201051e04091401031205091302031f0e01050d060b1305 79
    0x241d0303001c010414081141d88a0107282c00d0a60250b1461420140c02c040851249610104140d400200c00300d42214046a020140000030301c0072851600501c4212301b0703500240e40c103540035480c0c000700084038003000c081a011254162900e8061070842e00041d6000c8480004143c5403058190020300041c0860345030090451180e84030f00d07240c0f40b06050101203113400400c0365000342c0c401105040507070b81100648003140c40c02d0507040910000040105d0030350045040d108521640402d02041c09800814214425101b03031501300081c0c0e030f038600080240c3d0000e1090045a401610f40d00000c900055903958807240181844c0d894000820000d5640301c40c401c0d801c040964020031b0a00c454101e138025602c0790050384200c0805541580c9564042d03030400c1982005001001545c440035880e0041118042542c0c3d02c4110745a18060b012002e000603103445164411005200c0403c00351030200d0064140c1c4e80c090112040810b070f1303540f6200107011302c090255114a90045440341c045070303409018070030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 777747841 1250 777746591 777746597
    0xa060302280309030e0303040f091a100207090513170a2114010e090c06250309050306063a05011a0108160e130f090305040f0602070807050105070201170106 69
    0x74042030800410340c600103241075206c2e400c04c100420444c02000130542c2540d46103400060204007511030540c04485001034940c1142c44500790303881071500442c02108540541100348419a210350341103502500c0c0c00c10013005500c01d01d80d9020320344030600103441e110150f030500e0015010161030741c0600c400e20031281a082034461f050300d5150b101150440f401401030050780780300c50034900d0340c0a03144c04400650901400e030205103803e80400300181914120b8402900381c0f004d441c54113005100c0350180c0200742c02486400d01180b028180780403100d0000540443c40c0d1040c000810101c0c51907205920718140048004000d0303408518203110307180848414100c4128840d50400000d490890000d01c3c0e01200ca02d02e00106420070f80001c580c01d00707203104aaa2002180e02043c01c84010200000440040f43c500b0a922003056000380041096030313800c6000040a41c0e86410407651550a030080183c10b4120200810030740d4001c1c0c003e001103d10505000010a1b040d81c03c0c0140d8a009a0001e400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 777749091 1250 777747841 777747851
    0xc0304030c0c1511030c0a17040f09020a1409010f0f230910050a0c0206090402070501050a051807060c02060c070b0a0224010305060f0903090303070605060405070305060a0603022803 80
    0x3210b40100803007013a00000b6000d0f50401004040c0903480e804070b048041c3c11010045118000c8203044000c46014010a4011540352a2113002841c02900030659000110380032404400051014006540340c400b8143d5600c60a4a104581103a2544a242440c4144100c02492007104101490b1038600c03203404035000394403642440d04100c00094040078810501908008100d900340c1e100d030542604580603914a580d40c1d0f03120010900070300c500781003c0c04651a0005000c1c029010b50022406000c160504ca100c29941d580316035220025441490045000305c0c0304000141404000380580c403034108240c9074010380d64001b402c1181c0c0035144840058201c80000e80181441c40f500e44141e00001828500942c11540d03115a20440a40000d140c80801030000340182000c004840c4019006819079869000d249006800b0340400d40e0001e200e20b00740400102614420f100d513911400703004013045060b5250000640095011503080003001f40d80c2610707807490405021002e01030f849203540c0012 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 777750341 1250 777749091 777749129
    0x3190501060509040c090203090a060905150601080c1806070c270c0e060c0106241d030307030503090c0d031101140606030117011506050c150601080c0304030c0c 71
    0x42100c805402c5244030311452414000800c82c103844c0c40041c4d60b07500702c1c0140e49850b44800ba0317152450140e0000c00c0ba60a1681c8441040404501c0c0c1c50241d10100b001d42c1580c5a40700150340e44034045949082d40c680601c0000004031184a6038101203801400042c80d1020701d4650011142c09500128000705103940300700c1c1700c002001d00011900707401d03080400040c075058200514170311000c0312052182d00c002c140901c40d84000e510410080890001500600048420441d224600041c0031808180b048800d000d031800d00c400f184450380c00c0200518070b020aa81e60a60b160342024004180c5803054807140040c075200d141c07126084034001d441c3d03c1c04803100341c0009420b44484c05080b400c880700d2542805060b46814050307d0645a1000e071a0071030218410b11980140802d500c4002e90410450001030096000401001c049040b40c037511000c890540b0b83c43c13300c4500740c900e02c0c00035403050005004034030703410702a42d00603120345007940c440513042c2c0720308a590310310b81c00840c03184080100f004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 777751591 1250 777750341 777750343
    0x8061e150c0721020904030e03100e010b010905011e081b040f1a0c071401051c09051504082706030a270b060d1e0c06020c040203060906120705031905 66
    0x10603c2c0c1080b07402100c0440d19501041413048013600040074401d030307020712042580d800d200e0f2080d002c0052504115a150000159010702035840c181400b240c000c9102007125403003a440381d1426440b2066000d40981c80c50021a004040100350a101c00109407904507065101c10041008040c50f40c2041d040d0b03811b09180031544040310b1500740d810342c1d00f000f031500403000100c0c00f24100c1e41032288501d00c1542c44001620b81d0f02c17403d0b401a4044884083c1c5000c507030340650080301d40358001d50884501c611509a4084110b40c141c03000f0704a14800d01947c00301b400410b80100d00d040a080e01d503100100440c011075003e820680d44604e0803501e41000c442e010452148542868203004003060b01c03140d540e125030b403003400301402070b50280c03882c0801030060019444030074581c0620b20f001c000300c80441e82041241040c2e24003503140140030b00f0310b10b10251301e4540203aa00541c0e00810910158444204120340640c190820110600660900052b41c1d03905000601c0c42c1036021810281c040035600d011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 777752841 1250 777751591 777751619
    0x90206070c090c14041406040810451410230417130e0108061b031504090828030f0209011b0f0209010b0d050a09030c0206160b1e0708061e150c07 64
    0x3070b40c9901811500080520580141d10341d4503a071a8802c03044601c0c181000d10300410200d031724141c4540341ca8dc910302d00e40c0c1d910500c1c040c0a60700d91558040752030302d5500b196a20940f4050055505400f02c1155491560010520310400b158004d2085554103040307041c414090740502040d40100d010043c200b84076640d0b113050300740c5900b64039207140360240a640248800c105600c1c003980e5a030b03503540300700003040003103407001c1075000039591980c5904103500082c9e0081944500009003401c0c520816000d0328001d64803440d4058503800d60389407103418021100c01c0e0051081d2400d801240041d00980c032000e02048c0a400c01003002070b0350380031f0001a0010341c3c40180080c00340520380740d00c0c4404260b1054400c5801c035030440e8240d50f580780060043c00e2465802c400039265941c00340901c40e01c000c0905010f0590b050780005000305039243d03101591a02011112240c00000003130244080e800e16a102d540009002001c416240d072007140302c14956000320302105220b2b0f116104c1486404040f40328 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 777754091 1250 777752841 777752891
    0x1103070e04060b0d09080f070b06011202040e07050705030720040c020c0a09050c0f03011d090a030c12111002040303350a090206070c090c14041406040810 68
    0x1003803103414580380391000340d84200790740c0d00d09613661004144100140c14049803040480c5403107d90b00d40da007504081c000440d0941d8860302041c2042800c0340b100d500c13402550204e035607a0b1800038441da520003003510f0756404400c0c1214a4002081020009001018844030034007144107041c052210040501c01203e0390068101c065501504078034000c1e548209910094030b8020001040d1511010000581406175140c0c0c07084401010001060f07051206d103582810900080e00601d0544488030382507266849220f01400141c044006c20002c5503c4110a4008503801e250030b107105581e041c046410980041c407200000b61b00080c040040c11b6011600c100700d8000d456040045100c0d4080c00f41103002210725211070001c00d540003a4020741e05900101d07102c0d40180207141d50754031030301d0101c9a1480701d000d0144043d140c1400300b101c07540f150002c080d0041d201c81e559490542001d01d080d42580c01e0142c41d40c0d21010810002c03c400c07000780511114614500c1001c218a403000c0060f480c04056101 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 777755341 1250 777754091 777754099
    0x1121b032c07120602071410050109020304022d1e03060c0f070f02010c0b0403261618030515100801052401020c0423060d0507050111030c011103070e 66
    0x7012408010100d851012221940c2c20744400c103096240080290045000c0a440d0f8800800c540030440404140c1c90b040d401701c0780c0100241d03030720350422008a001c15038010b0340002d100da211820340d45401c00100c01c64040c4c403500d0984a400b40c00003615204141c0a0701040051414500080e030400f00082600503500148583c204088012000500c0c001c91501612406d460100ca40035a40a0b80010b81c000760420400348031490a400c01802e0300da104034192001001089606280c1c00510003c1c6020700341d6140000c5440c0c0d2210412a20306a1034030b89d4051a09a4110000008604100e041f040c20000140c6042030310304000c44500700841980b00b441640d0512003080405480f40e81100b000d05003a0700d44e46c415124680040745051000001c56410034a000d000c0c40e002c4204103d610f51030b0840c10480f9800d0350750401802250844100010065807107400240403c1d03010f5600364540c21182c40440e82800701a01c0c4003400c0d50218100c21038429400400d0000f00b907442140c8000390700041c1c03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 777756591 1250 777755341 777755411
    0x220617011a010e060d1e0b030d030608070b07050c13090308010e04050309041e0603081305040626120a050403061107050d0f20280b0601121b03 63
    0x42c1880d411066118131481e0b001070f01c001c08501c1d50b48003405180501a80340300d030b04812614080103050b0f50030b80c0f501ca481442a0021010f2090041750700f0b94040e20f003e000030b180f500200b2512a04507000456284c0590545003056440b001441d4040f004004004119445a1309000c0c14002040e0485040b40984500b0003011910000480b240e01100340d40001d2200b4642d140c04145551650354500064113220740002448100801f0f0b2600314000c81000c00f42c540d5490421040366682e211358403080703480b544e9605480380940b071520740504494007500c2e2942c146009106090b403020f400715000c6079000c07809000340303d5a032094801043c81c00c03442620f40096529000d070f41e5085503409200300720302c050b001d400d840d100b031810407038402e13070324010340d00808030f44600340d88403410050f809000c0c0c64140c40c0e1b032980250749181d503051a90003481e0000c840c1c550600440300030384202c9482c1d0400303456080308400700441c0c2542d03002154241e03400042e60252030b0b41800360350604401c0011012880 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 777757841 1250 777756591 777756641
    0xa050d03060f0f0b07060902030114010305011a0904060b03030f07141204180c0e0d030c050d030203060607110f0d11011d0f0f030709061502250522061701 68
    0x10201c690545240c00c103020341700d2019140c900042d0222140003034040d400e0000200c0c140410542007416030703204400074412100d4080100282d40000362800da03000c9458004500402c03000c3c4d021000c0240003030141c0303142ca0850301552000d81d101c140115181c0a0000c031503040c580c01032104007000900b00c0c100d50325151400b441d0350001540e03044240a855951403403034203030f40c0c01402508419200944208100305842c2006440c014102c1015101c6020b0050300f504594480d208682c07142100070700c00750030040b45498018041c0064402a6040750942c0c106500c9a901c01c48800c40b41d52082c5034416940e003400000422051140c8031034580d001100c1942a07040d0303201100303158918001c2d82d02c0714030003414078002031a03d040b50348036820543c0741c024080b030010600ca000c203900801139002c5902552000c0e40102410380301060202c1011240c1d00c09110600c3c1210b0204513035661400012242d050701c41640e8216805c0380e1104504841c0c40d03d440b40d10300c07800e0041110301c140e030104030300c126840 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 777759091 1250 777757841 777757859
    0xe07050607140a120c0302010e06010303090e1e13030e15040b130302100c0c080706080c16210210051909030507050d08040311032809080a050d03060f 66
    0x2000002010380000c821030740c1c682002003001c0880d884d04100640390100c02400082d00800d80404168015428074042d9440100001255412a035060b521a003140b4508840c561031000060030010103400c1c0e48408400f41268405954014124400c2c01c82513286117150203001c1d00d441404450260802d10b903500d2071400b09000b42d4003101d50ba600341d199034207003282800c0b0a280050b0402580080c00002580d0724950082e5946140351003051507400c01c940b02e808070760382c64442d0310880e400550348000199092041401505180325924011020301c011a42c1e140f5000d08034a54840081040d018620754680d81000341d080d010b44036480402c5141031145146205108810a070030309203849032641c8041600c1041203510302ea41000945c0d014000440005000901c191000e60000e01150710382920b1030b40c00b0003100c907103882c021140c901c0608a000d841c0303d1200d0590b00001481349031070300003c0890040c09541c406a01c04d4020b40203001800c0300203011145917404c500d2401c00002020300c40c07200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 777760341 1250 777759091 777759097
    0x26190b030a0303021b12071e0b0a180b0405060f100308040b37172a0409060902030108160e0f040f080a0f033213240e070506 55
    0x10b010301c0c0150303036242c55541e141301010402c2640e0350305101d4030034500049407012011b081c81e9407041ca5100c00c4140d00f0140700c448810021400b0b002501a600803803107501c0c840e448040c003699114500c02d20350655481700e1018200454058070907401c190204102d10610504c0e1590050071120700c41005400c60311140b006000e180900124000c00140504081d110017281055112610341020035000c00440b0448062451101400204415049010b10b11100090b030710310401c9014001600c5404c03400305486007440480528406500400c40415000882e00a650113040d00e440c000d82d8a52515080b40d10707085244c8001c1240a0100000303000005110900e2900f120f4a05007545450b00ca509080c20f055030001310007002e1000010300c00158507009459500f136440307161000c11450300c0d40000003c01c43e4441c01e00d0003009800d00d18071107001440c40801e0303030040b0074800300c07004c0d800c4c0d1903a413510650004120720700341c10002000500860698080e01c0d02902948001d016044d2601d004209980 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 777761591 1250 777760341 777760343
    0xc060c081026060108070305060903180d03031d0127080a08070306090c0e100809032b090606150306060504050405040f061e0e010b061926190b030a 65
    0x408480007203604a60071446650403190a0b0181e48040d6501c6074151394890702480121b0b01400f407400000d624002c0801520042c1d1600394542c001c1c003061008001d40241c00100440a040d5a02036030180342902c840c0003107100d031181e4000078079080c0301140a0300440f048541941c1c540030061030b075800500520300346c922a903c9030804021035190400240c020341095082139840d2071410040030425584203e200d070075400281c40010705c9820500c804c8600b8141242c64035040e51040083c1c80b10020780d0032200130420821120300440e0360407407402d041901d401d0034094540c251145401e01c40c171503d014030381004080c00e040c104810741c40c0c05001b84c81c9019520500e8800c1d0303550800201440301c41030013030b028a0303845003007000740070318141d100b0700542110401940c44a2900702030008240301440740d03844040d0024010746c2085c08190a0401c5038110319009000c002e6146001840d40701d0f4118002c504180808050002e890f0000c11004019120300440d54110700300044071150341c8020070200c5040d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 777762841 1250 777761591 777761609
    0x1150302030322080a060c0306240e0d0c080d0201060e07020703030305041a0a14070c021c0c0e010602030903011104060c0b0601050c03040e1008010b0a0902030a0b060301060c060c0810 81
    0x12071000c20124412007044c0e00c20111402001041c4041040942c04052001529201046403a881c0c3c00a0382280d0440740e41d04103507280035004d4101040c0241040c03511140c004250002c18500b580ea0804420341075485810380d5070108980810f030503028020f0001409841c582401c003490f00800081d0358050300d100103014195a00c2c040b90038000741c864009084500000600c0d00e42c1400a010001002d10a03641400d03d440c0b000840c440c0c138415045481002d40080007000039580c0040580b001000280e02280c00703000b404400500000f207940c20b00c0c020412500515200c46036007041c1400e44141265440004908110910046030032800c1c520103550030484240e520f0741e501d40141d64a220350000c4111510022800084c480552010240714071500706600302172907528a0360a003a5500c008807158041002ca00510000c8015806150301504c884e4010428401c1c01c0080384140c2d0007070704000d0004070a054400203104460080c3d10500c0c0061600d90914038003060007100c403c03000d000b04088 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 777764091 1250 777762841 777762877
    0xa0b070213051306050903120f07140c0a050a0b041a0103020a090e0c04021b150c030c0d060e07030f0509070605180d021002061b1e0c03160b09011503020303 69
    0x83d40c4062070b01150072503002034100280c0c1000c1400c2562138002e006a040026661070020300340e8060821068010412500d80c6204451130382d8044081d80c00011503819103206501c41040418400c000a0842d02d0160094982c68242400c05c1c80c504840030350800c481146500040006864640b00982280c1c03000030001032101000a903a030502d090721030705c5a401400420086900040c1070b882031039031130b6900100c941032a1031941c1c40f281181c00f19000000c1030f80600011340110319400007080c0900f40103900080340c644520404159480036110701c0300180d6118607600c1d028405129164000e0f056900030130324646024401802c6202c0c600ea54000310500d8610321850b6107402821921980c1c1c0144000c11266803144d000b9950354084842c54001c000040b032314541d0b5030210003103d072011002c6145801a40b11400903031225804250f5454080c0704c1001202c900454900100504600c1111502d045043c0041e08909481c8075142c441100058146e0810050781d0010480d04c0401c00c01c0c1e000c41da = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 777765341 1250 777764091 777764101
    0x6070212010213180c021903080408041502060106110a0b061e0319021f080708040206210412020d08150d0203061501120515010c0c050406080c0a0b07021305 69
    0xc0a4010704400c40410311000c2030110304d143e02d81888180c18120800c0400035510310b00406c0740d43e4188170302c030801001c0c95080b412022921440b1015030181c080c402061403c3d85da190080a40b2140c01c154100507000400188017083c3e002c0d0007613400064900080c0312074090740c0c42e014000c4002400041c4115401c004c207108110703880045c040440b500406070f854456818100d1564400700780401c91066203403a10450b0030000d181c0080c10f15800b82c2e0740d80748007541c441c9416241d00030081d00a0741e0040c2d05125407902d82c1a014a141030003111603242013000d080c01d140c001c452502c030310f106005540280050034440d81d48003848660055501c1840048000543d010620708070703541f4070180d0140070310310800085d004040b501c140a0300080c0d0f01c2e0500000381c03100c00f6080f201700761a1001140c07001e1305980c62541c440e0762503541d8540a1500300d01c2103556040000d04a41041c0c2c4054403d4001108205881ca071070010704008000c0e84c10901d2409600354009105203440f14285007030a40d4581c0418 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 777766591 1250 777765341 777765343
    0x150a0503153408070e04020f0c010c110d08070e120a0c0b0406140d020c011b1101060f03020f01022505120303270c0405010603020405030609070b0d0c18090504170906070212 76
    0x5d216008090300840d903684a002104a29911640110026608000209a01c1c0d07208403111140c000070320303000d03201c017a09049040f80ca9080c081c1005003004840c1d01e52602d540d0b19503000c1158aa0220004d003000400d03843c0c0050406401e031b0041146100034403040180640084440b0802c00b0860700c5980e0b070b03c1d007a450280090007260f074410301c03641c41c04584400140b41d100d180011140c490f1205c5a4441e0703100304260a0322954021002c2d082075a01c130420041c00c10f0300e0f020315000d205005560001c80b8003060f003c8203500d103000f1180c00003881c0c1000c1002e8144204110142d900243c040d510b1032401c16000215581b6908020703120014400030040d03090b006105c941c10300b0000900c103104950f07445030010040d400500480744a4040c07000403c20486000402c0411542a42d0b034007030404800900d030030024110004031400f80002d9110003a8540668076200b0050481440002070a04250a00c0c4900c00c1284000c03a180c2c18040150807070950300c0f60203071740d12141e040303428000040700c114010b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 777767841 1250 777766591 777766607
    0x601030c02062a1209010c08010819060b04140a1a0d020d020607021504081b100f08060a0305031b06010609030c052202031302040c0c030503150a050315340807 70
    0x2c0900b0340c000801c5c06400001900b20054041302640c801c4d8031a41c803003003a1a21810b596180c4c880440360a04043c0c00551540c01c1014600b41c0107100003440d070a030038030940d200107003291072080031a82c5100003001080b905c6840100c000054a4055003c0c1d901c0d40800d244514080020b031051401190b01411075840b11a0350f64100240b00a0613200c903910218240d0380c2e201d9002c024401c0b401c01c0d60203500742c140400343c03613035a11580e59400c42c0500c00306021303034140781c005d4181c80c3c10250240000c00850403c10040404c03148110014180b5000344000b113051403418cc01000800c0b0345401c003040452610101c010a585003280e40142000d5042c4480f00d080c400b040d919205940048100407504418100080a8900031358050240c5800880121140b50121130000d0101e0024070200301c03036000c041e0700740d6048540a031401101075107540000380b9045da1010542aa01101810001030400e071080201d600c58030f601c550710840040482c00300c0701018050300c3c00c08001000c4001090f50b4899404 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 777769091 1250 777767841 777767857
    0x210b040902120c011202030c0306010f020106120b010f0f06170c04091406120606010c060e0c06040b1b030f070809030a1407031110090335030601030c02062a 69
    0x5400610703984800b96854480304041e0a022641d80003090218802034000c0360b110b40c200c500024995503440005442140348030940108565895201207001c0e0101070440004500400d00840c4561600c0c100603d102112b070400440d0741c0e803008042060681201d05501240c100d148646420754407140511a140a21340c00303100444d050245141700450008907250007450223440c54507031a2000807070a03507219001c4c0c1d042400114440c00c0d5402203900d0b640008a490100c2013174402c903006280c0010312503001a00030700758065002954500282c0040340d00b103240b1b44054061410300380d24032000e140c18050090007800c02c200004904580750b5050080c5012641e001102d200007414101074240c0e030b41c0c12030100312511518a050b00540c0d240007440803e01d40250754a0f24401d50641d5201c51080c1200050800c1c4010a061203c1d01c40c565001003c120b5491040e01c55101d140041c001425201131005e0131081d0740002c014052805150340b0380d00b800818141d40c0c40e2a11601030000b800321720500030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 777770341 1250 777769091 777769099
    0x31508010c0219030e130606120b09011a0409020a27030b0f09031b030d0f050103121404090f0f0506060a1e0203070b090304091d0d0e2206030201020607210b040902 72
    0x10060a0000c4103a01442c00c2c8c41c065905d4000306c0c42c607105440c08442e480510707241d00101d000c0041040d045c914580611803290860501d082540c0d5803070800c2640c0161880002282c3c0c1c2c21410407846017004030120b03071003000000108540d45542c4034189404406000c82c0204041c010000791904010002c035040c50340068288000740054075995030300c0e5040a00b00f0446642081901d1b0404061402030a050301c0e0010041d04071100c5200c0240c4040321080e0781320350042d00c14032000503000414420051821050100840d200814001c40340c101d5400404083c441c032001e10164050540c0900c1e402c881c8605406450550160008184d00d0340c019514024110f48811080207640c10011000e4800c6581e0704000740000c0603175841089854a006080030501c0d030090b01e20008043c450500c10300d0754440036021100b030320440003110340c082c0b002c92a281c20441c1c98007002c204551f410004660300c04444e141c410321409140564010b41107181108020551b1201e40c01c8400b596181d0140e801d80d54010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 777771591 1250 777770341 777770359
    0x7080c0d021f1406040203060f090106050306041b050702100219081b01090f030f031b02060417090d060b0303040902040e0708090309061207090f06031508010c0219030e 74
    0x590000d586405140140820310042d10311008180340c0303030194482a0061200764400d59480c04280802900000c004d213500440b00710a502240d100c01070400d010b00016600d090703807440c0140900c000c2d601c01c0e0b0310b100b505402402d450310581d5448019100d41a0341141d9406c84800c180c0000ca191461100e50600405407040000040200180007400155802c1200078404559109103d088600c5000f02401c458401620000064070400508448000600300041c02244441210004c500d040700c4038400342e4421000c5c802408807010303e004820804003a410b00d0b203051f1102042c2c8041f802c900080019448900000c8281d40c00d0007a58081d0010340e408640710f56888021a0130854142c81220100c0c41800103d002080d001c002c4802150b0041d0096140105c1110340301848080104204200018000c000c40d118041020300001401140c0d0045080260242004440c100e80c1c0d201c0106c2740c2c07410701460740407a00422821049106140c106060050508003614951190001c00c2d90000c040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 777772841 1250 777771591 777771613
    0x120501090c03060504060509010b03040c12030c060f200c07090222060513230904031101060b0910080601020f1213050607020d020909030c03040e04020f030307150207080c 75
    0xd911000074a8440d56003440450760740d4050004a5906000b0300b60000c40820060021031003520040d0781045c812150703c6400e540e00c2e1200242d10b131155030118009040d410035401403001901903840b01440c041420804d4070700c04580c58840c4801d403071086a5110011a5040041c00e05000c010020084e00c041035590728100040f100184204d1500c6402c20a0003e1002c111140b192041c2c55150903006c5418400a0800040150007041c070303084080348942244800b20301e80c4070010358500403131207525605110400d08000c0340c251010703138100c402c2050084c00710524582d55510a00c00c03507001402d001c40148c5036440100e00b0807403281c15560151207000d080364291040340c0018130030300c0b2845000b105032940300d44c1006910311034040040e60006954031034002614140000b0340d08000c48404480c0f4040780c440786c190850300701d035103c0003600d09208208002e43c1060340c04505441000c5002c1c43c40c007801039440e02200e081110801c0406503000c00c04400304034502044070103006000c412516003000c8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 777774091 1250 777772841 777772859
    0x409050f0606120303071b150207211d0d050f060106050307020709020307121a0a0305060f0f0405060a09050705220e030a0c030c08070b070c1e0b060d0201120501 71
    0x825180b00e805070f00c042100002440c2c0110aa9018001c0740d80c4404d20341d48022510141c01c000e114065610846071a0b81d849505124030040203800c0c03180e01908200c1401039119450b054030a01d4032020b0120450411600101040075651509030480360108070b2000790130302d5840d26521a00442c1c6520a0700008104a40c002d030280d03104807025401c680f01541c4403680e42050740010b0341d039400840d40200000142d03440350380013503615411201c490100355407200300080410242e680140c640742c0002083c0303d503200e20703007442d0780d400358010b8500700c0390382040d903601941c4d1100140003281040e40d401d0003404010b0240141001090f0062003441c06074068511012005c40e149054140107140501c074100c0380d0030100559034540c1c210313244c2e02080349154500f83c4072142540350440e840c0b0000c21040c0d00243d24203101a00407130060b690107142d5289444c003508405c112050b940101c0c8102842c260001d000d82000a90008080d00c51b07104100700e620042c2c0f5000245940d00000904000001c10354000c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 777775341 1250 777774091 777774103
    0x80f0703020f0d03110a08071211071401020703170a02160b0f060111071406070510060620030a120902031b10081b13030503030c030a06090213030b060409050f 70
    0xb0400c162461041c41003400c0d03080340e0b41c600403803104010034005072030420302a16859034002181e08005c42a0720100041400326400039040c00e0140d8004125542445007140030f401d0f1024070007000318640300b56900c01030314409540d031900301948203000000d0081e04440d0190ba80c00164900412001c400500d002902e1510440d6003440041600d00014019072240382a2410102400301a00c0f585080c0800c240340b11811822844d00440304016420004100f0420340d4400180f03840000f03052420503000502d8003030f003036003c021400c0c03001c401040380c603001004603000800c03981001310082c0c401e51252405003008100280d4540184141140b90300c1070050b03a00203e11045a5051100c552100d080c1d4145505490150300500340c0348020000803c1000206a00c180d8440061441c039903a55132285160300440c2e03800900503020050100d820954000c0300094070b14100c05505008840c18a240c244a151101410941c1d44002246003522a03911198400d80c012043e81d4000d1030303051056641d01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 777776591 1250 777775341 777775363
    0x705061306051e06210a08070c0602070807140a0b0c10060605070c050f0d0803070906180501020c01030c050f2709041a091c0c060e0601051c080f070302 67
    0x42c100b82c0050000c501030f80890300320705142e00038856036441d84130030f10440013010810a048040d03d80005980091300704081401342c3c6c802c8001a031303200624a0450114481c40c0d01440c199030003804248440306010400500356600d801e06041c41c4110303100000d0000500b0b5210321010540000c0c3c100c3c01e02c03804205511607603408a010700405035952402c50b01403182c040040d0000400c02d105000a02c0c09401da62504100200700707540881e91519101800c0c0d0080d205500450301290040011740e4000c01c940b020701e260030a900261519144c0003075103039844540800e0415070340c0e111002c503003800f80d0305a8400c052103807072250319070605000303a80c01044403810f48024a8008000084940781034a01d141c40307144c0c00450f81c074480c50780642004203044080c241c1d0055000740504900404040e501c8542c02c0da100d0b0362101d401c201d5509000003142c8490000454542000005000f81e13118051421494600e0000c40792071804076041806d5280038460700c2c0003800d0700000e500c2c07082c50350010f012a030312 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 777777841 1250 777776591 777776603
    0x160c050406320d0b04021305070c050120220819050c040e0c0d060b0405040f020153090c1503010609090e012a0f0207141507050613 58
    0x341208051880b580c004010707040e503c10b1552001200080701e03810001c2d041407028040004140100902405880d0b0403103640b000134038901031003002c0c001c00f40180c84d80421940c0800c0300420159000c2c00041c80394901041401d4449064881e507075000c0311540d40140f603201e05444c0e43e07040c0d44072020035250701c00c00d050b6280c0c49040a4400079140500c1003050207508100200f0156280c1818044c1c08000d40a05441d115a20560b241064484c1e0052922461203060000c82c09481c900c00503008013903090360b00b040c5102501c02074040758180e481c20702c180d4103001241c0e80e091902c507014540c0087c82c0130041c0a8a403100d0706201c480040003c40440d0210b0840d0100365502050310180c00300d020901c103c7c0001040468100701080703503075004a524041c000004a10000c1484a0441e44100401d103880b01c81100c03c5483c0c1860341c05803615030480c1c030500c013500c0d07041d24000344120600000c41d415489150b100b003440021035040130850b80004e9000301922114070380140182c14002500c0c1c030546071 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 777779091 1250 777777841 777777899
    0x5210d0b0a0b04030314131203080c0a0903140c151803120f0f0d180203100b0315090a05060f060f0d02030a03080417070803061009030305160c050406 66
    0x6103410080d91041e9070b081400c89043c81e00d181c0701240c2c3d600c0c2c1d0030341c4103030012030811a40a000d010403040602810051b032140035221010725008028400041c005285004240301d4000603d9003c1d46c800c007120307044000c140b880c0500465580c2007000b0790040951000321603449035882c040c07a00150a43d41d044441040703800d0340c05000d050301c0d0000c2003402507070440c0c00c1102034080b1920902610a00d482541c80c2404d100c034002d01c070303000c0300c8034151454800c40c8455200021460200040664011207020070311060003c0e5020950b00e05039003a502060241c460002403168804101d40382c5816080001c490060408880d00c0a00e83d000303035200c0c0d004030708582d0300966504040c801c20031015070160003841201070b01d44007129403400c013400886107400845002c000481d0614081c00a203030080b40081d9803404c00d44100070451801e1a00c48040c000c0c3c94070304001003074000382660920f811203194035046d4062440c10405420b015000941d206141c00b40200d40c2a86a0801d00081d80e804603111807 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 777780341 1250 777779091 777779111
    0x30c0f150702030304080d05090c1e031605030a0b04080c1c080f1006050c072309011d01031b050301050c070302060a110a0c032c0a0f0e0f0405210d 65
    0x43c4900c411200501441002c01401495503200e900a55006581000703403001281c031040050000102040a4152500c00f8005800289410701981c10b8403071304030500c1c2c40114a403a0200380c6503640c411002d082c4c003005500180a1006120440e08440100b00648580b2400480804c00c0a1107072000880080d0f4400006043e16004100c2d0602500d41c0c1140351400d14a003080031207556010701913601e03c40c01507030303c00070341c0c0028000c90003171207481407210711201d100079800d00c40c035848168041c042c6012540d03607210012160314a05815070745c001d15045629504030001c420341c2c40156100d04d07015031130082001241200c02c00a040d0b05882682075956075103c01e01075000b0f4032585001d1009000c0c08100399122a030084482c0f01d003848c4607041403020500384942102605d11071001a403a5100740040c1c803401860f03d003080c2d4003e002200440c40040c0d00b0000c40171241c20005022003400420000858140001017010382c0c01030071a600b244000d4180041c08420300c0e000050124041414042444 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 777781591 1250 777780341 777780343
    0x804230102030301090905210912010612030e120304150f0f0915210e010e0f1f02040b190f0306141905090a14070e01120905030c0f150702 61
    0x40142001640214296400c00e040d03e4002e0041003011074a42c4522055854101a110044000e180144e141261074a44900030b018092580d600b0008507a403510b0001d0041d90309545a0780035040d0503240074204c1030707103800101c2d0b051000344a001441e480041400034403503070552000e45118032242c0c0c079410031441c0404c0a0390400082160f10001c20076405090117003800ba4841d0f04d4000541e0f02e454503841c03c0070b4035541300040d0081042640c942c0c0318222110768800034000d0980c40d40c900382c0108005c24030f18809548440e01d1700f14800c0e000010003558403841d421303074060341c0240101c0701441d56145019650541c4000030070444002094034814061607840c042d00c81c16041f01c0360410720440f40040a010805161441c150039400440744200200311601c1c3ca2000034800c030806880091100100f003030030140003900a20003001c0003644080400340340da2026250314602c00000000c1000c848625000303056000350311003202c50f4401c180400811034070000380910341c922100c041f032080e40c40c1d0803812 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 777782841 1250 777781591 777781649
    0x90b0a030b0a09060f09050a05210a0c1b060503150402180402030405071a0a0210020a140d0f02160b090106060e060c070f030b090f1b0411070606030804 67
    0x540380111a10000d48485030b80d80181c8101481400005804004849100129044654162903a6009051910403c00300700404070200107a6808605000182e0345191528442c04040b1001c01c80118500e4040003c0316802c0c04041d144002c001c007030103894440060070303034000701c80106101c9500c05003510b00c1c2c00e20703200700ca00b042c2c1120350340c43c11149001d0a000203584050021030f40791240340340014910801100c3c44c244100c0131001955200000d00c0b0007803904404580e42c08540c1d1041103104840c1350400505102e0700d40c20100540c44401000c2c0140007410000c21112907130303000040c4109204030304c000d614000c030b10402c841e07011a140c03901505d080714164001d503c040b0305000e01c108041d00e130000182500b0190f050480da00c040e1200c106030014849a80222402030040b0140f044624060000140800c10b03d4000e041803c1310303001c0e0046810840130070314021541c03400c200c0c1d240e10800c0110b40403280c10207005e01809680e860442070641c0148106a080400310103c0d01c4040d1012101d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 777784091 1250 777782841 777782843
    0x30304350c0411070c0b1905030709030b0403020a050607051c0501150e0a03060627050910150519030b0f040b010302060f091008100602030703020703080c0102040f03050601090b0a03 80
    0x80201959a10a010040c0f461002491481c58244450000525007070151009005403401c00c94032682016821260341840840000034050140b0400c81c074a6440001c2404a9800c0803100080c1d89075414141d050081c8100054200d026078410409000e030171100500440541e28540701c11211244031280440d90300b0b000e1100a88060300346480322038481c00b5490b900306d40003080404416a80e0303448504940740342c1e002110401e074001c10361041c0c62a400800302801310740c1505014904d05000540d132a442001d00d07401090fa030320041c0384aa10400c500120180a01420740c0c039204900800301103100c0d0182c4001c9404017400300020780c03141d081c0c00100f800345600404088459003180c0c200507554001e04505140c1038000c0c00000025980da1400b004004516110380903c5d0402811316201402681c02c0b680545d4410020b4500003603000460303004503900901069183e4010008503806441140e1101190b600080070200030b2000100380076042310041981003200e0258401032296104041c80 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 777785341 1250 777784091 777784093
    0x1406060d03080a09080415021b0d02090601080a0204050a061e0201111c0908041d060f3015090c010e0604050d03021005011509171e070503030435 64
    0x4085038143c84150400701d112807042d2900c81c149502c0300a4440d080004500c0c040041e80000b071039041484003800140c880890548e040400c5044540114036058006408103041040307410000340041c040d40c0c1031760040d010081080c444150341da0380c020240440492419102000c6022441950f8014891101a503d0000400d414080c00503603844130a40c400590720401c035103c0088000256840c00100050700b0f686c1d41c44000c0c01070b441944110000d00416080c0504140b454041056a40d07034200350b804e80a0036413006079403d40c016500a00d074207900200c4184c1c0b040d9014040600d201101d114071946044003150408a04200112004d0350305060194015408000a204a007011a02c1800c1a4041d0040701c0c580328400c0310440032158260301901c11841e41001901d601d07a03008680ca00201102400e0500304001080e1942c1c032000c03600c81086801c60080011300d01582c0510038000107000040580391210381e80c5010011030f07035034407803c14a0b19403800400003418004038130003880703a21828 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 777786591 1250 777785341 777785357
    0x60e0607081c0906150e06040b030a020612040203060f070801090507031d03190315120309032015120c130504150e1e040308130602071406060d03 64
    0x4140225580500000d444041c401c01200007030301403401440d410302c40024000166402c06040c51000c541700302001c0c18500c0c0e01a41d003005031800802d08150018400c50780040d59010f02000203180900c680b100035000500458481103290b481c180d0544228000d40980c0e500c0c0e030b14010b821041e5a400c0720b540001c5000b050050082d000a035200c1075200055040001d680600208480000e0128107000022a400092001c540901d2031102c0c520801241c102440022101d1052000040351800b503030440c2d4803c0709480051510a000783c0f4021900445c03441041000700c10f00d0000ca0f55811035181c003450f040a2801c0310b00136001c1c22940160310810f81d50055480c7c5005140950f44030742d031050910003500201041d15642d502c0740014040041441c941200e180c6101c03c1c0390204014533200a8010841d41102c0702603c1e200840c0d805039140c40c0c205a5030f0741e502c140640080c18920040c291394408600c10341004640c03a4051110002c1d1021907a00381d03100010030100d00c058200050000e0140d07 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 777787841 1250 777786591 777786617
    0x80313050319030507060b03190309090b0a051c122d120515060d090b011a040e0a021204050a06111611120f1b0105120402090a0902030d0320030106 65
    0x41c10203040c184d441b43c40c0104410300010006468810301800c110042500d101d00c0320b0400da04051070300018900171f05c0c00d11054884e00005040002030303219131030055a00843e449003c481c0c854646c00e0301e550200d0448000100004010003815045031000c0304e40300c10072883d40d0200c2c00003c803400e0000240e40e0f03000d0700c20704200000d0701900b40a88800c5000c0c060408040d484d640d1400035149032030865500007202c0c00c0c41d0801c0320f11241c041c2d100009001003851071555400c116400c503010340c5c198864205c00c0b0349031021400c0007441341301c41d0070315559440310610042280120b10220558007944051000741d2882148134410b210314104124514000c20b50000005d4000844d5204009c0080c040b03503a21030b03d038280e6070a1520042d42d1a0740f54003c1880702922402c03416900782015001e1a005042055904103d44880d002420192080402400180424010f90080c0c0400f503070203020f90315000030210000e8060545035180c1c0c1030003410005003591520600061743d040b11b8060755242880a90 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 777789091 1250 777787841 777787847
    0x91a0a05090d050d0f1e0f05070c05060304150b011403061c02030a0602090a062c0d050706050c100b030303041106070b100f08030703090905071101050108031305031903 74
    0x1481d40650403142e001006404110180b081000000e050346600113182c01d444402000000c1c211001d500c040d100703400b08005207a001c21510b58403402c0342000c95840106090403038148591f40d0016510070800000c00003082004042c021800043e8141409000c013000c0042d200101054010104601c040c4001805031510480500141c40241d100c840c8445450b00402d00301003d4290070380780180c00099100850611580400042546e4640360101c80b91802042101c1e0000300d811051440a0300740c14001c82d03031070703e1880303001c15440003c0754500d0b542c40d040602542c0104080a02c1030044004145c881740d03050282d2140380c1d0004014502d141d481c2c0e40c40038012003180c00c629070040003e200b07401c00520b039401c80d503024a85030b8a007859418600203451b0504e01a5030000c84242e04107021301d8000a4100c1111002d6610301d803000f046d140c0e42e1a8007100ea00d1040203072448550300f0310000003a0b0300d0000c8010103603c851070f015105400d40380c0092544e113001c1c411010b0311400c000381841003c00d01c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 777790341 1250 777789091 777789097
    0x110601060f1e0e0f040f1121150d0326040b090708150403031509020909011508070c051c081b130902070201050415020d080f2a190906091a0a05 63
    0x14008000040449030118008102d61562108641d41c010000700d060404c5500c043d023008081d5075549099480c40e00b030341c0312000d4000303595140e40140e90950035101010702890410700803001c5540c0d4000603200d002d5a00045010642e0140e0b8907211450108614490120ba114280c030318080040c00051080960340c0d0085000400075820191b0360f00c8548905040f201c2c1d001c004100e826805a26010b1640030400d9180e4180c0c081f01c4040e01c58020102c0160f08201c0c0389034800480c1c208109603c080c1c2c1092414082c8501d02402e13845800240742069a07005103c150087c090b400c3e06071030201c2c400341000c4180c4582912800c5600004408001e00c0c00c068000706010703881858564241544c0340485082c50f68541e4002d809a044040c1e0214811b612041c0140d1041100641d880d66051560100748103c801801721590306003495000c0035600c204408491141c0f480110030003000c000c20300014641080d030b000da40001034080c180002d500131030200e094600c80d0301c1d008142c508078074010b081c0e9540d8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 777791591 1250 777790341 777790369
    0x40302010c1107081e0c03060108031306030501180b01020c090a091a010602031e07050d03141005102a03170a0e12031801090309170f10090201110601060f1e0e 70
    0x2201b41803207190180c42c1800702c10b000b061698020b588602d00e044140044c824603400070001c25141800412107030003480c0315070306900302c00e410002c0c48200b45030040382890b4a85070700b645c000484c1403c2c440c43c400d00d03031b0100b0095806800c07403a80522410000b0a203080080c420240160f2091090100c40c1d049a0301d502490035800d2881840c100c1144d40c1d2a042103402041c06011a0303a451541452100c4450029844012070000d05d00560400c40026025000495144100f1190a86400142c80e4144980160380b54010307450f10046464a4024500850040828025840d52001c02c04104003402a142c542e0090f40c064510350190460801440e080208480b289240303203540152506c8081c8a0010224020398802003e90304005040080d1610440c9141c4d082d8003d2084c08446080443c202031004041d010204590300302c1e000407030b070441810624001034002d281c00010000d4102c50003084591044e240c041c050f0f07840d01105c4614030030041001d0301064510035100141d18201205100e01c0c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 777792841 1250 777791591 777791593
    0x2030c09060c16121106071205030c040f030b060307150c26030a05060307050f060904050606070203070810050703140721060605030615040807121a040302010c1107081e 74
    0xb40608620f40c2c500894603402521400f02c0062080c0611031208090002a80180c0c0e440b441c00e0b00c10341d02d800050840444640401c0008030102c0d0440c0b000b88101c80080030a80f03442c07514952681421601d103501541d0143c424819440d00140082c0700c040340c900d0b07503041c54031100b80b406040c0d2201401010105031844c0742d40c0c0075420704c51100e00c903400514005c0c0302040b000512440e20506051a0440e96084640724151405400c9800e5581e101101d065a000761004074054890902003511030186480095060103807040201d8041000950010030b2004864203201d5500da9840036421203910481c0030507031842203000903110741e000f0000000c5205520f000f449030586aa1851821900103820100014000206215540c980038400b12513016034954030b580340620349409582d881000384203402006602264020510000c80d284d41588501c041c400262072230289002030003402141d04500200300300c001802d40c0030000141103c1515000c0d0001c00c5840f5244085c5040103404500309041 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 777794091 1250 777792841 777792853
    0xe06030414032116020c0d1b09020f030f0c030103020d02010c020325060e03030a1e05071b061b0803340806090f09060402040216050a14010e0102030c09060c 69
    0x2a4028110128518103410304540c50401c04c0040940d081582031100071584201c0d4040840c5e9580c14450945c03907030000301d10507010f50f4440419070414980e48248501480842c40542c414a500002c40c4210007a480c80d44840d65185041c10090000b0b01002e504043c3d140b0b0701c8001540070300207000c041f80c001011034040e080000102400682424200c0191103d0103c003005965001240209028011406141082c0903032600030941004507500c075400d44804851181c410b8002c20440716081d4021034a070b0096030602405611601c01449000002421240c644010b130407a02d24008000703500101251554803604241c182c10040b25080322454440044038084400304400154120b42d00ca885840316413400c2c2d020000c4203c002040c80031041d0042c41000001000802d2607603001d94110f40050701e400c0001130b81000c4150070380005003984140313001041403162103031100d03807000402c1d03000344807188101120350f00341c0c041680d128030122010700c8444568645080a840b000700b640c41180c003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 777795341 1250 777794091 777794107
    0x1205040305070212010219020321101703120106020a03020d0503060402161a070203071e03122a020c220921030605014107060204150e0603041403 64
    0x44c09502c0600c98075aaa9400640703800000c154112101c00740c0c595002035810000c807411094581c003074030501146801004c0000072607640e82c480484002d0304140940200321518450181d5880c1c0c02000025501034080000268040c4006907a01c4907551550142a02c20552502a40d06800c00b900607684590244946405010b0032816400924060102200140341115100700c2c0808040c06083c21508104141340204460208030302c160f111954541c08810f165040448400111500d40f1700030b80e0420310781b0b4098000340c401204443e01100c0d40039000d0400a0340599541c84400030b41a0001c21401c441c02110500c070940004030201c4140210f0810046d039a126507890035020210140080c2c010b148081540c5480384034054402803d04103400000381d0006654100c0030751f09691705032010040803403030303544680c1c0300826034140d0804a912144e20349400c5019401601a4101e400c2020f2560740b003103480ac81384100308a05c0038003a2845c40d10f0f00e46984c845502d9502c0071a18510081180e44 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 777796591 1250 777795341 777795349
    0xb101205073f09080a08152d040e070611030c0105040c061e0504030b091614090c0f0a05070807050a0308010905070305010506160302010b090a02070302070f0612050403050702 77
    0x5202c11a0320000300c20b842d801c0740c1c00081052500100d80121529004440307001403207031000c495810410303040520341550b540c5c101c55682803070480f030242c01a080749400e00108458000340d0040450b03100c90003041d500d0709028802110b4113001000400d901a10007080240d000b000e49180000b00c0001307583c03420410300046825a0010b0b5411281c41d00144801c0140541c09108900d01c0d88414418480300c400c410700080c41d5010b14003002e0001d80844c004a606210200610700c51803040b0081c2a104d10fa1304c0307640f541c40007290b802140c02001c0f182d000480c030b20f0042c01141ca081c07011510141c208826080110340c260011802100d51400c00c00c4441c0100e0400c228400131188282e9411070558184801d0750180c1d0300141240061505041c0180318a0f5100d00560b2000100e201d16407421030543d0404a016207807001720107412510010502c01c200c44950001d2010074029000c0703030360882e50741c4c03049000d100300b0748560307400114181400040c1d41102e8024030b03002400703403030006d044c064150009 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 777797841 1250 777796591 777796637
    0x303060d142e0e0a060f020c1c030e0c090c0313150b0f03060402010905040b06040b03090c0a06020a031704060f150810021c020706180807020102010b10120507 70
    0x4100c0000402116055803503042801000c1d00c00d07041030a004004208a03c16552201498000d0241d42c0721a0780c1070100319164180c50810000f8001c6402251a02c04c010800201440c0d46c000000d040c50320406420000090a04050300058135100c00c0356034080c0c000c1c08031303040034000c252801d1442c02080b01143c4503401c420310641d801031002070a0202c43c400c000e64890201906402904030700d0070440544e8021300030f00100c40050f0f40116010b502100042c505100c1c07908031084184000c0b00784143c01600242c1084c03820800d9515002c855107400c000da0307481464503c0200040d001d611040750b41c440001e6502d41040c03051300d020940c0b803001d070102020740754213070905102508640420001c80030200440303618040340034411890b1900c1c0e204444078880c9440810103045130005000c000708401540215030300381090001b50710105030343c5404d19090740b140c24242d00642c204454032f2400d00d1704040c004244080c648035000103a00340c2c00c0400140900500407802c0c0059a005810405003103009 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 777799091 1250 777797841 777797863
    0x1151409090a02060d1e06231504182a0f0c020d0b040501141501260f04060b090105061902010902151201090501030804172a01020d020109050303060d14 67
    0x110b03503a011031803100210b8440c02c001b8006a0b003440003c0095880b40c0c0c407000c0c5118805403d070911004400040f410018420076074a017000e40018000a0154036a80b03550b031038200c0c2540522003030b04c00d0100c0d0904543c001c03c045103641c50f210417540303607540111070007884e8070b00701d051500c484581900014481c0700e00020070741f0003080e00030410081103006e200c0c01d000ca440503203001e440c074200301c88201d50182c03c144045050002c10003a0402d508102d60f02040740719144408030b80280f40102030081c034100c003a82c0c00c9842d10300708152141300d0701d41074540a0590b43e001d8a0341d4100f03100340c0d806884401c2c49030500000d40d540c614121015840700e0ba50310841160289501d55200003022090031000c805074410705d801f0b441e040061001481e00b00c00ca404a42080403000d600d03c1c07510003101e04084c1860f0701c41501c1d5248070f015521101d00e202c04070200050980903200416424070040e802c2c1c03141040002d006400800000300b00b86001919400038902801d03882c403080d800d400c201480e05c0c5e040c0380c03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 777800341 1250 777799091 777799117
    0x4051c06060f0e1f0e0105010e0d05010507110d0509060304060b04020702120c100e0906040c05040f060e010e1c060c120e01020301050a0f06020307082503080901151409090a0206 78
    0x200301300040c0c080101542d00c0b643c0080c80160400d15102000ba0301c400107004403070412070b00203d0790f0329641d928111a81c1b030b00c0d04000200a982021000604482d40c0c484600d40c42c1d0003003c4032810803a00900540750f40c1c0718064102e91655071941e80d040b00403d4a21351044d40b0581c00c1c80100c002d0b8070f8604401050a074002e008094031440e600c10024504e0810f000f0101301302c0035107248003540d140d4800e0107400c481c040e81d01241032001e50500750317190b000b95080707550200940030703001489960000711200469001e03201c42445212005c00d0201e00300542c006011806548007860b00010110f80c80301c2c01c9416203140c14840040b031105654107841c40d00b000d070305031690040300610141ca0040e05200042401c01014016249003001c00ba48a000d81400503058410100300c45400c1c0d1143c0d540002c0003120040901c01c040380d11700c0e019020400c00c2e030703800102c2d41c030f82004c1d404411014a000420b5420fa884604103d2410b4400c014100308004c004c0400c500402d005080140c680b000500a0383c61850 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 777801591 1250 777800341 777800369
    0x110907030e0604030815040603080403060504052143111c02030705010f0816030615050d0531061d060906090a1101200d020d02011104051c06060f 64
    0x5070b00140c00c400703001b0a118503d08002000055904400c84003102d03448000851540e0312400d11504264440006120b02d0328a110124650017600b002030400c41d0701b4491195004c9410061143c0da00d000416a82ca105044c0e80c401103a0700c800361141690521580d1600007050462010405610341c1c0c075074503185216040c2c1c200f4114507003444000003604013071901948020054000402500340a80600c0d0401016031641e0351482c82900004041d1640106030490803c800d54018600e510030343c1290802031418010514000d81400b114403825101601c004176002044040009550105402c4420b5503036088a900d8180982e100380561246010240a03d481d21501c4503040580c002c109140c140c011410071030000c0c0192840700211034081c6001c400e0f40c1014504070160100e04a003001c150320810f2100c9240d00d40c006280c00240400750f0007071041c0c00b05d00c500b104084c00342c0c0c018103502c020907440300d4051280c50b00948448a00800011038032940d0f48203001805030840c1c12075040780e5480 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 777802841 1250 777801591 777801601
    0x106080c1503070207061206080312090c1210020d15080a17033102031b0103060b03010e180307170a03060e1b0a0e210d0507110907030e06040308 64
    0x1400003401d50296851049156140c070b00d0000703403030f08401e00032041400201d458919800280b81d1040e0301911400003140d54071710b1803030036105130312800315441696485015440c00f818100541d050844034101d03402022103503401e8080c40081d4012826a1044650340e42c038107981100d1503007406000308280d1026000891040c1800c0c10340740c07501a8803002640382002801002076400c3d41e810514039140c0800c0c00100f079940c103041803400e03407000080d40c184140f5404202e9407190014080009209813002c000a95450719141d405000074807406240503014400188407241c281c1414410407214402d4924204030b603525400601c221070510f00850902160003030b1241d816115a0b409415140003665035890040255090010381110306010400042403c614042c01070614903945d540003403400041c00000b050410f8403c0044090f5035043c4101d00c40300301c1d01801101219111900401c5050402d800f02c4140b01105002030440010950703104403d60614406000c2030f40290701c240d50313400d0301c1e09003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 777804091 1250 777802841 777802849
    0x1060b0702040e160324021c15060206040602070c0f06031a06071101140d0e060405010605040b090f091905010515041802010c0809061605060c09300106080c 69
    0x40640c0c0f0941070b902c0022005015010604020304886d402440038140c4144685032640e002c1031032003045503041c000300302500400d20482c0c070940f103c44208010449041c2c4580b4081d000c00701c80c45041c025030043c601140226210341c00403c1c405000310085c2841665a01c040c1e88000745075409680000e507242007200c86d005414040110000080310082c1c149480c5072078840d1044089001d06060000140c08104800c2d40030040e0303580421103072001c000d1120452480741c0c840c42c089a044456518098001c82c031840c10344a40240000050030302209a03842a160b029200005042001203200d0095070403100b103081000206a07038410740002c036841c10308115800014001900083c8100d040903101c0e6039168011600440c095024a0032900c25109401c04411510401a040d50480c0001038030410554400f202c0d10b000b14480d108070380899032a0040040d260007000117150703100502c01890041d82480ca41c850014019908860b500c65000e0b0080341e0031111140e01134082030300004125811490 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 777805341 1250 777804091 777804101
    0x603090a0c0806150d063804150b070303090b070507020915010f030c030b03071e09020c030315010216060e010e0105040f0e1f0906030b0606070c0303030e0c0301060b070204 76
    0x62020002c1103281444483c1c078804805052180b40610b21001c03084090040d960005041c0300c40c40787c43c0c03d54420851000710b4545040d1103200002001010800645007001e01c19010541036180c0c0c00c0c000d403400c2040fa1074007a17224480540800d52910030300300205040061041c0998a07640f2883c0c2d80b1400c074810320502e00002020320740c045d40c42d0400c0c00c819176000880b0248004181c50009503070112004240c00425100c0031a0b034141c4516440841c0e00d92000380c80d240e401c107007080158101c503a2150008141c2c071840f0101d1072070760410f0010803000c81d0b0711f841202e43e0341014010b82e005070402c24045040783c45a07074402c00019070600180c0c01d9950300040d12501e012400c0c0b070418506424a102d04803d05414440c403040c441ca0b140c0002d034101d458100c4280036524001404004076901c0e450040a040640800d0360364107071020210f01c4500c1c3c01d01c2151440d42d070101c2d80d402c4082c91514158000d1440d00c0c20006103005811aa02d06c99500b03210b4003002c0d1500000c2e2a40300c1245006000c1195 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 777806591 1250 777805341 777805349
    0x70c1517070c0f0311010905120d140c0a0810030623070f02150c0403080c0304050102010b010c05060a050403090b2a0a030c110d080f0319020a0516110603090a0c 71
    0x2c1a40d8440601140c0c0140b461025190582803441d61066520710075801801d2504003d40b160042408060f000003861000707045000424400b0301059480390302c4c0d1400400181c640d981c8445041210845584c0503400c1c1e5079000c0040344141e030443d544c0c0e441c0d2030192110454004091411400d2601032004880070b2241c20500c80d00d00403070665060080655280180f0000400304070314040050242d61004040340d02031607110001d2501c034902050030b240e90b0342150258501650900c81d0b0307450254800ca0904480a40000c020007040d1202c4040400402010f0b00c103500300a42c01d00d0202d0503001a000502000c03608050144000c0300180f407403540d6010044100300380e5000140c0300c00c0481c2e4810000c00350150000099003480040c0d00004286c048540d100410540c00400c0ca00d081c4800d5102452107900346082040d08540c000381404101d215071855840420824018500c140d0b4209096502803031140700403084407041c880004e0900d41003210100141c3c1c0c05082d20000700115025000014 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 777807841 1250 777806591 777806597
    0x10f060308071704320d030203181c03080a0b06130603140c120c0d1a0102060f10170a0212010213092903012406110c03070506070c151707 61
    0x2040c20306040508074803d02c113168016600140c03012100305c3c83c1c10720441e20300c2d1004002d00c1030025a0310b8082e440307401c142400e83c054032500101c600b150400c120102411401c042c102103500c203003590150781448000d081c49200c16501c140700c1040303448000c0200002d0010174a21420f0b0b07483e000005082d50000d0300084128800242403000c40c4e01c044040d079991600c007050002407595030301c1c403242190283c400340160841c140580c9a050070b0701000f0390790280000703900f5140f250b51820304185200e4800d580005000c100300004004690344a00d5458072110000180c0d218513070150001860b92034811034504080c2d500040404007511fa0151040c003c040341e0406010156081d54000d06210020520311320030720000340038000c0c5e690203520032541c0da240d90300c083e040c0384899010345091510354003130940420700d40445240d40913400502c007000321200030010152142014203020964100020407918400e801101180c1c40d0303550f40502031010368640d11110240c0300d410045002d500c001d0201d800f4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 777809091 1250 777807841 777807847
    0x7051818180f1908120f071e0f030b180c090906010c260d1805010b180412090810090302100506030c0d0c0b160204050105010212070b09010f0603080717 67
    0x301c800109040519409011440100f80b4072420000e00303d102d0900300100d2100e0b4101004103415035034508a000c0c0c00e0f06d50b00e00a019110069986c00000305800b0040841c580944e42c3c240d07507109802800a60700054034840c0100415010b80324a070307205031004038074080007003180c0b40941440003480f81d000a0900e041c41d5500310360388440581c02e140c080c1c503120541c40c0b40400940340d007040003120b50009070440700b080b043ca090040f031000c940ca01d44085845500301000c034000d0b481c00210055071130081c610f0542d804d80311940d40c101420101c0101c0d00c14003200e4040000e803410140305031402d80500c3e0303a0101d50140f4500d4000e007009134008141c070700e16250a05004a5840c005030450207910281c442d4046641c0c0350410b42c0300042c09500105410000180c80d2801503038180b4041c0007284251010301469807103200580e1558010718012860758014031809011600c54a0415040314044d400003c0e001803186504050300c503990030036180b035000000e917130382040300c40344000d444402c00e0028182 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 777810341 1250 777809091 777809113
    0x106211d19052404030f02010612030c020310050108030a20030307020706080c210702010f020d14090307110d032303010315050c04090903020c041814010507080705181818 75
    0x21440010b80301a0805c1b03a00c4186205490003580440060000c0e980c00801e5800c2c07501c0d008001c4950300300104e020340600c000040d41a0b03541e0082c14180d6031460051342c1031040c2140100c0b03060700e440704076001c60b18812004890b148401d000442c001da400743e01503c1d8540c100000500303048000340c00702c00ca1345004c1110034191104400100b20004409081420a0312042e00c06c0b030240817158080840e60740f000880d44801c1803d60f00c80906c1d01c000711080070312a0340b400c03c55916030203030b400c0117050041c4d04103048606140c0130001c03241c0c0b00e1180c10003091f031b00c2180345200140c10a0580750042d04800200500901507116003521700c03902c0e0444203000500e84101d0245050140f40305203500c85480d03102407810540240020303503808102810070007180d00d442c204a900c035005a90203070f41c0d80300d0b401c1038031603120b00c18011030784100c845440390000d5845492040f80e081d070141900f03808007012940c1220080d81e40004010050343c02c000c0303c0d2080e0818401d4840f440003412820780c4075500c2020b04e92 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 777811591 1250 777810341 777810403
    0x40e0117061f060807020c091008160e07030b13090b041e0f020105090a0324140c0f0f040810050a18050a06050a1b02010e060106211d1905 61
    0x1019120546040440c9403200e17101039240481c06031841e9401200e180400c594428081d03414000c41c1c90840881d242c1201c82207070740918203080c1c000d44000b00380c0180012040c40c000d420503002c0e04809019050240c10300910030040f59502c440c01c80d08400d100b030500007800710349100000c0b191050f80710b50701880392654802d11407a4459900a0500c8000704600140e551980128030003503422801ca541742c1070302c0d1459001d24001d174900441080389401d485050300d5030140300e05445070207400d00305480d00c1c1b26081c45222580200020340400310781080301042e6144140003820059820100124203030500c00c081c40d0030ba51440550060552010606502081c40001e284800f103400000c00142d03905c3c1c040d4000040d045d480d86c8080b181e0f0140150b210700f560305500c508007980c0000240c0389181d883c1d6004840b900c0f030483c40c600d02e075407032151005900582c1c2d074000001c00345031040782d000e41d44040b002a030034440c0014031401800ca080e03030301d501440070a11509440400010740603400a055450070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 777812841 1250 777811591 777811651
    0x80901051e060405060112060e060a1203080a020708041701020a0306080c0a050112020909070206040302070602031821100b0f030d0c0f0302010b09101d061014040e011706 75
    0x18451030303e5a0200e0540e0740640702003e642603407c00c050280310b46a102a00d00c854090358414000c060000c80051000015614424900e9240e581e420860b200c0d1520071002e908082000c0d6022841004009920072006520314484c04401c000561a458941009400c0f00c200b5070122119030880381007030440d6503403e43ea2905841c403d003010b183c04d031504a0b446d0000c0c010303e50000e41244c1d0304400c1c4003c468001030494840d0303101c1d9084401581e201c0008a8490091062060104d21a2402c840c940c1c135040110003c10440313400f000001c48022000350303203440e22610850b010a170799641c0310b080604020201d24101d00d4290010088860340341c07001001079103207040240030300c00200718103800c26100707410005401c28020b00c495100c2c1029020500408041c0c480d12a69144404400c841c00c0700014000303209110080c041805042c3d608001d031074002d00b21000712250a400c0101044681885a80b140a00510b900d080380540407030140c5440d1050292036501ca42c180300300c0c41c0604180300000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 777814091 1250 777812841 777812851
    0x140108100c05091c0c14091f03080309031c060f06110d030b0a0b0a03020307030e0a03200c0301050c0a170c0f0f0c0d020109060b18010b160c0303080901051e 69
    0x720b40b0500700702c40d081044d8a09401c2d0014408010100c001810062000d09420b05540c12180501d1a803a4642c42d804803032a000222203000002d00410008119203401070f41d80158a0001c0d2441d001c1001681010032007204440040195290400c3c0903a103031250892014001314200640300c01400c0c1d4150781d076401c01a00940030151520459045520b84240700170003801c030340c140b59031a000d81c004007401030340048a00740b0000e0302d014101c100e158000940403003050b0b0152242040d40844003014440c61000c8042c000e464441e5a4004045071000d1040300e102d60204610261030708590200103001d409011004c451080c2c2c4801405480c5c9100c1c02124102451a40400e90b00c0c407840c204088a402148800b203c20f0142001c04048113406400042001340300709400c00c6401c00d21810049140f001020110030300e070003c001440501070b400c0c001d01c1c800d0f482115180c1890029640e21815200580084000901000c00c2c000c1c1690b00340203040d005070b110404559003002401114092440042c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 777815341 1250 777814091 777814099
    0x70614090d091a1c02040b031003031403150d030513061101110408100c0c060507031a1c02091005060c0304090606080c09061309050c041719020919140108100c0509 72
    0x4150384121255049074000e21f0303030940d2151285498851180ca1062500c000d602180c07032240350f00b4440d031508049034440e61000075840c161100c1030007400003000035a54101c080c800b0400010310310b5840c890005006083d15507400128142000c0030758291a00b0407000b110030003040c0414025041c02040030010403100e01d90000f02c404185204855107000c00d0401f17025245404240001c059054002442d44e40c02c2c2190003d103a00310400340004040742c80201c60025500413102070042c9030840e40240c110051004c1d061891780c42d42c00041090340038100141c0c051380000340801c56000c007030181d60018412400c0a054916021038003003803d01c6030b05d0700316100d1400002e04042100d08850244040c21107032000304043e1030306080e0300400d0750103070107803081300502080880e1844400144401d001405060f801192480707550a000c120403000c0c0041d120007a5200300002c4094461055849900040e43c500c4440e500d8071030001e05181c0c02004001c2e0141c107010041d035100d40c02c44200c0e24400004d403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 777816591 1250 777815341 777815377
    0x6030b1303051e07200105030a1a0a1e080c01020304062d03060602070905012105191101030b0303090901180e030c1c1b0305070614090d091a 62
    0x71804464078455542c0b08041c4141d000380c152402190b00c1c020f0000648103182c015100345110b040201400f540803015400101c003080080d9811504d40c004115040350050201802d00104c1300041d44c891440c2c0012001a4141c021001c005c2d004c20011b40061101d170020f44655010600000d4607072255004030424408109240b400b0701c0139104202154401c0c01b621142c004030f80d0750004010300700500c074510062040100101e821555440f40b14101c1e0801903900f0141c014008c100020078500c0c00c030946d0b807401120300842e01040d80c82070500c08503200368a041c8401c403440f03001400322440090035902a600070700c0700d50359548038901c0580c10f55501141000b60343e09920242c401030b1410704844121400041544503200d00300248001e00360403060f080035146603240c0012036001c1c0f200e610703070481342ca001044000480e000d440207200c00d501900c400701c0c08403c3d030709003a1180e207412307039220f000350380101c8980790f04550113403d017400381005904040151700c43d8064584280038400c00045403041c4c0f1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 777817841 1250 777816591 777816593
    0x13020607140708012414030111161a041211120409090506161b03030b041a10140a081003050d0503100618030b180105090c031006030b13 60
    0x580162285550310280052145101c40c41007500c98503640300b081c034158209881c3c103010b041c8408140142d562070356601517003545821301c0026150707003803110039400d5581c5507800544c41052070002c0481580015130071008101912340400c0903983d904002c40342917001d8040c00300140d03500303241203a18a4545031020955000354107040c01c14050021240d45018009030010341040c154011405403802002503e00b030b9681c09400450180014404200180604150880507035190180b110124003a02d80010300c205010046011540d4031148031440c046d440346a480d40d80b82428444510b62044d180816001d65003108800b45401002c040c0010b100307824001402018900000500440e000012550394249210000c0d1140e8010350b4100e0324000b1045012407224000d200b846140a510361600100764519154440e4902000e007101c040c01307070241c1081e1105002401150301801504015000c1c140c05201018502410014040101030515104001086002011542c003d440d048101100c03055 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 777819091 1250 777817841 777817849
    0xd0f05030c130806190506030f070b0f0f03100504150f120204140703020c06070905010801181d0601060210050f0a020304021c0c0f06320c07030803040224031302 71
    0xa03c1e0000c8000f403148100f0444401411580d103500ea8003200030401c05600c4a1090584134050584001a584e01ca000104504900d5a00820514440c038912030300303107030304c0070491542640160360b516035400040c1030601481c03505204110661016003410720420303281055146441c40340e0f20400e1555600100300b002036444d10b803c014110984003001c51180d10b0400700c0580203402081180000b44510000201924000c81b0102e0955405840d45400340c2e00e094103055002080480d0304803003a0700c0b1020700700072101655032030050858031805003490350304007078000f03240c404c02e9001840d4243c203040a01c03141102c080c40303d035048007810501513520782d503d0010900108a80c01c00040282000f00a402030000302c40c004410380b01009074100a00369280401c1300c0d10005440d0001c0e0500900442c0d0345902200301b10007003d081c484450f50305001880b03a1031030401611340e00c2642c42d480d001082208615220800110380c0203c0a4000303a0100c0030190007019003c010456414075909803034400c20b5640d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 777820341 1250 777819091 777819127
    0x613020a180f080d111f24030308280b15030109020301060305070c212001061712160c090e01020a08070806030c01051e04170d0f05030c 60
    0x80c0c1d065241180c40d07894101c0800401c1d01e10500049004034030411081c00d01c58000c110344580741400400b080360f000b045151040b1010094803040d03c0da9444803c104a401b4541d60b42d201d01c14101d0360000c41d140d801c014014000082c050034280441904203240c51422000c241e82e0032490503000034000d03000001040031340c8107901301040c0c0d5502c04000000c983c2140e40055060703c0c140d41c0c00780119201d408050b15000c1404800816181843c0080d1b81072107503a440601205685140850600003810000c84410060034600300c1d159440d490140b012a02c107800b0142c164020740f00500180303000460069680c0940c10440f034204410329601c401740000346c45842d01402241c04104501400400b4081c000d60241d888070303003c540084001900c15028910701445138038054050500e50780d16200440f02e55005241d40d1801910b03042c2e0b60040c00c4081000341c030140c0000d811030112075610044252411070940b440c4400c204041e0840e2003825403050075250000000500e10341ca8014a000d8403020507 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 777821591 1250 777820341 777820367
    0x110723030601230904020105160c0521060c19272c040503041a1308010b1903030207050108041e0b180a0804261506100201050613020a 59
    0x101c2918000f041c01d504002c110401c595400705095405440381082c04080c450032980a03000c10018014105000d078041c0181d101c0c20320401d0601043d41c0c88500042890031403000d9403218540e4085c0c1d40b14001c004102054010300d542d0101c0b41004c0030f01400d034081c528285043d01c2005540b012603842c0700c444a4201030f51608008007141080c0d01c84107201284109074110001ca034001ca9091208254030b03003039070b40c001d83d0420702071485c007824004218202c800c1d004a10003258403c00015000007025529500a00f0f480c03800807c00c25401410080210203e4030720000342c20911404200083d000181d01042b12000e003440407440d55141082d200700d0005501480394000c0f0729441c4001c0202c28009184105511501e07a00c5da0005019040c1d5101f004030030007041804208000d11200010b41000814041000303d01c4000000301c00714582041c007144030102c0d00d1800c2a080c84001e1400e41403c001e0901d252000700810326000000031340e040307031401c506010140d0028071071000034403034040c0030061 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 777822841 1250 777821591 777821593
    0x2030108280503042702090a1703070c0801330302040b0109080604111002030f0706090c12030c0209060627010203190206060a0e01030309030b1512010e010b0111072303 74
    0x313950b40c0d00301d04021080e45110003000707280e1110320f102070b22844c0700b0740f00040b4002c0c01e4a51854100901c2050b001c1a0380640c450300d04c4140301d4000003845400d9141c0180c030180700049018400300e10032400100c9185105a035241d00e00c001c058401800d07075075400c1140d40440700801c0302c4c1e416a0040c0c030389401c0ca4000c5030290050904110a1002030b50548160f0390054030386041c0d4094a0000300d0320303400b800e10300301c101600c100003002c08552030380c00100d501e80c01085d600c402642d4882002c640700c3c0030b0200440103d400200380c0801d51a0020700b855010b14162440d925000706641d00325040c46440d041c02381d200c0c2200e10014816442042940c07864a0005500d501c0d180080c0e80c007968440d000c0b2911071140440307c4c40030408000c03159819040b01e81c192100341072a030440e650030210b220000c1445a500005001501ca41e90720ba213103011303001280b00c000240210600142d6400d640400311002e040c42018250045400000500702e021520264954165010324041102034101041030329941 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 777824091 1250 777822841 777822847
    0xc15110f0703090509060d060515040e0a030306060302040e0c071109011d010f1421010f06030b0603070501020d0507030e042a08131101030e0a031d0402030108280503 73
    0x1045104a00500c074650003078030f8a0400507903440800c0004001102c10325000000c07083d5010014801d034010a42080300c481a1300101014107002c501240c40c0e942a030780b660fa00029108052542622812001d003599240640c035090070078640514071310001c0c29840503401f00240b000c00b4081c41031500c5040103002454031b0301950350f68608942c0c007080d00f420074691200410000031090b40151543c02160703020030701042d044101004110240d03c2020381d401814680b022212800d0000784905445030500540c001742403419801c100c0d80510008066a0296026032014131460380c0018240901e114a4035080d603540b016072601711000401007124903000303810400605403402c406208402a102031004100a199482d202120442001d440a50125134075005441c0424000f03110300803084c40605010540503030760034059140410425081d000100d84500714107c1d180c0480150180f924121401e42c11941450280c1740c0310560310351a0f110170401125030044050400d800e0b80c0030306070032200f42c0391 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 777825341 1250 777824091 777824107
    0x516080406090503010218040c121b0f031a0402160803010e1b12010b0901110303160e01090b04140d0b0a02030430030f02131403060a020405010c1511 66
    0x805410500039000401c0109030301140ba802c052003682e0042d00f59000740810100f4610a00c03005000062009042262400e0081004e003602c0c02144140c00c20a501c08050b121402c40050011010f821007000b054182400d40100040804d12403145400880d40140c1d01c0b400b95524402c000c800700b800500d200404030000a91111100b5030902c03603900305106080e0030007a40f090b8080c1d44034204440700c14a02550061091941000182014210605011103200009980c407451504222102450f0011480c070340b840d100d42c00010035440d08401e00300103194900302040320b607890095000d092900c103e0400c0400d0ba1703035200c625007071605405c8207000b41d60b410504c880c0c8021f58812201681c3c0740101c02117000300c070391700d07002618024007002c0440c041c010940b00045000e006042d00f42e95a8075021f03c5031a02a20700d01070540d00405401e1100d80e01208488249410144d000f0310304816148140802c0010740d1300030f984840803590000e807a8450324070b80032074600206031415031140c85020102e1a15 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 777826591 1250 777825341 777825353
    0x3120e0a1805011e030b04060f11030103050c0111011b030905011103070c06180c090504030201090c0f0503060f01060e0d080c0304030c140901031509060b1c0312020310060f0516 78
    0xb0f05940e61510140005044c8601c10101c038400c070b1000901620201d000600421140ea12180141050350804110034001c035086940a4100b038000703840300d41010490349060740e0042c48001400080e20002e024110301800401b207803409100395802410b03110300c121001c010007940142d030303000d1400d26496120704081e20000c084496900701102c83d14178007000c4081034581c08401240e1142d02220309000300c0d0810a498000e02400b9000300e09542d26148590001440c20700844050601040f40d95120751900003054500b44010300b4000182003114014040c0b10f501c600805a00f1000b80c1350403c00090602d490581c83c42850001d03009408085004010030491090840880da450780c1d0603001e2084400810064071028800101301056100d0503524200094002c0684203006220011301c20035280c1c01700e034072000d907648070210321000100d5000070150007510000c0e00034180f1800f1400c40c035001c16400300705c5042e8083d500034007000813030380480e46210f80111694161003007211400359000c0c1c5801 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 777827841 1250 777826591 777826601
    0x5220c0e0a060507020f01122a020c0402070b04020d0c0b0a090f2412091a072025050409051c02011109040209010c050d170c030103120e0a18 62
    0x3280c41032031009400540c0603c00d42c01e41d8a41a0010000002d5400900055407038544407510004055160b4180010181ba9003a004900e41e20544000910220743c0f00c0007424002e42c0d42e0405d20031441805603c0115010f16007069100742c0c1038407800364500309410320f00c86840c403a90061405400000d00003e065600c41001c0044404e035501c0c04200c030b038440e0480000049402107440010340030300441100188551650300c28030150180c0004c0416580c0c5a060080007102c940c010508030349800c2c04400307540301454506e412800d8500364200b0742800c05281d01c0e0003840b200300704480b8280ba03001c92500030100301e0b00c00900c1e005204109030740c02880c11079290000302050311a00403102149161041c018011075100f85030343e46e16545071a64032000c200013504500c2005040000502080001801c20403804150a845891782a0240766024a50410701001041d410031400140b004100080c90480c5208110815040078090540000003041d0300d00015840760306c8210b03100200030100201c540c00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 777829091 1250 777827841 777827867
    0x2e09090203070b0711040f0b15130803030c031501050d1a030d03200706060e010e040c060201180305030612061006020c0d020303070813030b1e0a0507050405220c 71
    0x142c0e030203503540f2502030790070340a030b030002818203c0380d400c09038a246040da0080d90400c00c03680b000102c5410344404105c80c1140c1500380d2407103000c0002d46078940303051048200e00a03c3e03100c008610b14503006a11b06a1404041c0c1842c0314106000d1030051240c0c052003d49102c000040410014000c800c0c61402c00001880a4180603004122002c07100307600c28082c0004050b12110720b0b0000840880349030795290301c940802d43c0c26030f680c0d200100720b80340d203c003480e40240782804640300c050600e030501c01510901507100f0019680751020409000c10444500b24903180c150900503142e075a4000032801e12080303040e402d80e40c1d00401d010098a13030841d00845058072816422205036501c444180646803144c00c0300650306034003e02c00100015030300740003007190309003044019000c0d80c0d43e075840c50005d03041640d02e401d0040b02070400200a4030103040d03096101307038001000e00450504403400f50841c4154060322380180c180b21101c1412030300c02c0c40d41c9203130840241c000f008240e2110400900346071039015 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 777830341 1250 777829091 777829093
    0xc03050a0b0109240207091103010527060103180525080c090112030516051f051905060114070b09060601050301060f031512030804020102060c0705062e09090203 71
    0x781034007194031920018080c3c5450f072040b141c0303243c09001001c02e80c5405116400844c0724000c004540d00320f4502a070341d03211519400300c42c1c680d418442000304031408900d19900c007a0080444500d4405035002454205c20203003000503103205c603054400711580c0c0b1210042c0481c440c2100d150807150a05408010028000e5034251000c1d4450a540b5140c0d44c10656180c3d00034207040060041400c401044442c0c1842030408610304880b02180c0305031900010020b41e069000b43c8014601e031501d072614090700d0000d0a000b000321b407500342d0034039540d2541d014540840c5035844000491036401200300711900310802c01240c1c0c803200146455005074008071a1ba140500030310000c2405540128281e80c10b850050b2070b607a40c00d07407140c901140189000c0218154044d00b901d000140022075010034403503c2d00a9503034104524050002a180c048098040e000c7d901080141502040010540617001000b442c542d201c8210018003a42072018030380360f10507880088500003d800301295214100c180e02c00e40c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 777831591 1250 777830341 777830351
    0x4140609061f0803120c04030203070e24091501030609060e15010504030b0f1e07050304060b0108150402030a0906050112110306361c032009150d0c03050a 68
    0x1024000b0741a40744510483d561042c4610385003090800c4c09030744d100001080c2903051503540d400107445e000079070303004031030117000710050006520109006401c41084003105401400e140b03008110004002481015004c960b041d02400a07842900060001c00301c5103428040c1d02e80b42c10b555100920141e41e01415280c4a4459214950061050710101da420448da007609035911501810043c2d002003601c103109056110b02148481d80c0c0c0310a03801042e0725910395450349003e03d0013404036040040311a05101c0b1031030802050440301ca080b80e480e16402d44001d030300c3c1d8a403614014003074a040708008050500341000803800700380100320301c001c1600031800c40948600f41e03410315881c1d010a55001e4420100114000c0710313088e031054050718214654507020f0303a94801000c81403c0c01c090301c0d0030080d510228900214801d80c5406031100114042407042080110001050036511405124030b000320142c0c0c640e4460064800107644002c540302d9402d00c803c540300c10004009041c00ca480c0461b02d0310305 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 777832841 1250 777831591 777831631
    0x12a1715011d0a231e030c1909090c08010905151006050403110d02030d0806100e06040e090709090503070308130c090b0d1a01030c050910060302030414060906 70
    0x84400422800b02c0507114809160030502d4020340700c01001c003102e80c01c0c1e6241a15103265240d2003107040b90000000c1202c110140c80c08101030070320f0000700c0001d10031241c1c2d14905981e451a10046801c4810b007480c0003406100b54900560862540d40c8042c1c0d80e9440c000c90030301440f1010806005092311144140d69940e2003100c500c42c081103c3c05260001903080c0414400581e0000c035540c240320005129480c1070300c50307138002840e000d03130000000000f031190b109029175401d220064650040c0c990810074601041c3e240442e043d0300451003a0f00c3c10502c030202217100d4060902008019002042d010b101690b80d1303003002da60326480000c045000a280400180314141540c0c1c00d104556401440c10940034540807030000501903209107680d1000c2d41d038802c2400210314030040c0c01c8000706c08803104146d41c55070801c4849030700b05900190094200804204401c07452050a0050382c0117410010b84076100d038200b41141c0c40c48001c4414207441803105028000b070300040c0e210b208000462800c02002c81c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 777834091 1250 777832841 777832877
    0x30115051903021b0303070c14150f04030309020315091b1e031018170316110309090f06030606040209060708091c030c14012a171501 59
    0x40e0502002025121100d080710280b281c1c0080c10a04240340c03000d07045100312441e982c00d40d07000759a04000320f000038200500b0022042d4050035513000c18009083d003841003600d80d22040c540180180382c440e0505002801b014000e50000c604690042c08032130030f40d0064074001d00281019140407415208924403022500e8040c0482d813581e1001a0030b0036910800d01440403800b4006c02191079160282070410021021a882002001d00d80341914040c41c075007505044110030320440b420220517104200704041502d942404403a000a64a42030200760300c80c104180c103601441c546907a00040060030712903000c2c0210a050701444c0c0c2102560855211641080100c0c400d042c038040d0800c600f4070041c00440d5030340015000c40c03500545111403195454130204480c10009404402184940150205104840300311070101c000e5200204074a08103d40b102c0c014080518005411000c2001d11003500c0d8030480340c0352109030022000e0b40702404c0c10802c100020308214040e60004080301520014450 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 777835341 1250 777834091 777834097
    0x50a02060912091201061e090b040908030414010212100e0f0736030f03020d090f0b0313020307030303050115050301031a0705040e010f1404050f1909050f0303011505 73
    0xd4010b04a4030f020445824080714442030010300c1c1880d541e900000807801210f40c0007a00410701d070a03000b034840b4100050001241c00c41d490444c012840c02c20540700141c4d00074116600140c01c210f10003021205600352602a20940c00945840311504050118107004407075160251084201c1d8400165102409400a98821075110000507810a12200408107004107078201000c0b5050304000f00c81004100e5598800941c001c4400b141c4a1107400c1c141903060020010440240c902150030a2070702c1c541081544890040c09807654000002c241d8442ca820065405c0c0c542c040d00303450005981c0c3c100600103210920607242e800b482001d00307540c02c40c860401c49040c0d075030200b40000d658031b0300c0c10749610140d170050207501409010080400c19040079124140200700410980340114105000c0c100c511400c0024035015a0508090050746020314444543c031001a00c5454107054076449000007401c64520064920300a003051285500004001036041c0c82082d51a1100340b814440211000d00c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 777836591 1250 777835341 777835363
    0x30109030e06091c080a030b03160302010305060d0b040501050603070812030f0c1b070f0609060509010324060903110910060516080a020102090a0803190e04090c06050a020609 77
    0x248000d0500d034261520700d000d801109800f401c020130707074088505524440041848140c800e0b000c0440d0307a001e425414003c40500000c180d0180503400071120004820802c14000241819121400143c042e101c1222910215030000320b09420b504060901d58000d10341514068080e0284580125846c14000340307006210005000309407550b85c0d030030300d07800e40720f50041c102d0700d044101001900c00e21440111824100185480501a414688242d40400d1003c540c040c40901401d8607080051030b40140540b00d01140a080210702558078944040c01e100d4061100490141000000f00e000c640c004010026a481040f5940d1084080420011032087c222845410100307034403414402184540080c01e01103081d420075000c58191f940d104021a0480a18903005070360128000c1c001d032034020046c2d801080d150340038510300661503113048004110010164248450781380e007000d07542c84036800781b9150750f0440d10b200070382d546520b4010240d600002c03500e0018403424010a20700d0001207800c06100d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 777837841 1250 777836591 777836597
    0xc0312111614120301090b031516030b03011b081503071a07050109030c05060a090507060c110411090a0b0a0206040f0813080607030c020c06070809270406050603010903 74
    0x29480e807680115042a5001211240604841100402c0c0c082002440005001e821030751298103140100c4211601e800800c1e00c43d50040d0100e044044203143d45541102d802119982c2041e901070099021f0f142d502c41c002c0d0190303e000351403400d04065455140f00e0803429a1805600d441e0000e1400c044600b0b9205030b030f8903400440341002081c80010004041c2d0b85100d031464105582611403a0271102c1d050001d8022a2480c0ca01c4002c102051000740da00a401030070070480e408d4981c8440383da8070903c1c0640380c2408003802c0f4101c00d11540c3c3c02d01602940c0000c02c1400b01c144d45825041c120f8101c1d00e40d441c000c040300080480d420000c14180c500000c0c0a41c000d015669660701c560b10440c00d180c4c002e84030541704014540b80e6414440030980a13000f840028102c60508500090450b2040b1200c43c0c2150420000f8101c1035584004540c40a600b2550706034480b41c0c041f001803c148003e1901481c048050f40b0400004500c001c17100d4811400f42c0b008000a43d26a810315098a20383e800c01000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 777839091 1250 777837841 777837847
    0x2010606090b1923090f0415032316090c0512061005040306020309211e0c01060e07081e0106020a0b1b07050109120306032102120403030c031211 64
    0x3031041c03018440c83c80155618000310911a08030075807a415400c24031201d150394000070b83c92140c0c14030703180317a445000003918200b0400c4001c00c90b100c1440c0d02d501000b0280d040c003560b000c03c0810101ca1000704002c00d402a28429084852080e5074031210344101c58007582080ca0b45860a0b01620a1fa44484946d00c071096165030f600003000303002003081c1c1c10501448410300c404030100740640b01541c400c143c4000100141406e5818941d29540e0241c0314818a000c10802418400324040d4004926044520440e0f10307080140c01c00781c00b41102d600700310182d000301d200b00b15240d40e00004940c080e011400d1403550b900a06038180c0c00780038090142c4000359101c03810b170394001a10303802060b42c40742040e258580403104210740e51142c0d5010550503038240e9102d100303103002d0003004c0c040440282c049003420804103282d584c1c1d40d0031503026030414511030800603104000c010300030300150aa24141c444441d540da91280f4000c0c0c4100c50303d520580001d06580003c07000c480583c8980a490700030340380c01c141 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 777840341 1250 777839091 777839107
    0x3020c100b04050f07050a180f061106010e090a020d05013b06040c0e06010c020901121419121815080f01081207110307120b0a0603030806010c0204141602010606090b 73
    0x34074079000200c280d0f0030748e403030610010b8240420b00b0306102a244607941c182090ba1310341561440c101d0103810025001c3c100c50140440f1110000f0407001c031036419511103400100a0812600401c41c0c1320503010b0075100e04280382c620740800c901c8442041c01c02c20300c202d0380b81ca001340d925562300811039004019074032482051124040802e5800c1c0c1c019014075011030307907c3c03095001c030f01e01c0b07070b070a9202000306408030310081c0401400810300007a444035580188200d104404000300390392842e402c00b13040c1d03010507805403020078810f4910708066030307040441c20242c9a4941c00079110f5103c40070810001142200495400c480261146040700c0e4200c0080a040755040e8070798013981d200e03c4d0103c0d02070081541180f081e0f203044c499140103001100c59400600c0081c01c1021a8110040001c2d0100707151800910010f504208002c0d04280e00f0318088150313030801d01c041001001c109240000d41038009040015284550074029083c404940c001e024059a8a10540d940001d80c021840c01d03080c00c0c03280030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 777841591 1250 777840341 777840347
    0x905160603020712110f01110a02121608090a0b070f0b0604151734050303030403020d140705010504050d020d11030301090c021524010905060d05040303020c100b04050f07050a 77
    0x3e030401c10324010385d0344518140726480d08444281707004210654020a030f101007141c045c0a84400c00c0001a042c3e4900070300033150030826031500c0002032180202054581d41920380160280142c044003100300e0f9188561f060403800540820360481d1001c903480001002c0d030809005503001d000b240c0c803003034070150301b411029000c03451409814240c902c1025024810341e04500c1e200e0740082d41881c546031484169074281d142a00e0913802060003a0310401c14040020350018800e101501075181800c0f100d41e0072f03c0c5c4280c1238891054068440d40c02c20003480140200461840e51004440c1c0886000002071f020954a00122580718012900705000420a090807500501100309042c03040d5205c131401c0c0b0402a4420800b40d403ca40e00155421650f00310400c840e080388003006003420301e1000f0600c1c0400051030352140c44c0c075185920f03483e400480c041501035015182c0c04007046055400d00d583c5c2c5c4245a00030300c44030301ca0380d11650614000c1454500c0b0326070058003540541d07444520b404fc40c03070415 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 777842841 1250 777841591 777841607
    0x306151d28091104060e070305071407061d0c010207050f0a05030106080a0516050a210b0a20030c0307260415200d1a040905160603020712 61
    0x8441803404440107036032184058000400030641103100050080b04504124600008040c0b0450185180c20000c0c03000c03480070448140d201c0028500441c035030f90f504130100c0b65141c0c000d8020100c0000400d0701000c0140701d41081103990142c3d00c0c66202d0011166600360b840c08141c03805800750f00001c200388074609105508510000b406070007a00125594404642140c406070301c8090160080e40d42041086418082d0884850b62000d940d5009404e00c000500031702078034071400c81504103494407415000c00c2030b1000b07100240c00060680951400718043c801400c0c1040224440b56002600429101150001d4a004808240340141503949401003901c2c28090000c040081d1080c2541300050281c0c9520840c0c0b14910a04407168280302452017181590744d6070401024041e807400044802e40c8541040d1100c420b030707114000c1886001075240340801d1003940d022642040c14060100d05000e000144c2c0a194444c1005400420395544800c5049005a21009165410400d4003a150b00d205030f0349 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 777844091 1250 777842841 777842851
    0x221070204060e04030e120303090c09040f0c0b09040c0201150603051f0b070605010e04150222080c09130b160e04091202010501120c03080309070810060306151d 71
    0x64503503c4891181c0340c482c0403201280003131000c50007058a0700b00340d0112403449040038011403d41c10100f51803500c48990140c0c4600a00d0560006800d0026a0b046507a035941c01082d00c1c3d91141d00c03041002110340c0f240b40668010703401c140030090b030544140308298107400340ca03109000f49402c1110460180002802031484506258642441e0042c24004c0000030145240115602c0d6003500e02401031304d4050703210340c807148810740400c00170801052810004106030540142d442c8903144a8104000e5004030484804a4103000480c840900249602d09004100c0d1140c5c600c0c0da03151142d00150044540013425820181c0104800700340d54a9006002009810702d4210601804042021900d41d100300b5602080c5200d4901c64050302803007032078058003007100c00d12404401911303a0503a0080c0b070302c0001c040741741c0007000a513000c40511020000e00754441c169a400e1140110000185c511800b09503811454040d49070700700714ac12507583c012a804004030704101034100752100d03140800104 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 777845341 1250 777844091 777844099
    0x63a0b2d06010e18060a121101031517030403150507021009020105070b0a02030a0c391707062405040e07091146050405060d021902210702 61
    0x2aa00f0a583c44408250000b56400201e041070300d050740800800c6100e55000d2400c0d000d04490001c0418032070b0381403c0d8000020708001c114005211941d5008000700c0c3d1102441c800029540d200c101c00110091080320b009007031122255101c01007410071100b00b40c803000050781c81100c0d8120400226000030101c1401414505d090003696201c02c000341e032045601da2600c0343d0000401010701d04a100d511140300d400d242c1207034840e1401003584084125141668003030301049060081041100c0c078410301076036114403140c1104510410340403140e0043c500071661a03091140051400d0103143c003c04c20001c0f50421510b40070b182c24148402007a100416412501441c00c011805909501a00c480c82184c181025590416866646c440c003030301d62400c0341c14010401c40c0c50a20100040c403540101e02e4012444006159031200391032910580c3c0c07082d5000341c004540820340143c254080c200c0400da00e0803d201580b0b600c1c030b00b00d0310740c03007811041c82c21441040c4070740407184100400760100d80c1c80a0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 777846591 1250 777845341 777845357
    0x1204170705060f04140604080a050d0209040f0203100801110906032e0609090501240207090c0e090f040201080c0c0709060801050a06060503040506063a0b2d0601 71
    0x81c95460600a04442c1200d402c034558003400200060b00c6104d80a8440170809407501d802c042d03480202c50711904118104104010450307a10752119a4100c400c0072900810070041709604806a5010350021a820b03070900c103030710000203a80d40d418000c2500b019080b2000c1d915085500d4100203c541021301031001441c200080003a0414409001154140d40c2c149d0650f80c9501e0108010101d440541100d07011074184401042026008155846a16500542c010003044222022858402e5136030103655807609000d05603191b2504031003080b482500948040c85a580d45a120400f1040d064400a00007007004000400200002016114502a60056580e02641c880804050b58403540049055955410500110007114401c25000305120b0410a0851810f5240c880d1a40c0d030050600e40200001d80b1460203d40000030703c40d4060f2b1b25003000541c0c141b910300301c140e0b84005440c41107580109180200b00e855002c10141d0001c0a001c1030006e00b00c40d814084044030210182c010707814010340b2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 777847841 1250 777846591 777846593
    0xe0408070501182006070f170a12110702030606010804050c0a0906180905120d0b0616021503100620010504150f0204120209130c120506090312041707 66
    0x2c1c0502c50306422160060500c0850f942460740d40180c4201c80b4404100c403149440c030f400d0301d030001600c02d00c41e0003000e899188407041c1411850b8008446070310044400004075110317201e821000c82020040e20340c41c1040b200c480040312461900c10f460703000c1e60641c4840000b40003076101302241c50f4414495401c3c0e9030725218590118100d910207404c40340c0301c80d4880000340030000c007170410302064014080c0301744021600340e120f00e0745441c0e0a5500c901480b800040d0711102c000e40fa003010907401005080140e40d07200c40305c5d1807904c0000480c0d0803481100c001c1c080388203403510316051301d001d440080c010080882c1f43c0740e41a981c001c0c040d035400000c4021410054440c940a01c18244070f035000e040305004011054810004495400413031079030310340c4140030911411007441c9140c403032035a040d0b41d4004685c0310460012413002d05c3c01c00c028036030084440d020403003002e0313031002080185c8140d0881d80c00c2c1d180e1800150302d0307020781445211020003034400100401c1c1360034205661403907660070391880d103202 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 777849091 1250 777847841 777847843
    0x909061a0d06150201020a022a0907030b150c0f070614130b130806090d020318030a0606030503091c0807060c050f03090d0908061009051b0d0c200303010e04080705 72
    0xe4443c91101607540414040301e02134042c865100640178249072441724504080b01813980c210001002030240d0040303070004081600923480015030440040000002c028039a880400581c0036440c015010700456942c0c15005038005801001c1d01ca080e11040d04040a41e008140250082c80368032580441001001500c4c00c1c940e00242000107c108550300d00c28108004a071915402415403003269000e00c1100003180c0e07010059500c0508641030001300c03071007007400003840c00202510180c4040e2a01400100304803001000700607202056602c1886200341ca10350450b54462030001600403841003240000295055010340b081c002c007414802e09000d61043e41100b1a0401ca404020a600540c1007468440d003280c01d000007802c001e001061149030603815032205601074410f0008480e102c8001c59460b01e125554009001c00450581d034a410000101c0005030403403890681c007041e1180240d0400c03d44c2a904640121400320041d031659103817200f41c1c6a03c43c4003c105030396400050000d0400660 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 777850341 1250 777849091 777849119
    0x80901020109170306040b1e01030504020d140619020f0715060b030c030103051b1e01120903020c0f012c0a1203050903010b0109060f0e06040816060909061a0d06 71
    0x241120350f0036141d00d000400e00045583e00c41d4044d110394000300d42011040d0003a451240200000c0c81d002c2002d44991011070300403051450f00a02540452224442c45500010b003a440303494600c40e040000350b02400000308030b01c90340d03031694610242041001c0102e000a0741046840700c1c40c94000030388079951f10683c42c80d81c00644042d600094000010001e2100800c400c4d0403959558603414141e10800c800208050540c85000503158240f02d44201b03203a0165015407016043c0020501000300d00c0e180c0251205c0803031821610411408060718000d5110304564200703c0c0039222813800065107810050124148080c01c250302400345580400c1d400d0524003e806140d100c0c0d240d298550841d5070406082d038640200c801c0c10000c22141c10070620358000c00d001c0ca041c6560900018010b4014085481e0384203582001600303125200801550103504810b2101721a290355075006525103500801054800e91310803400c03500740003284440c1c0e004c1341700000e05c10741020110000d482c0707a55501560981c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 777851591 1250 777850341 777850373
    0x1e2106040c080c03010203010f0e061206070f03052a13240f110601050607030c020406120b07030e1002030601020f010e010c0e18040807080706052d1003080901020109 73
    0x301c40c4078400c2100480c100200d070425102180254210740c1040c20715121445144540d03c81c922807003012a803035483d8600644000d541180c01d5030564600072a000d45240c1c00c042c000d00c0028500800580c50410801e1103c00741a214000800d030b540010712521495080828001e0311b806c00e86900007040c50102c00161280c0c0008030846020075600b81024108400100100e014051410201182500c01140003419030f40c089440c16210300312400d0440b00c20211b110300075001440c100c004130300042404069080c1380e200d1020f10105640d0385004405940f04403455022030380c00303407031075121280058020756400503040c81258550b25100140030f080d501180d1205d141c996562500c0f000780c9038412400190716000761421240c401d5041c84a01e0340d1400100060140d21020590b5000c1103290f2080b06e98003908200188011b00348040c803007010080049469030100f4944c42c002c2d00107120400031a00c1042d0040c0d203c80c156103162200c0404c1e9204003001c0d4119542c4100f554000b070890b21a0040301 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 777852841 1250 777851591 777851603
    0x601181503060b09030d082730160807151b0201020702090109090606050d0308060f010e0f15040b1c1410120203101e0b1e210604 57
    0x306803481000e41240c409401440060404105801da00d40300002c0040b056080c03071a0450076039440713243c9460000404189031050440c8003454250b0360800145445940c1104a8402000641132a01c0c590745410060441c4806009100706003210103000211019035010700c26080c030b80100b0340e0700c0c44908001c014400742c4560740c4412604c000940c968181c031282d50180021441c0c08555000074040d8031051040317618103070702c42190204200c103a0700410020304d0054002c01d048101c500d4050286070086445902880d507580d40f06400358810000c86602c540098440c080a1381e841c000d101280c07660714840003619008000c0085c0c000300b01c40c000d01c10300844d4044043d107840e001007600d0684400301c40314103c2820810501144c2c0800c1c201ca031046490f071a101980074605407000c41e00b00100700c4402c11400c2d10301030716040c510102d0007407000d1400d640e45040001e101024100030381c2e0310000700c4020308076184110100c450704207a80c644004444e0b1110000040303007225203c9260850840c0c040b0b0324 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 777854091 1250 777852841 777852869
    0x603040b070314010506180319030203040e070314010e090c031608062401050d06030b0a0b0f030a0512090a0801061202130623010e0409061506030e0312060118 70
    0x815070502c07580803400d03022503200f8140d524000000710940990360014031004014201c0c2c06495a00f009214001c0c11030040450300342e040c50401a4491304284940c4034250341c05c20014483c244244030f0b030505c0c40130115510010f6400c0120102e035044000b00760b160315209100504402e50303000c06c00e1500108030024040b07400b41c02c020015090190140547d2200070400020203d445406001140100d8082c86c1c0b1a455100a00309200079000c00e6001410100c0c10900b400041c04940d041090720540c00c0e140700600c1c100340c2051507076800302000c01a100b07402440308503051800000040442040051080c013a403034440c1c007040d0845205034850b2030b00c40c00c200611421400c124580940700c0402a07010002d1502e40810401700c4030003ca0340240c0c0003070003821010b160303008a960451180303000d4070400210030989480c50050201c2003507842c04090711100043c804c0c0c460300941c40344404d200301460030046920550310302104081c04807410b0102a000c09000818121000c0009140103121405 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 777855341 1250 777854091 777854101
    0x7150c14280209070f0c0f0b01060921030e010e030f0705030c03030c0a0305090a170606010e03030f0d0902040605060d0203040c050d1a09010b0a091506050a0804120e0603040b 77
    0x6022190403100c0d01c03550740c0e9900580141c0d80b0f030b24010794840f0103410040004e582040702100c0c91004403030010f14500c030142152040c4480b4424443c10307500c0701d4403403096258586804c0d4040d400391250b0148502804000d500010348a07041d072002005041c14942c1110344d0383c4001174204446140740c2045039000c1d1404105034076040088180e020002c0d0095172419401906090b118880e5860240c140000040c050209407186081000142801d441002074800d8005a0ba0f4603800181d584a000a6078041c5a162034070b8080100d03040491404550b910f03161a900444c0081c118803141a41d001d99034040c00945615490010034100ba205540181d40e440c251800c1d40d844401604001d00420078612500002001018180100c0c9420140000b00341d4509100c540508a882c0710070b604245204030015480c1340c1030b08000a061854890400143d4680030219040c0c01018a201c3c0041d15007004240818056111144841b07641e1825403200c607281c00c04140d5550040d50f0403a00302d034042c01005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 777856591 1250 777855341 777855373
    0x30204270b0a05030d0509010c060e010509070f0627030c15080901020a05040902161e050f1c0f1b030504090b0906150a020c090906040b0106050c07150c14 68
    0x80c0407a407045540303000341e40c18040801d6494001d82e6030381e4188540041d04990320303805014200c0308a6484942030001c40c442c1700205000e0102940d1b580c2c41c03442916800324880c40385216040c113603001940c8801e0780015001c1e0803880001490b001c50003101903038a001c0701003110420004c1c007405860045650010740e4034030040141030001d102074a544d00c1031100b1540c80764444100d82c2100c405840c09600c0d80b221190f01810701c450020700828000300c01610110100d510b010540340740740904140d4020250342d022003a1200001c0700c000100c103030301d00d410710340c400e0082e210414040f500c1e10f0b040d048543c018940900c08186d02c074041d07001c941d000c41e040160600c00d002e038003240341c01039848a05904100e008618a601d44c021054080788001ca001d000d800d100300200c1c641100000e2080c8510f0608518054503140243c0e816120407035003030004a10a40113404032030424807041e0041036000e24008039072003501d078203031707051410480114070180101d8442d01c403090140c00154040e1038440d814884c0c0b0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 777857841 1250 777856591 777856601
    0x3070f02070305070320030d020f16030b061009030501020414040f0c2f1005041b03050303040807080409150e060d020a091104080f0307050d08012403020427 69
    0x500110352145405200060300429940d040300e034806e40e4226001c00d126210314041880030b0440f9018812801011452540003900c1a0004403006c1950b0340c0ea100280c650031540c825000161241c480c2101240d1103003000001c00650160500c0d1420b07003252690b0f900c3c2c2c2a64420391016403042e04400100240f440c003442401115407043c0c10810540040e903c1c040c00001070f0040c0c3d01034012002d492220503905c8055042042d60305e000648072a080c00b000c90320000d01007502d06654030b0140c04440030007030400c0400c203401c1d2071b0844010b5003540d940350742c1c0203041d601c0203500311810001072000185100c41801800046a000c010b00006182085d05107403e4900041a191042c0c400d80401405038a40301614000c1d20005940821b0340c022114410742c0d00d00c51076025060a10500c1400d510751200440a005914030500984080002c2d00004136003141080c052500c43c1e01d8451003c2c038060091902208901519040c0541013030754440c4d88100500100b08000c6804000000a00742c40c0310b540300f5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 777859091 1250 777857841 777857867
    0x32e0317030919050c03070e0406110c07140105121501030e06100b07080f070311010c05120a0b0a0314010f1d03090105070c0506030a0b010305060f1c0c17030307 71
    0x6007030a40c03428440c160b54462421090900c4404100261400d212081c42000a0014064111500c146e07484046e40745100c0210f40990f1003d03d03103a03400c84000c0700802151688900c8900401009041121600c104c903400340e0700c1030500c8820031070380c2001c0515150413485012110703c5c0c40700d18a40400094180e44001d40c071a12140c11403401c011002183d0400c02c0192141c0c09451902e950301c0d4640647c251042a0b041810340401154480c2050347c441c0c2d06180380c90281009000f4007101c0542510207029500d940e07144a11a1400a603581540d6400703000b45890041003085220368944840300c00d551035417500d007000d94440c04985ea000809018031580090490110308124015551507a100e000e5041c3d00c1d81040400960481849103110b112030140c44001c0602c0d42d242800e0202900500d07240c91341c940400c1c20080044c0c2c2514100110348001d04010744030440d4035a0600c200c0590850034031003210940000c080120300120154204040c0010500c015035603410b000c040134090008100d5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 777860341 1250 777859091 777859133
    0x114060a08100911091206072304080f0303041b030201020703030c060912020319090f05010f1403092a0112050a060b0c06150d1505070c1208070801140d0206032e03 72
    0x8e10603001d52019001c0e0707a0700d9603410600000004411200b19074840c40e4000328062250511990010745d01000840c0a24450b4004560b440c903501810004c0c000c440c40081d015803c11001040801e0141c3c2031038540c517228103000200940c640e59420690b13030741d6803e100c1c0145d00201d0032001c0c001040700b03002c1c4844024107142045518180300c0500c07084a6004d418100702c8400d0040000c20302491020079648100340c1483c0d203038a002001c4a41c1c80d031029040090305c0f00a18a01444505070252030320380d000c01a900c02d0050201c0f00c00184c0900000b500d42402c1c0d0359070300800110311454001802000c1b003000041d00e11406d145210340035042280f550300380301d41c1e00d240f940000a800f0041c004041035210138041203554070030b84103407041d080c01e07600540000920214542c205502031001403084040b03403540031a603600c5000c01070f155444640303242e8001d400c000380321002d860100702a41d03000e00f4002e6141a44008540b00008050030603162501403051510180208040c3c42210200100001703 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 777861591 1250 777860341 777860353
    0x218060a0803070f020607060e07060e03070608090a030e01110307082101180c020c0a0803071202010507230702040908070b07080601090302010e030c0a1d0114060a081009110912 78
    0xe161601d5130980007000920a61000440c90108a5103070400c40c03483e4540e10648680390b65510780501500d62380c214240c03090094940105803140545000c501404c0b1101c000e10568070a5501550030446800041e0705000200d80000c2c4040c1d0f081009044292040118580751100c190310f2011b2903140c5500ba2512191020050183d1601d0407600c504800b0b200070082148040ba440a03400c0c8083c0c0e1000c0340c1c0094100c080800c484500100074803034548200b44207445001c90030300c00c81c200c40b030540700100056031115001c3c40d0a003840c0d03101c0054078041820300c0d06d0182164000380446080743c070119040172000c00c8010a02c80b10805041c0d100c0001d003054a103c0c50000e0000b413a001351800000e0601030207420000a0b0b03141000b4400c40c01e075004c3c14650700262a140103003030300c4c0d0f00d10480034860034150001007404224845140380d4800050842418880010400d07141c84200605000361640f15410004020280f4080e40b804221150207182e9a00c000d8000e000981c0480c4c1400c00e02e5038040c03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 777862841 1250 777861591 777861593
    0x90b0703090305030c16080708030715020706050a0b1201050105060f130f0602010608070e100e090c191e050d060b0310020711040c030506030d0305060103020f032d10050f0105070218060a080307 85
    0x100445030a07561000030066280314058107030cc024055003101521140c80c02040041c4940994800c0c0aa000c04860088203244d0064030705081e41c10034001c99400c01c106000c10440000110041c052443c04414130b89005a100c6180d4080ca0040d5840035005030345425007000b002c6c00c24000c4102504c800c226031619450900070383c00b00c51807a1701c078660702811480e001402d07003403050040c220190780042a5125481c441305030b6032180400d41c000c011022013094590b004502803003800d031084075005002840c0b182c04940f641002044641680354143c01481c500700c028011520081c007002d441110640c540e4a060410f00c0300b1122441450010302d85041c0511045030380001740c525070400c080c500402c0da1307612600124064000c000030340c1c1e180e0303801105002100100e43c3c070b41000800e0305c100c51059a502c9022040d0b4081302a81c08203075606408506000e1810200c080b408090760604000c1e1810403070382c0c04241070607080220740160004a1051240e00e2810365107041c01080740030021070500c40c01e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 777864091 1250 777862841 777862843
    0x602030306060d1107060603050d0905030c0409050111160605060d020f040507031104030602031b071a04030e0916020c010e01020c0402070f080313030f030606090b0703090305030c16080708 83
    0x10103040301d44505008035500611408a802010000b1441c000b45910b80d8081d1401c030020300310302d000445050282880600d82e81c0e115110304012600000d00608100b40c40c002848018208030070150783c19500c40e4091543c60140710000c1c80d18403282c282540652085040c0075013100c00140c83c3c940700304a01e5122401694a03050315206000f0200c40001e01d94582c404240e00a000c080b803003a84410703000c140003060103101c2e40514840c407110003040f041200c1c4018803965501c2116070090510f002c1140449403046050b007050b50281c031900305405511586400110100b0003100d0010490301602860303840c40764103000b45002402d081c2884101c6030103a0300080c0d12100c00c20764041c011503000c5100003e00080c042d2021010b0742081000b03940e070800f131503003990030356003044140d02096070342c8503c107031151080c80748038210b030180d07035a400b00c0700d080843e2070303503030340d202d500d041e03040183c45078021003c20001c0c4003c1c090983d0f000c0003018066681079494040702c180740c0c016041074006020400036244 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 777865341 1250 777864091 777864097
    0xc120b07140d0507020f011803030605030c1507062315121c051e1e070209010b07030509120705030c041512030903140a02011b12120209190501080907060203 69
    0x1040210100d096071303408800b207140c04600079003000705600b407803211004a034007040503980309802941c2c103000081d280c509050360703050001c00d09500b01c8240350080b4102c203a10350103021990b116807404104d2080c4000340e10241d20300c0744102d04041038490188071140041501e5010b148a0581c1c1c0c8000d150401015540c03900400084080c7d0101000510000184154120b03011410b034083d42e00c541c164032050680311500720009146600d0107807c1091080312241c02034603c450f0303008000d816280c0c00c15100c0103140e00460300c220107022052100a4032541c4654030200b018004900410003d454071041514110f00c1d5014130380100e00e0104041c1c920458504a07409403004c103642c0c040034510a24003100c41124650024120a180c061040402c1030049803948026000740c1e208020745c1070282640510307801d042c400a00d01071807a4101da092500816082c1501504c0810040c10143c000f4040342c0d00701540c1d2034009441829810038415903030051702017a04001040c009062580c24048003a6480c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 777866591 1250 777865341 777865357
    0x150904021008090a054602040c03060909050d030f140a0b0a1d0f01050402090102030a080601030f0e030d2322080d0b03070806270a0c120b0714 63
    0xb00c10303080081e4043c1420003140c0f60456008044070010300c6000302041c0030840403584640703071140010b00086111002d544211001207120303141001c82c0521b9003000018000d00c403101050646600c0c0000d4a12194420700ca54a80201302410070203d040c200101190700421186120500d00404035500e066040e450aa20a13407548000444d06980c80018001584c25130020b10030440e00d01c0041c1104041241883c000d14604000150998a5904200c1a4011440500d005038020300103203c1c8584104080d81e0000c1041c140081e044204124100c16500760400001c0341d6030002800110341c652511030300c00741282c1c0e040740c541000c030102d184c40140100600400d4940300d5413000c51100259400000704ca95501c10f03980c6685103880a4420040d00c58000c03d1842030061110000b0040c00c04500c59119500210146c44c024551200d4007090303c007040c078102810322440c3d00c06e10000340342c1d0b52100060181c240344110385110529081203c480c00400d0402000701e100d1502c8600540041078507100b03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 777867841 1250 777866591 777866597
    0x7120305030106110c12010c03141315110705030a0f0e0112051008030a020c0306010509100302060c3d0903140a0203040906060305060a090e0318040f05040311010e030c0309150409020706051509040210 88
    0x454101ca03a18025137003101c000d0b510000c00040d0300c0c0400200000806440c44192103800d00204405000c2e20052482602c03a03012501e01000310a5441d800e0380015405135080c1c14400c0b034161074000c80e030702c1e40e00310f003100c080035034001e006103100da1408104090050000711136110b40c5252000ca00801030849100083c0550408a880c1b10881000d0080e41004506108004d203c0082c211406561140e2010201003050b5030942d100c000001900030f0f240b1042c3c01da1660140f02c4000c88240d45680e100c0b021070301c00c40c0003d200114142996000b1312000f02030f00e0b500401d280c00e0031030030882d480380140e0100541030300d015081800480c3c0070040d1800b001060000900503181040071401600801c18500c504500c1d1604020070541c01c030b249403540e004114001c03c52901c07281c145c16602e2243c46c4c1141c0c490383c404c1c41604014231382080c0b510f01000b0040c500605255272909244142c1e0082003045468235129001c1000381d4000070040010507108943d551254141074003c141702e00c507440c1400c010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 777869091 1250 777867841 777867863
    0x207080118080f0f030a060306051f032301050c2203260909160f09060e1309050607080a0b0d08031306150603020c07120305030106110c12010c031413 66
    0x6a4129075084da129208a0850340c2e030380c1d142419242009040030300080b18907514040110720318044e0704020310085980000f1413188a4110389694031031041c0b86032004000c40e0b00817650a140c2e42d003030044602807028045100d885840c400d0f4203030100b1100c400f20f20310341d80c40074000704003249448000d00c0440c4007032518502441d035401901c843d1880341c90034283d000300c20304040c4010040c2000f46441c50803019030f1106030040b1504811500c1405030703c00c450000301c0c901444401841e00074500e682100705100001001c0000d55951800d02108651010201d8400c40411007030b02ea045c040c100c07003120203c03141d0f00b000710544e03648a11408040c200071020a41041d10508000d41e40d80b0400a055400302d00e0380340d0703e64412006010790300010641c00301740144100000c814920341a041105940b50b245e8505681c2000400c48038511310b00c60341801441405012106902c480e503040d0040044080041040c1505010240c00c0d5000003400c050604c501070f0800500c080c400c01e5a00c0040e41c41803c3d01a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 777870341 1250 777869091 777869107
    0x309030418060b0705100f06152604031d0108190c030f0e07030303060b040311060a0e10050c0f0c010819020702031501050a06090b0703030e160b0406020708011808 72
    0x6048540180b203000c3c200107a00f0041c17050014a4540c0d48986150600c0741192100042c01511820301c61110354076100d020b6164814058103001030309684104900103d42041c01800301244000d5030300b5408242c21101c81841011250000f4411601c207081101107810000c00d1085840e8030a04001c0c0025551880c0c000e20b14480e03000115040310010051100002e2252401d4961095100881c00b01f80b500800084d400c0c003241c162021039130020b041e07503a100703101c1061004540c0204511030411089110542d902d640c1e441c0c0da00d2a040d52550344c0307610354070441c0e000e40c03a00404103040349103035008200c0b050702b50713030b00c006496842846c2042100001202090f60030190040300e5000f52301d40940d8100d0410b46440e035a6603412908104d5442102c01d9880c00e00f42c1da000040d01503810545410003581c00400e00a80294100c001c0300c50465142440c83e030343d95003546015403c0400e1608000904022040d4100962000303044403500030400c500d403001c05a0f0201d85240c0c0002e059400101d0625 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 777871591 1250 777870341 777870389
    0xc080118031409120309040c09030206030103081606050c18010318030f020102211f0609210b04151a03150919030207051507030c150f0e100c0503090304 67
    0x303003410000381400514594240c100c85e04c9411007000180101c1c07034185c0c50005d092140080d0b00403660050710711451a405e60321200c4166000307400390545400361051f02c0780015010b1280510821103000c020707031940707510a124118115904201810581060290480d8150840d00e0220300f50340f49c00c000e88010008034040e800380c06000c42c50a4440800c10118110005181026200e007140d0746800580040064080d000340070f09005e640001031194000340009008070f60480d80c0b0024918900c4003500d555540c4075001e42d401c9400300c07200b80700103060704182d040c14000c0002198085000b00d0a09400030040b82d990784065100c4000d071f070300540c0807410900c01803102203200f540403801c00d6030800c800e080c06581c5400520440d401076005043c00505102c01a05540c201c1e0b45c15a0307604a85542c41d00c416038003222140c023203040241e0361222041c0c580c0052040caa445d0b0300345c3c80900b50074070210402408403104250040c0a000b401c10030000140c60210881c1c0a076a00a600c148082c00d2580c440703 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 777872841 1250 777871591 777871597
    0x301060816030605370f06290310060f0207180f050a020901120902120a030c050601060504050f06092b0507291e0d0218030a02010f0c08070c0f030c0801180314 70
    0x120f0f0007505d081c402181e0008440640410b6200c23001c0c05000d02a42600b04251600c021940c0a030710704001d520501000344a070b07422100e100c1036881111086921020b1050041046030041001203580d0394032910a03107618003a00d2750094494500f113040851010000c1c1840c10417180c0c0d4400e5650b2606604115684c04a455500028000403608000441d1801401601030501e00b0b5450f4030502c0c000158451003001244d080c0c9401030708461100350004d01b0710110350861003801e5445100221b002e82007540e08a1b507a0341300d100d041d00001d0200d605080541c209200ba400513003120401409070a0300031114820344d031050040360301d20340d520341c5c2012143d414081115140354140030002403040c2607040580240c1044480c030b14a51101040c420109582e928954000a000c64107540000640e507004441c000c600a024000080ca8810720390f80c1d851044840e0b410110900910500600c20f010300114807001900d8080001c00c02141301480240d41c074001e9450050810030084888450114504d0503 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 777874091 1250 777872841 777872861
    0x2070501050a1e020a02090a02030411212e02041a0c03070c080312010509040201021002180603011206060b070b0408130806070c0611070b15030106081603060537 71
    0x540781c2c030007030f0204025203580c0c0d0340005a00c1248101c0201d21400700e50710880380925801515150b01c007c100040c810441d000400c000c641d03000d04250440da2101c244550b440b6541e402d031003070324100c462081204500701103541950015105000a11200340740b2200712203c101710884250312a0000348280b0b1461240c0b1100a1403c0116a00002c0a42000002e07160040300d03450300c5601680c8400500168007000c8801a0060b480120501e0504891741e000348080e00403015200741c0f00d24240040f40d82640300782d0000e0784902c1652400d905100740c40c0b242d04050034580020364507110243d221314031200360151000d00300d03e41c00a000052038565100140003401c00500799a480d15104102400303030040010180c0c2c4007070500c120700459080320821601e089034044080043d64855001011310307503031400746154040d941e17008082480042003110361103c0080c11800c034040341c11450200d050724030113440ca44001e03200c0b80410341d494440200504003002d51581c000c0004200f010b20202502d01c600c0c1c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 777875341 1250 777874091 777874127
    0x2160909320316020f0904030c021203300903040b0714010f180204050a060501140309071d070e0d02010e0105030709053c0d14030c01020a0503090d0e0102070501050a 73
    0x18600740030f850a000b8500003140205e0b101140c030100182441450082258001c00194140116500503c1d00c80901010001c0000480b81081403c2c0d2a5048c0d14004c211040840380021412447c08909202056841841c50000d10306240c504628588107003d09031004020f04950100d05c6100d4409600442a05151080901c02001d900c408507030f0b80403841109034000c0d828a070000341c3c0029540130381001c44506030340e410311544a038009aa15a00050400000750151500c005060503010124051003980740003880c6080c01c01c0e03a03018040c1240c0059a9014411820492000d0b0780c0103180e6004021080c00c02d41c0c0c0d25074a0724401c850f44805900b246e0360040c048145c1c101242180712141010710b24182c803a40c3e0540c1c3c1c0340d02d40c1c43c105290720364803039000c4444020700740011301880c24a89001c4540c001c0740c1c1405110740c005800d9800038500c1c8070004a011041201c503501c00c21100d200d108440c02e210f414031405200003911424180242418082c0014130009418441c100144580400344 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 777876591 1250 777875341 777875347
    0x604060203041a04290d021306020c011d0607080904050405010e070e0c070f05010b0904060c26010314030d050c07110907022109040f0203070305010f0e061c02090403021609093203 79
    0x4803901d42c6823501802006101c0ca2500324659401600d12449440c00078581360b150740798a0041102030340c88060203c9a041003400a005c0b0b41d2650302819003d5403044001140040300c640603a49407248a0f40700d1441c00025405001004030040d08071121550000007103440f0300354900f07205000d8468684501e401c80c030740c081080140320495000884828690791103000030410040800502850300c3c48400b50f00b82001c1c01000040c2650304019080004c19080da401c003118080d4100c100e0b481154216040300380015a84c040103044821030112800446c0e0a071594180404000d5503502e11101d40340070142d241c40e1800d21111000300b45c03400410010014403a51b03190100250194006803a61008a4140400401ca24800c40b00303840c01c0e500d512540911913541d030b0080060407440342032420326440001c6a060050384407410480c1c400d50080e001425190004c2c03c4c0d0290008061380701890041c60455004006400034044c01c11088081d183e15046110ba50380600c0d05040c4c40c031040a00d40f00c00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 777877697 1106 777876591 777876607
    0x60f080c0607060e03210c0406080f060f060a031b03052509050a120203120a050d0908040503060f1015121a0604060203041a04290d02 59
    0x3410040384d803201500b40d46055602401d02e48100c40c8988500d811031007030b500c54a5820407900810a85010f02d0407000614481010300901c4002c100c2e10046101551500340c0d40b449243c000341203c2d51030803801805002440034803052203403181810203c0703512600034412144584146614a0303042490a807013200460116141d4005200c400300380411681c0354941c0d981c1c06001d0494821301d000f08507004061810b91414401e460021301001411605035200054070b500036101c0c0008195000b075490400350700c2c0582d4100c2c2d50548209001c0007824140254030b5805600415104c3e000c1a8844402d035504078202541c04c030103e2280926a011105039906c80088242094051049010007100091003a80190f02c2600180c4c00800c1c203008120011103242140480d02e40c0a0b4609450188100701140c5a1005070403c6402c08401e07040503840c0b03000300c0c2c0c1601081c000455590b107030 = true := by decide +kernel

theorem cover : BRFrame.Cov 777697841 777877697 := by
  have h0 := BRFrame.cov_init 777697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 777697841 ≤ n) (h2 : n < 777877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
