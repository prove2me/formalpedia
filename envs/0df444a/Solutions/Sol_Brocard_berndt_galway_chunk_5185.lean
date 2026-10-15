-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5185
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:01:50.205132+00:00
-- url     : https://prove2.me/submissions/005f87cb-6bd7-4f8a-b86a-c34285683e3f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 932374100 ≤ n < 932553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 932375350 1250 932374100 932374159
    0xf1c0b09011a03060a0801020304050a0b070f0c12050c072301050a051b010f110301090c0c0c090c120c120c09080a240606091e14130b03010204060e090105 68
    0x600000219139a95110f240039001030001c50000c1d0748074501810318a48136240b000041e076481801070001140c491188003450b400c032050342c5404046c180035441d0607031041c8070034240c50b05000080103005001d0508002d040c0060a0300141944090721720301c1c5c0b441c02001d0540c070b0b25050010500000c2c40030780e00034058821311fa00403410107840c030300340442c81409800003061a440d19813403e82102c11900d50440214183c0e40a1034080c450101c100724100c8503000c0700007000d4000071400707805100c14082ea810480c1d0900c40c621b0038031100003a074042c903400c03260001a01400301e28490500c40780c048150145444a0503141846a80390b490701464680301d8610a070000d14401002c1d010303503110b0b8400d95002040c405041c1c010052983c50341c44c00b134101c002c5070158440d4501c01202640d5140207038000441a18180c1c0710030340720700005906110140884880a100f02c40c1c40306000d50315038909201900080122b580c400451031004014080c00c40c8060b000a4001c3c40350154401c0d02c04c80c809050103004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 932376600 1250 932375350 932375399
    0x3100501120908030717010b07030e090403090f0603020703030e01060b0904090312110a09080a031b0213090501050a06080a050c010e0a08060109050103120e01021b060f1c0b0901 78
    0x4500900d01000b400c2e0004003c08444000c01806031265000031100c4440c04490718819a03030741c80e1030040020307000e00000200028000c041e44000342c1408610150828031030b04010074115128460090a08103581000340000d5020848000b07155050041d0317240546800000c004075410312064010301d02c00c405a0134000d0f03880c1c101460030117204080d48800000c0195042060951602e958500c0ba804070602400040403c040410b5481c00818080e00c1a541501d4900c01740c0880744248888000e520b205aa00210042d10030740e10f9002030292070055442400001100c1c50490011802c461468000131800e5000d8441070300040c0000403048454202420700580c0002c0c07020004502651581000c515802441c00004101110303410031030681e0300c14140e5a40f004a8a0000c031410314001c400140141e000e09c0b1051180e091400d4416110700016046c1c900d03010340d08040000a40c04004601a0f2004054400500c003600e403048074940042141d25400e01d5150003620703e82c5d4060070800c00b42a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 932377850 1250 932376600 932376617
    0x90e07082a0c0c12031c051830040b1b1f02191d01030c052109100519020309030409050106050702150307050d0906060f03150f0203100501 61
    0x41c07070714106441400210803180302e40c0d038101c401c0344030744030110f08900c5800340080011407000110084240c491420b131050400000b580305162510190101805840d4020705411109500d82d1060108800c42e505240c280c0020308951042d080c1c86800180f1140d82060701440240802c030500b8080710501101c0c8200300000d007110000440c18141d40304100030092804029404040c002d64015202101c0c2081582400f1460340400f43c546002e03000b1581a03000b084103c00000d580681d0180082d0700c500e1920300e041c0101200100c03156600d500000b8900c1c400e9108000390741804010305840003a0320b0718140118209518041112850160b1480c0c8054000c800121086410015613005045031b10b028016035070f44480103400341c1d01414041c0c0c02801d450850420282e4082d0880340176900b00c0e591549000303010705480c402014503c8044071000c0e140e000008250100d9081c0308040c50089030500f03090300600010204450755103c070304a280d4018010081034184587e2200201d660a0919404 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 932379100 1250 932377850 932377891
    0xc0201030b0f060703080a0f1b050c10021b07090b01080f090f0601240c0c05130608011109030f1b0d080c07240206040c0623030106080601090e0708 65
    0x1000b44690a855420802c041101c8040c90350288000340950001c96040051800e801c0060f03068a003441010355614510110500c0c40501c540d000b8505030600c40181c0e01d0304200f000b841001daa219043e02d640b081400002d844000350248200d00c0100000ca001300024405a8000307044020001c0500218000c07002c001007605000f0710521600e0071402d0160380c9a507848a00110100c11032603820703418800c05401944580c0e0003000d1540b03540d0b030000c500351091461b00003080076010501d050801410b48036000091280002d0094006880e0754040f0140c6400380402854a000300410580c860b03a80182110700384180c44842d41d0040b5101031b9509900100e0b24108001e00d48101c0c10040a2445030040010b913525481c4640f0150b800c48441155860034040c008a9440794280c0703001c1c249040f80e110070450207024441c11003404601c1c01c5240300000210b00050140e0304241c1c030213000b040a40b0104646907038003d1610000d0030849030028071500700400d0050454100420701c5188041442c0a0f00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 932380350 1250 932379100 932379109
    0x50a0b13030b0a02030703050903030f041101032a17010b03060906010c120f020c010201020a170a0b06030910060b0301030f0228080c040e070b0304030311040312110705030601060c0201030b 83
    0x4090342c0c01011510441c2024440360000303610031100f100000349080007003200c183d00802200d00641610f04c80c500e854031685c441d051010080d10950b81415514807010001144040c58074072018881811b059022021100103444000d603003881c4010303680312030018007900c101d00c803d072a0400d02c1900c5c0d40c6410f650381d40c01070b80d070b040c9501c401070560030074580109465580f1000344200007013160700ba591141e180000683c281d00801402c603010446c0b07006450380078514211013540c88040707442c0c040b07081d403000d00c0821100e5209603120031181e000448800010b0300107010340001404039100a034515851911142c0c0000301089000344101b031440229010788012451004a00b040d84401e10b03416503403a48042d540b06c06107445140600e04140941a00c86d1010540d07200f1502e022400d58919541c13a641140240403101100a950900340404404209103c003d1050072580d03880300ac00c050072a691070342c9880c03910b5001506c6a40010010f00110394000728036107507207a080c20b000c18180703034400004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 932381600 1250 932380350 932380387
    0x8060310051b0705011d0105133914011404090207022d03010b06041d100308030a0204050118030201020c060912011a010f02010506010206040201120e0d2106050a0b 72
    0x2942a03800103e501400d028040d80b1441540c80c0011281450280c0701c000d16003611030840d410411003400520312404554403003500030119250ba02c42000907000b00b800c100c015203800352000081540c44005101e90501c905030944038032000d082280c0780c5400d0110030320251081c2c0c0654094142c0110f045011034442c02d0748185220b00a0050f049410110b820003d004905038034424800d40c04c08800901c0d46c10b0120458013519179070001e220780703030b215080070500f4100c01521007060a45a1040000450307840800b45002e0140b0704005a9202c5c03810f000180078800e00115690031162041007080180e8000070180c0c48c0002c19501e0988645901c030002e25000368a44548007a5403c02d1314806c511001407a80c541c2c1990242c0f00c050404040d518102d00305d42c1c0448060380903034848008200558010300c281001c40041401c041184620070b1000c0d8203047c0303640425008a1000558544414455002c48044004488040144510701000500004020711641d148214000b685080b41c0c0c0c1283da88 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 932382850 1250 932381600 932381641
    0xe0c03010f0e10261515010908070303210903020d080603030309060f060a050a0f0905180a1b03021c0507060e0901030f0206090603040804050a0f12150b0d1a0105010806031005 77
    0x1960b160035071030f00412000d217008880000c4400c100510011081d0301400c031130001c1c0c40d10300c7d00070a1024119a0180c80e001e4a000e80640c583d540d602c000c1410b400c45000e40814035109601134500e0f0048000c003c1d10400c0048c02041c865001401001140000020800c1d030025800d0424a9544c4030b01c40403648043c1180c001a401c460300a5011411200001555040312141003040040e60b0300ca51019448004105c8003c0c10307034124140b6400850804507915070aa621034101025559480d80003e140c48a00e0038541254503c00d089481441030901802c0e004140d035040c000c482c41e00200008003004014080208a03005042480f0250745034241074805001c000f819031503513030800f420018180d070428440d140c402c3c1d1503d08085400c0c80c800c050314003100e00700a031008030040c0a1740c40010010507002181451641d51031160031130707a205916a034006000c0d01c0902605020a0409603e16a058120f9418404020f00f80030594500059101001042038000030315034a40702a04520082030b14031 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 932384100 1250 932382850 932382853
    0x180b0c040906081506011b08030403091203020c100306120f0c0e0c1309060b18151b0c030c090610030e01020406200c01080a0b0105040e0c03010f0e1026 67
    0x140455001d0303000607413644c0640705004a000503520a0011119640503102205e420074490600c00000b400580195400c1440f90800380c14840d261103600000540c005403e9006902842520322541064000403040109624051003004d041c50354440b540003891800800006072011803000703009600c0c01902c0a0200300040d140b490070500d030302e80150341240a002c02007094041c0000382c206410310541c411149000310690030300e502d64103140000c0d90500d00180c1c01030100ca20000461034280f00034100740240c041c0e034000c88903039219007514141c9a1a0214069031140842e218542d440c032100d0741d0300c080b044688006203101e40e14100c010b000c60002141c13480d80045000700b0166002400720102400c50180284914203840709a95501585013a841c0460340d14004103900c07100e80d40141d5908081070400754500f540c0c503000319428070000c5605941d41c507000300c014821255640071900044c0307140602c00c2040e003807141001c901c640d882c3c41804003003102601c080c0e0000480305001003294500c01c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 932385350 1250 932384100 932384111
    0xd391103030405010510080f0706050708160501051503010213030605070207090c0c170a091e120c090b0108040312050615030703050720070b03130803091c03180b0c0409 74
    0x58028064517003a074540011441c48000881c10b60400100c100030016108003c0003082c2c41d00409071403e50000b4000c1c0c0b00340c0d90400c0303000c540a01c50301040000380d110b10000145450001080380d1700203483c0d41124800d03401000030581d406207456002e010744e038200c54001942e132501201a0301e840700580c4418140390078154000c1e102c42e0031400b50300701d0354090700d803524a410484051080b1482600d94610100d005210141b00d211001c48840c01003034503001c20810582d440d11281221048014400c903080c184220041c27141c980c050146080091081c24100000c2c00d06545c00b50078024240094070515646000141d507903030361242000803004108545c42d0b500e0900c030500030b02600080302c42070b011880c08050501d0750b040a692194039007074004083c00c00c0780c0c100b104559150b07102030071940c151b462412003200801c1c1e0003401103000b904800002c080028007042065049502c0d00541c105151810810b080700c00311244401100e584c2c0421103204d04c0d50b604030608031900035504240260341c03030034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 932386600 1250 932385350 932385353
    0x212090406080a0507031502070f0f03180f08150105030604110402070b07030203090d110d05181f0e06120c070501060b03160201060b07020109060f03061a0d3911030304 74
    0x2c2110806e076070183c000c0d07140d4200070440e01000ea10074644010125010340a02e44045003100114900f0340384203290040e00701105c0c0d4511101001d40741c101803005290f14204015002c130411405540c04601444802d00358074000c00292920002400031703020110801c3c89495036901c41e411a00025400000c01c5c54905203450018002c2d0030071034000c00f030b6110f8413000e96070309800b88aa60400f10001c4004041c0c3e07c10041c81200c2c1600081c0380441b071205070101f4001e0aa0300d0710151110201252341c01c40025010450040000c80e49402640c06002c040191820345030031040001c2d40001580b4015a07290903e2411074010529981300e900c51f84004414802c6060301c41c2a042c203142c641d0381c002e0003c02e446440100381440395101c001e0115041c107800300581c5010340ca049c0694411400c0008203d46c0d140d0445030760a074420208654a400082c29480c03224a0b88203144000045801c0d001001c5034801c07181d4031000c45403005e81c4035203007040c10180d222440b8030344801c50345c14200103a03504da0909 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 932387850 1250 932386600 932386603
    0x21b1e030f211e0624070c090603031e05040b07030e0d0b040c051801050f0d03171312050c10020327010c0f11060a0c170411130204060212090406080a05 67
    0x101d4840420486696011035110305c1c3c46040f85542e003d440100f1040e01d0b8020800103207580c803810f07049558207407102c07000410a40f1031003020021030103a00d51100200044440000044410254000b8003500b407009101c5000c0712070a0301d80c810341c941001048940c2860002710540308000e0300500a04074041080704204c92140c00c80f0441d54295946c01c0e403100e030ac90a02c000180c0074007036203070004441c901c0c100d0686014050a842a40a810004d4200d144030074035203080340044a003441000c4040c0f82c50740801801c0b1403400300140da0307803825500b0402044a00c903180c000070f02c0000e201c10340103c00700d403040324000749800c00e40c082d1508d0307034000c41c145030f8005010b0002c005003180402c80d00e900c45400e4500454030340c885500701c04003800141d41c41400360b07001401009955000c04c50b49400048015002c403101c80c0c0200d0260740070380c807801020010170440349501e580000082c2d006100c02c020042d000a50752a40d003141040050711240c40340003180060110b6440000d00d072003101c140c8001e2100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 932389100 1250 932387850 932387881
    0x40f051501020d051e090a051503040317040b0403030f02160302161409040f030e180f07022409030c070303110c0105070c06050913021b1e030f21 64
    0x2001e0b0280c55410041010a540341e00500c0b460301c00c2030074007100200c500e0264400901c034141c0018422411584c907140801c4a111140303a001488400000903c410b00d50440c0301080300304000c039882c60b594038141d51410384003e03003c4e10080a054565a140c420800190159001440352107001c454103041802c00966460042000c5014120001c030081603030400e1240010054002a00020303681c3c9a9954080141c043c0076801e42c10407420880c03020460785c941321015104901c0c0c40018865041604074603a4040000e04004199801548414882c401c4a0410902004076034a1040e480e501e00e481ca80c214440c844d0035000c1401050740110415070007400c074007542110101180ca4040380d1000550300ca06c19280094030a4803015820400b0901c100010a0000405060700e00040070501101c420713a00070200c08100741901c0d03200d021107841c0401004074500000145e0400c0d034010803400d00e8407841510706200250f400001d190205201030039190040a521b0340e0f008030945070003921005c1429 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 932390350 1250 932389100 932389141
    0x10c0e0108090106081f02040905100510030501081b0d0b0a09140d0e120c1504050310091e020109030f11120102090109060302090d08160b0903190509040f05 69
    0x1d90034000b10301a00014480c190584002d64001c1c520540c5144101069410903846440c01540822010803100440d0240078001c4144905484025062070104140b08040000840826180c40d0041203081d200050041201c00c184019480005a1a020803903292002034080d11f141a18810310900c10312a40c840001140904000d09042112124040d2640c10780034809000415603584219545040c40840c031003c2034440480c0e4a0401e40c4000c00d80c40c1000416400b01c450000c601000507007014046412100100d141c1003040c01c8035541e078001100081c3c00307019111940c0002140442e405004c15901643d00281c0c140c00250302d5140c01402413401c403a000307020f400d40d2124076490302d10500a4420003e4140c44200c1c13010308002c0118000d400107020194030850840165011aa900d80140300840609120040d07807003039424030003010b941c0a82404442d6100700100400c018810401041c0344c4180d01d040d60f501c95004000a01800d07a01c4e020412291502d1300303100d0601d11641c040f10160 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 932391600 1250 932390350 932390357
    0x120a1707052823010c03090318030b1303051c0e2415010509060a0e2812113303100e040204020705070e010303030b030706140a0e03010c0e01 62
    0x4074031080c041d0440d1854015500d0100030042416070006100c60140403031800f00c44146941c0c2c44209181d035003528400f650b2403000c80c2d610002101410740c49101d0340c2500080310411100c0c1c525581e1601940040201290348801c101c408000c1018410800c690100c49407119107103090704219040c40c0101111450940a489409500410308600c4912000d6040481c5503440040e0307a050291610035080601880c10450200403070303140d40e03465001400c03d1030303019583c1c441c2603483c0c4002d0102e91075101c54501580701d40b40502c9a120070300c1e20300a005803402c0c1484003034110880c2c64042a514945910140d20085056280311b00c0001490b00340c0042d601c001c01c0312010401c25611107078074442507550035119405810709104404c600b26185800c03e01c041c000600e0702402da00c0702400c03c0c00742c1d0484907080440d1001002415414058404004000c0700640040e46c03400c0c0e00502500e00c0e0582212070713840301007141c0c0b078101e0058021404491010700240200c80b90900e00400e0a590083c055010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 932392850 1250 932391600 932391613
    0x70204090219080d030908070206091f030e060603060115141c020d1d0d0c11090702060718050906090a020717092d122418011406120a170705 62
    0x81c00c0c442e002c0c00c03911baa00440814076110154081c40900d071301103088640c0062003100c02c25001b40c440c0c9007012990b00923907800203803a42a21121814020041d1040344a9403001e801400445003c3c201c00300c0c5400395003009071140b82130300a010294050040103c10814040c000304a1081d8103070002c1c00601241081001074110304c010191303402031484c8240d100c0750310802c00000024002d2003907106941c05081c804640e000ca00f4001803140d1000c803580401a00010240518550014204207440301404103400b403450070000410b503002802806a8030410b032038004100106d809604860446030803078040001a0643e0903040365551080004a00450190201014208911171004100300707544c00040640112f2804002070340569030304096050040011480c96807000c42e840c0100c5005400100c640c0345044042c400084850400c5400365904014030084c1c8041610291584802e00301c65001c1d11071658403189150070b80140005180200d024140449a01410082d001e4039228a089600 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 932394100 1250 932392850 932392873
    0x1104021e16021810170c04020c0c01030e07060c030e130207110901050d02030a08221d13030e0409140109110f03150114060706052a030105060f07020409021908 70
    0x140f11104480340c10342c2c0c0c0403140c400c1c401c4500d60f061010705040454101c411880d02d042c0007a080740c1c01400c0e48105948034a0300e005180d60180650002440c40340064020319181c07450107041d090380c081000301001480503005005950340b9440d2092a1440300c411500c036042460000b04800280240900c6441c0d02000041c1c075290004602e0b02c696070280141c0080e040b81c0e40c890b80c3c2a00040d00304a40d1041e42c1c0103000b42030b00e0940b00c003030080040384800c2d842035920400311100c01c0d10151101045011a402c1c0c0c6001c00e8001606c19050070b070568001034010180d0424255802c1c8641e00210154200080d84040c000d003c120b03041450380482d40140200c0c0300078100340d91a0a454030500350501d44c00c00400111207039a40c1d0710400d0b540074042c030746010901e540e842c0c1281c0003213070180c0618a00c080110300780403030745000c0e00441c0d83d004042d61071941010f00142c1caa00641ca0306900700800019603030304540742c40c2c100300c080ca075000d005003000760300d850000d8000c01c40324041c070a076a00c1002001c0c007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 932395350 1250 932394100 932394139
    0xf030506040b061c03050d110705070e010b0a090e0709030b24100f080a0603050a080414091b0a020f07061112120411030f070618060c1104021e1602 65
    0x113003000042c3c546200700141a83e000d4034143c001014820005503900b00c114048103400d8010007010744204054000d15040c1000b0b441885010781040da04a6024401c00054a03044503802080c0c0301c909a40c3d0015545e80b110484d801c0d41981c00c010030b410885018442c0d99040c03040307815900700c01080058900205417041c4110000e509411100098800c0c484034400d03400b61030802c0e0481c020031004504141c8903100d20f0300d042e0180c0390403100720034000350801c8180201c6104080c800000c030b41024590a003041d4082e028604049024451100050a074051034001c0100e01c104a040754140d030051359849002030702101707070f454072011580030b0f4140c0325071b5600e1800111440c07083c0c01c0031250344940b1141c540c8038100542d803111a030944518280000f5145e410402800240441d43c2c6061000c60700c4c40f00c0c101402c2496110406001c00d40587c20f00040712907940c0d100c0c8050554005864005281c10f4055126001840a81003000042c3c400b1001c18400c0700e400000b03000303a83e032140380c404902005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 932396600 1250 932395350 932395369
    0x1020d0c1e02120316020313030f0303050f06030a03110a150605120a05030d05060103060519050a1418150d030504060201110a051803010204051302040905060103020a120b01090f030506040b06 84
    0x205083d1001c20024081e16080b401544100441c3e04c12207050400c80400b221040300a600140c4032074038040342400825605024040e4040f00d40c0052585508202c004a5607450588100030b00b88440040102c6095000700449e01d2415000401240c1210142002100408490050038003e100000440700d0400000880c88620750b0310800a500c2c0c40f000b079084600030003002d043ea42c101500c81000168a5580f000d031190041081c1640c44141c40c600f9080000c10010399010164032403100d000c03c122340d55001124441c100b4240007800700b640e200e4886140a00c40d44204680c0019020740c1340e01030542c484050010b0360344a40080001c2d802c0d0030a01c0717110b0301500e043c00002a10800260441c504122844600a14060300260816440348009440b2004808401c6c2c0718642c0424100070502c00e600a490f040f140a013400c501d40050f0b42d0f00100040ca8441e444a80181c4031090100c25034414000b080062a903031711102241916442c18a03100c00080c0c40035030750381d41c0340b502051851420002c078 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 932397850 1250 932396600 932396623
    0x90218221103070b1617210a0e010b030309040234060f020910050d0e070902090406170601120c090507030504050d14092103030c0712090b070f0501020d0c1e02 70
    0x16017100c0c0e031150b9078043e400c542c4810903901410240701503074a6400c6006050158103621019a403d80740c1320006604813403058500700002d80c1030808100103030f200482203445625054401680d110707100c0400a0075031840340c40c0001800c00710381c0f2000070501c19000008000c6d20a01c801c3c0001000103541e001a801790421003584281e0a40200840c64065802080391003640030002ca0080f9017100400c1c1826256030000c0c4a0320b0300010017080910309481120080d118841410101c050b113240650380d0342c00d05000c0c81c141c0b0455001144180600b03a4608801060050800c0c4224542024024003901040c0ca04036601e10071461249106400740038080a408169032016041002000070042c48080c3c0c00a1030303840010034046a10804010300040d44140083e12006c0d03520282403420702244800c440c1003030204001080248166402c41c0211054640c018801c6404006c16081c198024415100000015882d004000701c245400c403040e440e09a002e90303c428107840c1d03420f5040c0d0311a400d0f01076 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 932399100 1250 932397850 932397877
    0x10e0d050f090108180f011d011a09060a180f050c07020102060708131a040302071a03010306091e0c1503020405010e09040f0210050319090218221103070b 68
    0x40d06102c1d510600c000d6500019040c3e042c1a0466140c500d2401c00c0c1c000400754800d651a810203450854400008048100c06100200014050f203091290307200c5e142c0020a05c90048500400c3d0750796103081c2c0e220080e1550181f110f240d800540c2c0e2480062004000344118182042c002990124800040c0c681c0a0b4040e00540b200f40c1c0c0e0715400300e82d4004000c1c00c50064a850140800203d41d401d121200200000030300c0d2909403c1c00d08029190203100e0b444100c4000300c036480f0f001c03542602e500341d90440b41e020758049013040007858900e071180b85030032a005485182d016580d052000d90f50007a1700702d501d403901c95084400c51100031020b91055004207804120b202402d0f016a0402c0a0300651090180d480c181c0400300560015400d404043c031341c040064404014409613180c120040f60189030b11020420580c0315580c0401c0004000c01034603100040f040d00064104810300d040748080640c0001d2104001d819890240740c1110203100c0c0c14007070300c18082c020900c0005030080741c65211100383e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 932400350 1250 932399100 932399107
    0xb040b070b18030d140907050a06141902010507031b0c1103010609060b0304030306050a0f05060a020f030307020a1a28090618050f150109020c01020417010e0d050f 72
    0x31118072010002400700c1a008a0b40030240c1c1c1d1841040c4050f120803002c00f0b202007400e580100031810403040180c2201000e4000d11804c0085a9441d89400704880e42400d2141028107030124040041c0580e0b039140c0c00c000d0904040c46401e96040d80b01620a0075952020400e00083e4424403007204001c44051003c0350003418007101080c7d90b0003040d070000340e0060000c0341940e207030000001071318520340c05155209808810b0208050b014029900a008142e804100c00d9251401e61016201141300d00c0c1d018003070020301480810320034040315641c603c0c41c00880340ea90505010003035880038003a00695071014010440e11000c40b442e14003074010115140c3c1500240f0440780116030b48030f01d15500b104020b80d82d4940c41c00081d8a4007484802600c84085883e80c12554185103041c45c04074140001c403908092281564026244441415103283c003100585030448104164020711868101c40f1021000c204000c000d018150030031040741b040304c02965442c005040d02a5881c0c080e00c451151000000d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 932401600 1250 932400350 932400353
    0x3100e07050d0f0213020307080a0b0108040605040f060509101a0a05210d120f020901120e010908070b011d010b0703030f060504020c0d02010518060a2a0906090b040b07 74
    0x903114505020700d24030721243c20b655001030608815114058150b540110030800090f1304a00084d6204d2103042d070500c044215900002d007036150040004010340c2d50303100854103000c0b01000e101c0300541c2c0450f0410607030412900180e80c0f01d078a2802d1405480c200307280440d2a91101c2052600603002818488110381040e08018034560841c0440340b9810018282402c4100d040080700103e4000d17858a00c0d6140c3c1415540d000d440d000080c2c0140711740100304541060740d000c180c10500a50111000540b56071641c0e086002d00041c0902405c5c0b20004240301c001d101400c22410b0480b4100c2c00321603000010003c0e040e16401e0240f0807010080d5040c40b8000c0400d00a40002036a000070031000284d098840c40021301701c1c0c00140b050390302a4095803100f81d4441c1c0900c075060b08030840c2600400401d42d01d00c000c2da540c2d4001016241015140c1c2c0d030b00b40c640e00c80c6a020b1102c1c20702505040a00e41c600c2e40c4018500002c0d441040001042c05c84002000e5103090215810344588684203481d0607010f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 932402850 1250 932401600 932401609
    0x4020f270402150f0d11190305041b060e090f041505040507050a180c0219080d060b0a180608060604091a1c02030c060408030a35010503100e0705 64
    0x10000da0b049003002503c4510000c2e0f540081410001c041540340e11500030943d148211105200304880c5e00c00e0410103415060060100c2d04c903d51080e240110795a82c1d945464200040280f0605842100002021030401e401c00c0c9114402c0e1420b036001c445590300c410000c07203128030644000d044600c284928039140c01c410740001e548a0f004008640300580e0b00d00105044850ba82d10035800781400d61070000c0e0030300c4503000e10b00000c0041d100030802c903002c41e401820210001c0300010301c22500091038144072510340d040440182500c42c5280d0b01c1c0c1a480c1c0003d0601c04100d01c0140800140c0040803420360300440c14a40603580c05044182004e00b4065090000d14200140403c80b0142c45804041645c404401e044000d981428144012050744141454030000764200c62082c00c06003c1072125900010545940c1d0b001e034649400c004090200008501600d0b075590300303128602c2c8220a40e41c1c94260890342c1203e1003039007100d00103041c5801c9401104d0040705e15860f240c22000c0d041109150 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 932404100 1250 932402850 932402929
    0x120a060e150f040c210210140a0f120501061709060912071e06150801020304170306010909050f150f130b030f0703051e0d14071a0f04020f 61
    0x20801d440348625488131031080485121742244620f0034400c0d80344000f142003602d46520340341030b5418030360808031080080c02d1035406082006810014005c0c904000e05125661080c40c00758004410805542c4648004201440c00c04000e0308000b540b8010440c000170003e00310380320b500d810010b40052261032082d1f1070164041e520556081c0c40c1800000c2c86481c07020f07501c44074680304280000e0244035035541851440c60f29400034550307910600420002c07172603100d61131902a1031003010503030702d13035821740143d6130ba82c00c98001c104840d103410100200170340b111441c64020071607100c40401280d13044081210700381d102092a43c00c0107a060300c0b01e1091b503aa401c500010400202550707500d1581410991620079030f64010740385544811489601d181760b01d10020f000d00400f401030031024071507003c0688060600600f0110052000a1820034810082200442d545c52a05482c480e8185200031044488041e42c00ba07120300b050710114081403401c5071946030101c090b482c5074440320702d00302c401110720013 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 932405350 1250 932404100 932404103
    0x405010503060402040815060102061311061b0d0201090203060a06030f02040902040b1003020304021203070302070b1e210105060c0d0e04020903070e1f0b2205120a060e150f04 77
    0x44e024040852440c405010f40025054640c4000a00c3d280407000203140c0174000e4170300101c2040403890a40070541c070607000889610103884032030b40c800d02080c000321000300410203e0001d001d03207540d01001541c19005210406c1c021002c5480c242c4900074400b080b09c0c62840020003145100c241e042c014101501708a24490009000140604019011480484403102d13030000203540003040008514140850180c4080031000071400c01005540103940c8541a00821802caa0301148003105242c400f0409a800c000700e04055840e1410155002002c030040201099600506000481d05040a90076220303410804402404401078030b103000d0301d581840700c1481d41c105408210004081e2402c03c070010091032415a0f0080ca46480304043d282080d07010320450034682c03403003410031641d111041900c111014400900d6200200203174003803503445c041d900c465003085480440002800740403070300c0d42d2014001e074028060402844000b0361142c03a0403188565402024012410781d4040707400c3d60750710a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 932406600 1250 932405350 932405359
    0x423330a0f090b0106050909090a020603390307030c020616050703021612030f030209131a1305060f030a050604120908120414010c0b011e0b040e090d14040501050306 73
    0x2c03070858460700c0d440f1109070003c0f004107000081004860030031003666a4000030301c0002d00603c00743c5034001480c1b440701400c0011503100e0f4445840c040d0010500e600303801030703c030310000000ba11046c112030301c150011540381c00070924200301c1345020f90001c01c1e00d0340306140d00f12038182200b40010041e00c590f006010180c08520030300e1880c824130b10050200c4409000440308070703581c81e0f1305490300070080740c0401c08850030140140000c003c241c6401409503030904002d0004039030a20700743c003401100c19990704e01990104c2040c44041c101d207150b41c44180104800c1c1d0b004c00c0c00e5043c20044c10780d1343d0554900100325070702010020340840c030001600380e9620046e01e400000541e42c0c0e60000d01c0c0c202c074044420401701001908000500400c0078a403110341013070038501944040d0f92110240400b0502c00d1402403802c0301c0d00701c3c0c0d00000072028031001c1c003807441010f502c03180c44148051170032104569042c01d91003881c1c81049041d0007440c030b0a107030380784411555243c542000011915a040580040e410 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 932407850 1250 932406600 932406611
    0x40f080f12010e48040b0313210507110f1003090b011707090209030f0a050714041b030902011e080907061404090b0d08070b0a061a070206030423330a0f 67
    0x600070366100450040d4090001c00346090840d007800c3c020b22108140391509c246503400c0d82044035410405a4803401d4001c48005407500c0b5040100d01100050300000b648417000320703410040e040d0581d00003a80503000f11801d00d0241e03200d03456a05584508107800c029644a1a005c014030b4510790001e0042e504c01400f594a201a8284910320304841e210382152141c12810040c00302801c1c8544150001034104c2c3c042c000d40da06c8040300d51020004803001010142c4400c0944196402031002c42c104801c0601207514a60407104014107030401901c0e540001d0207100c40c0012070fa8481d5400e41615801e260040c0e141c540381c02030050040090440258102000c0005040460304410150024500a044000440c90501140b108032101500900c289010780c0c001110303081105002d58058560540c0c00507580d41f0f070750810b068118103402d007500c4200d1072480c0c1c1d017949a00c080f80b002d07201051032a1841d66244e507070300060705d014440c901039107021420100081d41404540c001646510140e2000a00c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 932409100 1250 932407850 932407859
    0x10516111507050d050a050702090709240923010c0c0306050403050c0d141e1209250815130c140f09040f080f12010e4804 54
    0xe482100a461081c0001180711400d0050900c040031a100c01441e155207045502d0b0806056800f85042c081c0c01000590001000706004040410141c01c490010700389001d0b41108969201810b1504c9100042c074408001807895040c607032070700402140c481d0300780d83e015042d801180c45101420003501d520700c441f0030010214240c2d01c01d4034019406075a450307a5842041c1007140c42c019050512004018a10048038801075040701071300d08440c000d25140302031940c00000705c1014084c55079104000c00c01441882464000002c00b003d03001d4140421981d1201c04461080c3c00154030f03ca410803a8000d00046200742c24010303a982c0e80300243d608183e11040f102d440c1c41b0a040280c0d00a8003070080c1c8545020300510708034110480084044820145503c0d16540307082c828900424014a200300200d211080c65900409840d07981d40c058036030004030342e502e1000d204090015101d00800c50741e0317024190488000001c418031601850b030310740ca252503403401e1801c01101103c803c280c0d07641d00c148000708 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 932410350 1250 932409100 932409109
    0x6020702130213090b01020303040b010e0c07021c1e12210e06010501020c04060b1902030912030d1a030a020d06060911030f07020706020a060e0a0f1407080c01051611 73
    0x2c20710f80102d0b4801ca009041905003012200307408030850542d40140200000075040e81d019a06603011440705400903150000f00103070724001da01c03000350b0029171f0032540f40408400404c089403c0e405900020400160800c24112440c40c118026281c00c0c2d201da000306c440340c001d20f50000d1074018810341d081070071046100c0d042180c0396804641d1094100341e00400081d03034108054940c200045a040052610308180040e10303118200300c0c034948080000100c0c0815000380151500d030035002d084166500341024469444c1d074812100490494508000c1002b100f05c006203280d10210b0260090141aa0303907000c20000c11101902226070b50340f03485010940f0541ea005848c145004000c003a5100c0c200207086a00c40c0c000109840d04642c00f214081005541c005514403085803c42d4000540c907030000202810103081c4074014010b1000c00300c80c41c0c100160702c00c20174030303882c2190305036602c0340e8607034540ca03481d0206402040d00080c424070441140c800c7e0362000782ea8184c4a1042203411010750303000301c0c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 932411600 1250 932410350 932410357
    0x11030d050108150123190905090d0f020304030816060b03010f0c080609090c01120f051006030b010f051c0e06070e01021b100309062a110712060207021302 68
    0x2001940c112011001140d003c80907240e01501c111780c4d80c4984004a0480d5903140a141c09103103208a20750b82105884601000800c000340c00d51400600c901d10b40305d10402d54034074030508504001a164180004940c0c0302005442c156a0301454040c03a25060803019403004d1a0213005460503959420711802035a02407080c00081000e01c040481e40851107140540b040c03200415850043c600341081000740c007000b00c3c00c500111000d0078114140c03148209100300500b0408101074502d441d1034248000d680300c0c03095103c100d54640c3e9041c09000310342c000450b115040089808045103040c030801c0506040301309089084001150001840d00200782803601d00f2000390340c030348086443c0c030300040c03841d584c1800f158502000d405141b00c11480c205c0081400024251060410184d48124040400c161600412504140c8050890412801700500300b0b0011010f810780011072017603c0d855140103c046007400440d00b20510001c0c1202c4941c403020065804000101e03845030015200d000b8030403e92014 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 932412850 1250 932411600 932411609
    0x6030b070e0a08030301050d15050406060e0a0c09060e1507080405011701030503030601050a0e18071214040807080715020903070e190c0e21010506060a020a0311030d0501 75
    0x46410308000c1009861005140d00440c0a8484440b050003811000000c42e41110400e075400c441000d01804e00e0b00415181005400d1103170704060600042c452907812481c141c5030821204081500c07418254bc0486002009030bc01050030508c00300111802885400030042019103484039118035040e0303521075580080f9048625005c003080500103540d01010b04240f038210351500c40081e5046446031a0780340001000f140c10001c00007141100988030707100310238003081c1c050500050303000318103e080c0c401907080f62181c0014203c0628080d01c04100e00030003502c40c07407801e80041a43c40342d460300d484603803000a050710400300400001000410310400c0d400780b02422503005840b42c420708105030a001d42517128016148608051000101d03018902002034059000002001081d1900640d81510082031840d4042810607480e0302c408510183d5103d0484418001c01030356035408200300150284a03001c000580c040599900000c0c001d1518000141504080781d00b0300030155801020345009822 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 932414100 1250 932412850 932412863
    0x601030e1c09081b060d050613020f1b0616140c07060804050106081f0b0d0804080307031815080711190b0a090201080a2712140702091b0d0603 63
    0x30104a109024055008040c01d000011242c0544d40d000040c03e074003d51000440560740c540118003582e030b44148140766401e262605548602c144000e18010750059034007010b01d002a0f5603c40aa00350105e01c40b4469002c0c41e03000300d800c0d40041c0782120007904043c50100c014804110114508004001400042200f961000a0740c070700f601d011402e54843d54010b11690307103c0008101d40390340c917180d45140d6440c03040001640101d1440016010742d41a80003a02c005ca00140120310104044001c0c44450700036110840307070302c010580b0f14498001e03030b129500c002d4282894044001c1c0c4030342c00e04d075009804c910b4040c070a1414202d030203040150b007040c1502744082c0c10414108010440000560141010717800700800c1c1d5042e00040e2894200030181040566240c850119414094000b07407032443c100923444040801a260003210031409200c0d42003c51410914240020380800403903502d6540900b06c6041500c0d10f42030b240802a044410645040f000d001e221100c0410b4407990005501414 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 932415350 1250 932414100 932414117
    0x180c170117160819080d0f020a0e0901031104020f0c0105070f0f02010e06150a0306020f0723030a05030a09050a0c1401030e03040b09030c0a08011a010302070302060601030e1c 77
    0x3000d5500d88141010040c0010060030b60802455802050307120000d00e40c004251400301c881c0c81c1c003000d14440c050750f1007101454601c0b8520081c4040d17000d416442c0b00e80c1c90348141d4400380810480c00b410240700003452010b148085080d01d0503e500680000780707080c0b1595090980d030419407030944074103c45500000e4180e2000ca03003030640c00080e02811002c180000c028a0045800d445c0e114034005082c444028001080e0b01059101d01c0c0821000b590410340854540700c41710007210341584100f500707803540240d0080e0a081890303510080c690242030700f00214682001c80c007042c0c8450304010654900507030f03130394032620104200340610083c0711f2281020709025424542e5001d40307515880c460354100761038250b200d0b2036860700104a5003a6841d800c0c5143d1a0340d582c0b00040c0c07624010820300c40d0010b52041000401e083d054005403906001400008410050040110120701a400c00500103030b01a0700400c860354041d034051205162408255a080090040c09913160000c8041101c000303002c50 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 932416600 1250 932415350 932415389
    0xc0a03024e06060126091011090a08010c0504030318150806031b030a1401021909231804030210020307020a021f02070e070c0c030b150a180c1701 64
    0x40c401103030f001900342015002c000030116469080c840900100050b840c01e04045080c0800c10407540070720110f548018031881031403155034001d50f0031a0184034011070224401080e040c07010b016568040026a443d541414603503102100d030000c480c0c0789002c401010641c041022401001001110b00164403140320500342902032501c1c0080003181046210243c04d001c0c802075502054460445410690440b030b034003a09a031031030081c410010410b0b2a44035000b000f02030030341c2005180781280d4010302864042540b4025040c0c9050500004943c01340762100f54000072003010300210f8209001e40304807010781031400321690072a4007d48079003015a00060b609411464240c0c188014810280801010315100c1d4501944e036a95070f0084a003250035034800a4050b9105100101c2121b0304030b04003600031641c03401d0100c0c64203070598401076240c04680300a107035030401c80e01402c126460a210b0b90340f1600b41041400c01440c41008d89001c2040707040220420b00c81040d1b41340d010f0022094421442c3c081c4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 932417850 1250 932416600 932416603
    0x40c15080711060601091703040e040c03150513020d0809031609060803090306070c0311060a0f05060d0c09020c01061208090405010e071b0f060e0105090c0a03024e 72
    0x8000b000e40583c0c401c00030031201ea40e0191168040302c1c0c03e00d9004491000b1880c480b801c50069400c40b005030710640b010407060183c803041002c200c038007411555510040840c070b0181619411a284490605141c14080043c10107941d0390111500582440b030400d10003030006402c050600364089903074105010700f884080080e209100042180c0b230010743c5494610804071b0746800e0010444400d005072081c001c005d25000b13808100008060000351034851800783c00d0400200300c0d10241e09140c614141c0021200e04011081400035508500d64095080c980240040a0b42c00900110050b549803c000190f20071007240703012125100312146512400c3c004d0511040f540140d0152808800800a108146400207450140142030820441c015132041c10443c414880f90480240040c2c60181e00b041000410350000340195002c5083e80ca5501d00c2d40108111b220036400080d5105007405001c0400c0d20380c8001884001200b85207000c10b81c00105918029a4945585d100b0700c2e0903054080c80160f00c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 932419100 1250 932417850 932417867
    0x9030306060e03100905030912030d1a060d0903031824050402091b0708030906040b07080105060426030a1d0d0b06090402131506120c0f08040c150807 66
    0x3080c41c02c0090300c91540c000969800c004685425855074440c4280c06000c0c0c1031048402c03403080034102111881503144850350325409009502901450264500c0300c2c0e08040f03102100511000b17040342d0078003994803211002458410f00c00c8041c5a5502d03210b40c0c0d07005e45d20380407030b440a010300c0e04180c1e0b000390f42081c001c90313950040002d4542d92410f03041000503a42e00c2e09094010b9400c08049542c41c404150340c5007240b20340c13140074011036808400c00016400006030244124450108510039072503202003690006801e000d425442107080c041400402c02480341d000f440d1180c1c0503100240b1307070780040003811940507924003000580c4280009446a090b0b85c184034503030318183d5940501034216111038088c842e0140a06201b1911100801c0a5584001400c28888007181041281c0c40100215000c02c0c01584075402c0818501c95035040314000324071030f01a80c910103440e6456140d01c680000c41d03482e90010f00413200e081452030041104003c5a41188002d4a16122a0954102200060132810 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 932420350 1250 932419100 932419109
    0x70515040510051e030f06120c060d0b0d0c1203110a03050f07080706110d0c08090d0e120313051e0102070509060a050d150b060c070510110d020109030306 68
    0x150821040116403160307001e08100300d541d440e101d42c591004c09844081e0280d0400c804040e00404000c2c0600d024056201e580202c034100c85a07403480d001e10001c0c584030b210b0750000360741c4000c4c1441101d0b0b02184503044800c04401c010038005e80403003181d99000d20300940f41c01041c00c0c0c00c008038100081503000240700c021000000001d10401242d603400401900c140d909200703101d0301c0443c03103408002c1c424060b660348642c40a0140300300c80700e0101d842031581040f544013400600f80003103580d140c6e0080001c24000d0003024040c0800184c1260240c800119a124141e080110300b02c51103180e207010b002520344140e0124042d04031a00d000104850f00710070610000511110581515843c3e1700051400104e9000365105150380d510140015000621130380242d4100c0034140340d00c0200300b1107110a84449198020412200c0e5400c0c0900c8501d01600808004c10b038460a170901441c80c19148401e10700c9200c2c030301650707650300c40500b090820403150f41c01e40c090703915141342c0c00030103401d40191400b51 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 932421600 1250 932420350 932420389
    0x30304060207121b0303110405030a050c1c2d0f0b0103050d09240302131202181308092b02121c080604020c0a051f090305030402010305070c0b090705 66
    0x14100350b00c0c860340c1c10640e144e00606159840c40602d4880303012000740c800500c3c00405440002009051903a1202030401c072031031140a18141d40e01012030320058621902d40c00c2034000c080c03880010029402c40190b0449660519000309030345c03002800da84070b10000144140c5002c05c2d20351651501910382201f144101c1e040c0004500284078002030356115a5600b4002c84050043c6800c1c45d4054000f84505901042d000f40b4550000c10f54014014490740518402e40700503188101107018400344039003c0d0340d40c4074484a885600004162058003804100400500000265101d00801468441c058104150782520310701018150310341490390010001c050380c00b408500f070015001400001c1100000c0c0c00b40403131407012501c903844640c180e030407401c003107001c07900c0c28459424403a03a10341c0240c6c41900350842c00d01c409036444010303008055004e076040c2c44050450721181e00540140c60000d002c0c008100e140000100441d48a01d6507034040c60010b00038101160400c002d110300b00d50202e01c900c6e0034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 932422850 1250 932421600 932421617
    0xf0b2502032d011e0c0306031202160902070809060a02030f070b07021e0c0d0f05030d0510090b100e040f050a0c0e0103090c0e07020a140d0908011505060d020c03030406020712 77
    0x20300c41d8044c400d04903944491001410035894401a00180203503003000d42100c4001e192468610340000e009080e00580401580300580d603003421400360300c550240241201c40c04e02030103006080c140c02405000002c0d0043e40d040040e812090229908160800d541d24005282440107464060007003c0c0e050b03a80f05c00c040004041550b0a035074501e0941100c500505007124403a040c41007000030111220380c0b101c2500d07500d01c0f5541e01030380545820307204d800440c422201e00151450081c41000c1d4443c002900050101ca918070f0152140c013031081500f41c10644034141d0f0074440c8004d1003001d104039261384e4009410400c180c0e0040c03410090b01403132818145410010404690161983d40440d0f26100402c016541c0d503400c102d05104000c1c50060080c040419826403107a4041a8040c048020342d580a405030b588400c1c0c603007a50b20a03031b415106a84000c07000c3c007039414035138010702c0220000040949003400508000d03265131f00172601034965130340c0400d155007003024201d81d203d4a802c051800e18072 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 932424100 1250 932422850 932422871
    0x3020a12090c0509100504110a0206130506070305060d0f05011509090809100c05070909020906041a040b12032d030c0a030b030a020406030b0906010f0b2502032d01 72
    0x1a02c4106000e01031007501803000140c140c0d440340b0008800340402810520051403003041c0800260015045071015016020000d40181d03104640d60030065040b000034112612401400e400070000070741007982140641a000d4042a5401e40320300080f0f101da800014510580680740b001c40d00d0341e4100140380c3e810211040007284129054614010003222100c030154280c642c269942c0c07054040060150040d110001203072000e580c407070002180203035440c89595403180c0401044410584c00110312701a546044d100780d0601d0b610088903000046c1c954800104125149451a0021120700500040558107400d218540801448a00000320003850644c1810981001c2d00c1c0542c1000c0010140d6030624581180d408003c407000c5180c014200b0043d00b900c03030810100501d0100d80b03105183c82020000074500e0489090f100803100b270360005034140a40310341e0b50740008400c8518203004400c41c102c820050b9500340700300b41c94031454002c02904600302114890040e0900340540d4101e902d8108000c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 932425350 1250 932424100 932424113
    0xf0703110a0315030c170c041116030c2003100902010903030f0e090a0b030f070621060b031f0609030209040b04050f1b180c0f0a05041503020a1209 65
    0x500c04486400c01207080345014910743c5003480b45500140400d40e5410000030b226075115101840120400181ea107190b10390800d20082d01d09107900651015002c11841009085e03a5080043e503900c02e241903d0140016120344501c883e0420703200205401102b0082d0051800300080700f1070521401061181d0f040f281c001800e6511544006824818112000e180c440d120701c0c60b070401010b000b410705556003069022a8010501610258024401c2ea18040c56034080000e4640c01c50b20155180070f02c90b461030794407040f01811080d40b04001d603140c64000c11041302c2080654403400303120f005007904074201e02c0500659800c540c0901d003401100783c414001358032149400f5038070540160b07031003945440c2c03440c0203031030b00e005003104040c107003c0e40c074902041d608056112480700e881116000d030992122500065044400d4034205030313a2400b000038034404004900500140034840c00d0807401c080e503501c080d140c43c001d000c0e01d42d00060360000c0d601d81804e401c142c5100120306241c03802c1101325070940c1c1c0e00b0f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 932426600 1250 932425350 932425357
    0x121b0305030915100e090a170703090501081b0f07060f0506010207061d0411070803040f060e0f030d0b0a0e16030f060e040f0507082b030b090403030c031b080f070311 73
    0x480ba45c0145400658001c00c00c000c8001d0b516480811310700060b100340c030310034400c0c0c20414084001900c1170200182c150720600945024901868840c410002d070507824407055441482034450b40c1105008441c04600703503200d9500c01c00e0000310042440d2404900080c1000d01c250040824010100201c0303c40c94071880d44804a05019640080c203030304440c5020744c0c0340c01842030040c890400002003100b0041d44404a80000d44510b10a000c0e80e00d140c1011a100c1d48950b6030815258803c1c00480382c11300013600003805854000d8100020144c4907001c4c4401507100b00d40d408400c40c07585041d821640d42c184180c140145d00c0450400510303050884102516070050b1000e0242d941e5100d000c0c045c0b0005000210083c40c4003412180000d007000700840b44c030100b0010a5120601d191503402c0064001d0281c0c0c1c84000d00103240240a0f9107907903054005005005d100d404060342c442c440c4803003601c41d10000c0c10a01c1a40c440090503d0100b05008007041c0c01030000e805c140c00d1090103070740c051000042c0c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 932427850 1250 932426600 932426609
    0x27330108011b03050907260606041802060708220e09061e2e06120b062b0606030207050d020c0f011101111b100513121b030503091510 59
    0x100322500c5d41140540340031016008000da101040300880b070103040c240f85064445100d035082e5003240d65403208201c1106d940c110801c50303c0c15031541d10b00051802c54000e109103440740803942d0030f0520484a01b03402243c3c82252954800103408140050084100c03180d600004a000800c0b103464840d88406041041e000b43c6c43d044150580071821070103040c0c220350f424240400747c0c07138000340740e070440b0300390f50905441402c2c046141c101014210400502034000e4241001e010f00d4036209e003510000c200003c0d1005001014078521480d803290340c000d401800000e0086650158680d44141425424403070000d1b050015503201425004141e00c0742c0e0320004d082403090900201400031031480c83e024005410298210f44800202c1c80d2408526058108800c1d002204503100c0301038040556080703a40507030b550041021803d01e008005000741c0d07410001c0300791601c0e00602074103042e00680c0d0703601425130084000c181c011080020042003000700c05a41158800494217604044030441c1031800d09024 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 932429100 1250 932427850 932427857
    0x3013e09031522050d1116060f05120c090a09140c0918181c081603090f03080402040507020102041a0d11160b01050927330108011b 58
    0x10b04046509121034554280100f2800300b0301905282032070301c031444581c0030404580c0c00c0d8607058031060002001c08800200c6045075154604181c3d0988a8030781c01c0321100d081010400110100e04c05030b22004c1d015414060102e0340f0380003950100070312028107401c0100b18514107010200c544a60004603034001c69504d1b01c07141d41d03106540c0800ea0482001106681105501060090794460308071900d24503103400043d11541c817000143d12142c44031a50340c000c00600ca0710045000140c042811038440d0700f2a09000440c0b0000b035843e000004401c0c407041d03010541840030002941041c0c052240d02900b6480211315040c10304c10b0150408030004c81e0106180c0000c00c05021900c0b03076611811001ea896403016071125810b0214191820388134404903024240ca2000190506001140314000c8500420030345030307440e469410070340300082c11080740828440d800e43c0041e601c401c5000d00045006910006c0d160703514900403250084410381c060303002c0380c0c50700f554110444074907030100351400320324035 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 932430350 1250 932429100 932429143
    0x111060a0b0105090a2c0603070308090a09050a0b030714010c061508010203131a0106050316090e0c04060329090c0715090605090703020102100b03013e0903 69
    0x240100c0f040e028500045800c62000000410030310b070b01030854100d80d030a451610104000080000d09052001d41d1000c0d0590320618042c000110140d014010001000d0f05000340c2c107a4500f603000507104242d0f03019544c070b90303141c400711400c1c00d041c08004003520406a08010700e15440000801e0350b04500400760034541c0d81e070003511400b0402a852402041040b000399141c1c10082e58a180c00348507800e084542542e560072862054440c42e503014121390480e11010f04655490100220040f1030080f240108500c3d80408601405c1c503026285c010b110206007183c41d5030802c000070302111070108042d1543c04455450380003014098490b00314004003a81c1d148110780300c0c000174a03003601800d0382c020801e000840c81800d440c5c401e40d000c0c103a6140583c8083c01182c548407035080d00c6030307080e00000c1d0050f081980d08001002503a0401c0b1080380c0b001c0c000282100041510b110015414824001100320f00a4011a65901032401c20b002c0e421030311a0500c2e14240c600029960450442081014100c05 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 932431600 1250 932430350 932430371
    0x9140a030507170f0102040b041e0b070b070e0307030309050415080c040b12010c171e040b100b030103060204060f0f17060d0b090105040309121119080a200111060a 72
    0x184501c14440c2c5268009540ba183c0302e000702d14030b50708a80110850550003075011050031180f81c2841c01290107031440103180103040c1d10f5100c4dc02130001e0848041c04607800c8190484e807010054900118044c0d40c41c05c98960610003003105075000740d007800944210408082c406200c01088000d440c0008903400146040f166001c20300c9650490403005680d460a072001d6071860300410600118030b000c2039280c0c21642d0b4404400d4503100510f00e0101c0c1240040006400102001c149540242032074420000e9265030f418a2519544240c1080fa18140c020604000c4123800a4507549403414a04010042e10365070301c00200090b407042c004040e056140310202d103c0784c0b580010004102e4024041c4040c529140803801d000e08415036003240020740c00a0001341300719044130344949095101215083d050200300401c0882011140c038100c1c1c030342003000300040501c0c0400c042012640700386252000c19030020f601c1c03892030300028600c85c18003281d01d41d80003401e00041000d65010340c0d05203001030f586105 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 932432850 1250 932431600 932431603
    0x1030b330307020105100501030e0a02120304050310020912010902090a09081603020a03080601050f0d02030406060b07031101051f06030c09090204060509090a0e0c1e0405040309140a03050717 84
    0x3005814515684000244041103506401251051000032216031a09580c0d40046044600940c580c62075070308000090070040c5404c0b1040c003032070f00f1300a00712400d0070745800000341010580c0d030b480c0c2030340c40c0d000950390b50901380030510000c00001200200161445038010806040004111036a0300e2f0f50703000c4070003c101180d81920680d01c5014054000e0f13042a25000c0c0d62141c1002c0150081500100012095841074040f520f10f070542450f250f044c0150040741c00c004e500003070011100c00341c4454000c2980320402020300b800310300a45d191404480000001c41c00c40e000902f00070098440741194244d09201ca05d00f000865a007454001019000c10310201e645002c1c035041042c2080c000076002a2950340300e0090b0034060011210420b141d16400c4c02e04c01111801c0c5072000064210035400001c6160001150800c2d920000040074060380c0c0b08000b80c102d5104441c200e012420000d40ae200c809202a0f0b41d00f81500c003500c01201542c02c6403229507a440070303442054112540c165022502200 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 932434100 1250 932432850 932432929
    0xf1c0201110f0d0503060301050a0c09090e0c0904030e13090803070c020f030706051b03160b061305010b0d0c050a020c090c0c070b0d0506010207060f030506010c02030f01050a0b01030b 81
    0xc440d003a41d0000d074103d4802059a4400e481c43c1e440b0390309000200d05540c02c60b00c81e82140c80501c2e10350003a218503211a0303201420402285464a0240c600c1420180e292401d01c1885144a5500c2030320089001c820802c90003c0d1098007115185850f4601c1c0006032141c044a4000324641080e40c031751341441c0300040b40c4075241b0002c1e54044c0943d41c17000aa0340e8014015194410006480800045805000303540c1d0f4003400b041d41c0c2c0318803084041c03140419003000c421500031001400c50007400d485821a1300030356100f85c9c0a0b80c11480000b40c0300d0072142ca14405c5034884c02c01ca10b0024503100c01040000c0d0b641c014020300910070020780010454568800040780c510a246105440c001940d40394900c50b9600851507040d001818180000c80300c0d031020420f40142e82c3e19449840f81d40e4051401100241001041a4103020f0004031a2015036030420440d00e52200e044004119494440d01500031b4590392480c13241403509001b00588683c1d214804218500010b06009105030480230110301c1d6100e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 932435350 1250 932434100 932434123
    0x25060305181b01020c18011a1e070b0f0c0d0e1e0102130e1006032d0504030210020408030904020304021801030c0e01060f050f090a150e0f1c020111 65
    0x8101494150031880040120070b00880c2602a0348511030b824060211b20400200441d02c03580440d00140b06c5088048800c0c0428803085040d40d0402038040c05d42a101840707440c040e8803c8c000841e00108000501e85110703400480000a45a54140340742070014034001d1040c40c0f181a1b03115001105140c000b00104403146a45d8a900e00c41d45482e144028000d41c80050750540040c640b12001c00c58440d038051550051b4800ea80050305e50389800402c130000d04801f9a40691800000c0650340b140445117400782e0000e10038140000c0b03c0c28289006031a2418440d800c52a0900510081106060100584200302c10035280035a4a40c1c2d1840059031100b01b400440020b00d40c1d00f00088103009200c8000400d40345407451519290343c840d5010380342d40140c0d01d862400141c04116024040304a60054414624080c100742581034564050f00d20380c0c0e48940d42c020000303054505284480c500001042039412094070340784c444402080c0a201e40c2d0500c020040e0520121041c00f40d4400e01c00c101404950 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 932436600 1250 932435350 932435353
    0x111306030b10110f100209040b09010302010806100216060807110703080406032003040b04140a0b1803070c080309032e020918012c1e0a141302032506030518 69
    0x446041c405e80300940202200602030b9141c03060200700c41c200186400c6c161790701615207034000e0742c03643d04100c0d4031380300741402d5801c42c041c09142d0301c2c1c42c40403c428840a441a43c0354800b45280004004164400101600c020782d801030108101182c00030b01190199801c80c940800c80600d81c0c0c10f102e42c0180000c0c1d400013221000020070051105141555002e18450030f00941501084400c85030b540001c000007900c071403000c00114602656400b419608681c030301c001d40381046556114010300c410a50300c04003003500005113442151900388a8030504180303010b40090320709040d0780c4c610b014500802d18910031550008841500d56110703040d002d1540303496100701402d582c48102024100d0014640c00300c40a101591140f04091040c10741442198100740200700c0740300c0ca800340031030798002800721500c0d2540c5414062603c016110004d10849403c8999108071540344141441c240d0350f04928241c440781c0d82840c00404407900420400c6891710702c3d000c00c4548a20034140d84640e80301140809a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 932437850 1250 932436600 932436613
    0xb0a0509070f0b0c0c09010311060d0b040f1a010f050f0a0504080f010c09060c110922260f0d0504030909060312090b090105040b03090a0204111306030b10110f 70
    0x203003000c40006003404c020003001d48405103810424820b1b1000207000042042c00380c2c844c2c9401c035050a0003d8020102d01100c0410301e20035050110b4101c2d10010040401c5c16112440300f12411400d00764844214401e203044c8450340c0c0c41c2c0b4001421409415410003501400103010b41c0c40903c030300d06980280c0040ca00740d81d480788510340702c079008103040702203407020842a84000030107a001c2c0601c060090b8100140ba44901900c1081043c2200c00030311000c0e990303040b1441d240541c41c8100390100b41500c1800f007410b00001e42030180d218150200041c01815100f000001c0c80701030502c05849140210140214540c2c865150646105c1600e07046031188a01d001400400d00c054012103030700e0500300c1c0d01c4524669850740b030400c03600d200d8851828040358040008000c1c0480c50301c005c40d0b0018105041c1e0703010b940c1650014003030f01d49090000e04d03000c5001c00c4001c000344010740200020041c0e41010408420314001141d201910501040103200d0564030b258500c60050100070686c1d200201500d22 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 932439100 1250 932437850 932437859
    0x2011b0c0e0a15030c0e100f080a060b090601020a0f0f020303071203181101181508010515032a0c0111030114030c030a061e05010902030a180b0a0509070f 68
    0x49440e000c40c0c007a01282d08290800c0c00f030164000325602600d400042c02002c1c0c40c00d200701103410a102400500c00c84503642c00000d10003c90741f8858000d0446000034107080c0d8050f040003003d0703840c00c2c09640c0c0b00d42e41200502510341e0f0005030100b05c25600100205c4a03143c2410810710620282070f010b90903010029004003003041e100042c54150320f103a2003c00010501c946400c4807c4030b9000010701c1c248a0702100c91071076025091417a035844403594880318075610741f00488a01c1c07075010500c0340800e440c800180030034038042c08a001c0d02100c4009e07590440c9800000c0100c2141007880e400c00c2040d1188842080c55031800c1150001c111003002132040755115900013409620074400c0311691a00411120300d44e180c0443c8a40504400034001c16158400d6290100100b0000c4181484c20f0401c0100700c007851b40c9030081c0c6008040c0000016140e1074440b6100c001d4403103c05080300d0f8840e406d851140003e1a601c00316403c031840c01c20000700c039901d0702e9060b454540c1640240c3c80d41081d02e9000607 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 932440350 1250 932439100 932439119
    0x1120f2406080303040f03030f09140303060a050d0f020607060e1510060306060203091504121b0f08030a08041104060b040504111617070c06120b09070c02011b0c 71
    0x603052106202004207959400307005859000c25280141701507108010030001c01c2c8690442082000c0508000072459125601c0507000c41031074401401d260804010000640303008021400100701c1507811803a1605a0f41c0c645000000000703000b449a40b010801e08103000321036028114a01c0c480040307600c905061070f90a260003008940348100e802e01510081183c51080c000d0b0000c581c100c0c1c00440c01c0080c0f100c20000003400864021006001c18032000845600b14900204481d016804031544051070042070880c2030300542083d100800d4101c0100035981000003180c5219281c0d00d0b01d20819140c520303100403080d10512140364882c0c10441c0208503138410030020300480d2000c031070070080c26000c4000c09d5902e010341c01d0203201850401c98107801007403c07040c2d00503010380c16060fa44e107800d0940d607230070901031070315000000041c17160400b50f494000d442c800e01c04420011102d5030312a140c8400014001820124000d04001e8410035017007030006172500c60340c03812340d0017004560019120145070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 932441600 1250 932440350 932440403
    0x1617030c180f0105250b0103030503011809120e130203090c19030201021c1806080a2306120a05100b01090e1003020d1a040c0f050307050901120f 64
    0x18006a00e28035100c07070540c030700300310344401100c410b8540e1070905822001021400e105840b800f080e176400b0814030400501208507003806144a6110b064803541070010b030099174555410750007084e46c680010400461030340c843c44800d4400a00c2e10442c03030529200442c0c101c10509201c02c0038076001200b801342544006c01d4007004108161140d130300d900c282c140f070004180118440079016801003050032000564400c0002040c601038102003184445e04141ca00c0c41125a52200c03001075801c4081c0142c6220502030407030700054500816880301c100843c070f40c04450700900440d105880c1e044485421000c140800c501c0e803504075045c2c41403050032508110103000c0c40615030380003441004012445240302e0030920301a4400031024504a8110780c00d03c07110011032201520850346080f11101985460701c40c1e0742c840c40c07190088900c1c0f14640041040c41803017940041d032003901b0901c0148036640300d003102c40b411240c41641c1141084568200020103002404024007c01c181c1a0700903c10112580c1c0d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 932442850 1250 932441600 932441617
    0x130506041109090103060b180a090215030421181d010e01080c0904031b1202010e070e1303030605100801180c0c0f022101051b09061617030c 62
    0xd20004801d40418a001d124080025900c407201c2c0c801031003c20441d5001d00344280019009500d0528052003600590000311012058107440b0301042d011818480c2d5800a240c1c2c00c410858114141507891444550000441c11040d0766240c5c59400c0c04e80c0302c3c5c03507081503003161a44040300e002e446c0e005000001d11040313501410040c50341c0001500d0400307081024104d50205015100c6030030000b08204440790b016200307500b00590900c6218445070441d070150b4001d4881c80054200c2c1c03240c0703d0040d0954042103010402a04a070400b00031703001c11a500941d1041c00921154810060752500354010700d1550861130304540c1a5004021840e002000e0f281a1652500c4003c00552580c0000c01a81c7e04041d5032000101c020111400040752140000141d0b0b2005103245e010f0788a060f5051803560001c50f42c2c08050307445106201c0480701d401c90805200d007190480720b02e0000c200000c03440600c151a282603454203803000320b2050004c07480140e1025080c80c88086e40da82400c107150030b115003080c1003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 932444100 1250 932442850 932442859
    0x40b09062b110f01110d0f0306030204021801030f0b0312030615030907030c0e24150d02120f070f0f050c060406060314060103150b01020c030604030c0b010b1612050702130506 77
    0x4840c0c105601407000000e117005030710b00925001c1c5142004999503c00035001c4401d00d42c81e0300300803005a50f2800588031044182400c0b00140c08003500040170340b11020700040b0110b14010541c4080d440100e52041010070f9034803002e60343d8032440081890001400c4403001541004020f0100c1900007113600c0c02280d0003122074110765512518405c51101c819201040300c06054011204000030509c0c400b408080010517070640c400c0d50034850592944003083d1030204590001c2c1c40c2c8420085455541d0300001200c402c00c4081ca80140d02824001800c0713421000d00010b00d0f0303108a20761050f000c403102c0390340040544015040602c1c0c4400507182ca400125150132301d2900c07518400600040c0c2d88e04807a00000c1108070302900b201c111000703200308980c29045001e85a59408541c500b040840d00842c4295a00704802000f0b0030030140c6039106070003240140c2010069a241c80720110505074000f41c06c00fa803440c10782448031058800b4441c028000390886250341204100c00e58942c03141c4d1045000b40d4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 932445350 1250 932444100 932444119
    0x6070b0709150f020318030a02120d030f0603021008092406010f030c0e21070e0610051e0d0905250f0320040902060301090b040605040b09062b11 64
    0x840039250350b443d428090006078401c0c071180401d1714800450b104490b070094152880b100f10384c1c021400d90840c5200888040d0b004104c00c5242607030501ca1043d0320390b44440704001305400c40c2d000179404030030b402e41401000740d68008220040c1082c0700c00d032411850420b2088000021148010358180125192400f00d9181041405a00d0007401030b5003407003100f50b8403c000c4c80c04010030443d10000300c001c50582d02c0d00c2010b580110460400185001c0c0802060381055840c040c02007110007400481a030003049004d02c02c400c5020340c0001e10103230552404440b181c07a800801c0b0301100074403101d8009005403080f00120104245101c414907804203c000ba2900041e440d0f804070390441c81039200080600d040100c9104048a5a03d4650fa207150000e0000c00e0b0a002c41c0c000410b10342081e0003210b005075442c8481201482c00748540002460185c50902c0022214000506000130041016000b00443c00c96240f0142e5042508424260043c20349003450381c15003004c600350307402401800d01a41c05032 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 932446600 1250 932445350 932445389
    0xc01030605011e02011b0e04060603020903121612050a0906030515010c080903120a0f2a03020c100f0212040b030c13051c03120e030301090b06070b0709 67
    0xd000e000180c540c1a11030048840302c81e84007024011440b041201103558516141404d86a20303195401460b07890f070b4942d904212014100000c94040e44c0c0280b0500d0f00c101b010100c0c0b034034003107a070303e1641e28010300d4070380c41e10343d000404041d071780d28440014110f03a10316034103000b6160494090580c14909543d40784500e6280c540c15412100162222104601481481c0c440c0f9031240d048070b50807038407801120781050740e85000b0a2a024407114030209030100800c002c09001da01c500c10040300c1005240603100c410a01c05410b403038a05050007804640890019102458001c000c0008031b0500504842206112410700030903155040c105000140200c01100303400e10155420b44050b1109800c0711440c60f110b400009402c0d81c0170030f4000d002c01354a4000001e1030f580c2c4108500354520400c1121422509602e0000c140041c1840e010180324903040202c4142880001903a05565410b0400502c03860b000001940c0c0d0f00071424024180628035080120a40e80b224044007101d4900c1118181d03444103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 932447850 1250 932446600 932446607
    0x9011d09013e0f07031206061407060912201c1d0315010f060201051e060d0b10090b04020703022e0608070f0e040510050408040302030607030b0307051203090f01110a030e01020c01 79
    0x1f901c16100021506504801000a098028941c3c24820100040d002000d46d5501204244240c00034002c9001c540e5a240424801d0b80d407001c0c2101e5040242462600d006c0e81024410b0f40700108208004840800080b003d1510060a1601078005c040b1503000d80c88406202e18081c0901803800707078504241d4000345083c014000c29005001d441c0102c6d4102d080c10102030510003009066070382c44440e4850840c00324003517030980c034081c44410200c09400341c1040049401d8070b00b01002e05000750320410102e804a5404549100c410891400c2540c02c1c0080300c613400b8440c440032080b800010314080c4000390400000078203000700e41458a050074900c1d41d03842c00c00203680c0300b15409002600410802040c000301c0381e002c40e511501c5250a0790a05032a5000f0134681501240c1540110b03640300300041e1a071500b040540014081142ea400f00030f1801c005107030301c031701030810340600407448420244a268000e4070110707580d000b80700480740b0750b600c1424000d201018a03404c09002d40a5407030704001c507512 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 932449100 1250 932447850 932447861
    0x5030a03080109020304051f09050622240f06050a0b040e040b0606040b0c0307050c1c060e010e0102130f0e01030f03050a0201090209011d09013e0f070312 68
    0x1015262100c00303078039100100f0069480100101e800d401982e000d6000501c00c0c40c10b850b2003c8a14a0006210440f07282c00c078606900900340900c0d42ca0071070004c0841428401c42d0840040e482880e140c06081c140c500171032402035191000150a040c01d040049041c1e1681c00802214030441c4d1101d51680e8030b030002c1040e482540201560240d1740c9000401007800e00002c2c60308420302074203c9240ca6030702e00c8010016080b115040320b403900009243c0042c00340400504544e00412990340c1c0c19514529490500c458070b030358000f80815112428210410700031340c03000c41200b59480c0255030714005400b25038501d0b485401040d201141c030240120300700c1410807c20b410390f80c1c001e0f03400b504407200392420381d0250000400700045640303490071000161110304029008044806031142e4800c04030105415161005010250507031510070014620007002c07010300d840000c2e0b0000450f4400310100ca0f0310400c0ba0031021f10b4800880000c0b040501d070700040c0144503460083eaa240000862003c01c50195034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 932450350 1250 932449100 932449103
    0x405190801230f100b0c030702060d0e160509070e030c0619091505040e0c1e03010810050408040302100207080106060f09150c060b190b04051c1a06042403050705030a 73
    0x4d80c409418000d22044000600038080020201c1c1c1c00c007141390380083c280758000513801100c2070300c0e500340c18a101810030600c013002031340000603081d1900f444042840804028001802c0081022440003181c4090154216903180900002e69030340788440c8011000084200f200c001030021240060080b9041c107080216400e10ba03038940c5414a04014217480f10000740440303408003010011000d20b17030205243c0c2d039011580701140d0341c1c696140c50381403802c0c02c11110800070351340d0a040410000580e06c008840503240c2c1229000b426801c100d00480c90111241c006280e59071078a9804540f65802000200081145550f035800058440d034001300201e0740f8644030b0012410410341c1100203040c030b80100c9089407024002e01f050340c542c2014541402101c0d80403086c40c0710004ed040c400c0f414040c0c004884624898081190100c580d5900d07241c0e1455611003481c40b00d03240c00440d21954494004051000c07010040469500f0650008103869a0520044602e84500b5000280d03a040116229000030b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 932451600 1250 932450350 932450371
    0x4180b1e160801120c08010903030902040b030c0a0e1e07080a150605340b0f220f0501181110020f190c0509160914060405190801230f 59
    0x380d280000c4d001c130000e0198400c4038140b800143c0498042d0092091f403000078060398000c500f1540f24014401200c0034416101c0c06a0000c142e480c2054552240340811129002c031207030b140c6c0d82c54811195400641410300311504550405104400d64003406140c09400c0c0b0003801c002007a4200c080141106c400e21035a00880c205000601240d015030802c5c00c44104410054040540088150034404031a8141200d181355108188113031507a14120540e13000501c4400031341484039070426440041d8641c140102200030080700c140810000390805007500305500026460508645011002482c509a2482c003e02c2c0140c4800b0782c0c54030000d0081d417078040d240c001d0301105071842e44450b02005440015200d000c240540020075440b0904490b00c20300143c01c05050701030301c401000340080300c1031703210802d81441c480d49042c043c0c0e0b9a4080340d0840d50111507001e20800170000314000e07158642d218400c19443c10060708581c8444005600c80c1c030b202e202c4090205d41c0c61102d450215030040e211100070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 932452850 1250 932451600 932451617
    0x603120507170a2708030702120a1b050f030105060a06110319050417160e180706020f0d02070f0b161407150806090604180b1e16 57
    0x69000da0018800c00740240d03481000b0391624036a0300090f40c8a4078906000500380c881002c00da465450400139403501940440c0f0446240140481e940c0c040c204019224142c0c9030303651200032504010032200103600c503d00c90b81c0b00768009045014401a0700c02c090045011411240c0d4519042c480e00c0d204800007840c41000310301b0b00e50202c0e03d0192007401e591880c4420440540c0c01c0031224003240280c29150303202907545007862400403000b40003209030001c030345c00030703c1c207010300d006913260301e4107440243c4181c0c06141d60703540301c1c401408a440300240705805007610100303000d40d02091004802e103441e800c0311030038405003400300d9480b000392140c680b03030941c02103050280811186c02044984072240030442080c10700c0d150300c8012807540040d170308181d0240208104040d901d00d422070300007001e424500b140c2d03c0c002d404107140d1580201414800e59880d605030b42c101149024442d0882e4104001504914112150002400c510280b1804006070800006c0d0784100c090401c22240101f61b03641400d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 932454100 1250 932452850 932452883
    0x712230d031b2f0304080303150406060c050a08031320010e15030114030c120d082d0402130c2c0a17030909040503030f0c0c3307051c0603 61
    0x10120700110443c4400c0c0402c000c0040e40b0403040000e503009078584c0d80840040e03401f0604110498442d03600c84001d001c0d4003460031002c903030042030380003510740c208851941d29603130810558060007841a00810401c0d400c141c1c02405580030b41c148048003000c0e00c175640c901030480208050784091405401c8103900400040c45011040c2c1407104040401604540c0c041048200250b15407110035080708230fa6001c106400120ba6020154581054004120000c010b01c0303440a00403014202c10711020400006005ca400c44d2642c40d003e0704501e10001702003140c900103400041095200a441012400781102a20580d40d49242406e0305d030707034004121520315841e00440384800000d4081a408500080c0844141615901c1d00ca92145219501440c2d2b645424285001c00c401c014105a83c0820705000c0c0e801408030008840c10841c4141d140903000c072103011741415208440c605000320080e00724083c020b038650883c000c1e1103101130b000f12110101c1c0300d0307000d00790440740c00e40f0024100d026030b109581d0b03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 932455350 1250 932454100 932454167
    0x20c010c1803020f060f0c240408071b350d020a1506091104030201110d09050607150c0504180e030d05270d030e0712230d031b 56
    0x140c131a900a800241468a1005000f00907000312903105000d8203c15201039182c1410802c4640e0080c1c10b0160580ca420a03884680c218041c040e402840f40700042070300b481580d101d241141c000c0c0003100e11722180c954115540014000745281c0c0d01c802c9c00c000c4441012802c0042001e04405015900925001c002601c4643c080c104150962100035611034010426440600400304005006040d5070340d1249584001012105825950300340d942020f4803102e075840e4064054001c941049604c0303130b221401c0b4104000488010720102c3d132800e24003008001240e400c007001d00212049014a07864420701c5012907002d580c400360030581d141d081005143d03500101640031903080342101c0c040aa00c04034600e80e681900c13080141c040013540c402d400007100254140100c0310701103211800340a565140080c04000a048480010000c000c001c070414602101e615598903501c51403002c50b012200f0391003014001303042030220030384600090178074145c800740a4851402050403492110710901007901c1c421 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 932456600 1250 932455350 932455369
    0x133050a290f040b091e0a031103010213080105040b09070e060405040809100c15020708031302040b0a17060a181b09151d010b1b0a1203020c010c180302 67
    0x3200100244039242d21040000040d0002d402c0b02618181e80c0c480c0b4004000300351492000070000d800c440c0051402c2501c1d403e030000101d943c03105450880e10070501c0002c0c0039000c1c8421079442900c80b44000104608150030080c000d41c0135241201540d2552001e20b0b031180418007440c640c1d244244082800c606060380b1896129001d10000340c10b01c442c0000207607030b000b808100040001c09182c1c80300d06104020100b00780c0d44036040021440c0280a07a200443ca0000400d14044a8428403149043d9100c540244030346030b20048c00c00d584103407120041c1000b0f0200b05001000d500ca040d00044500078070740f045007500134100440c0710a141d0542d5424458800ac80c0c1a8811440780314000240050140102241c4020a1800c10009406c1546000011340590340034010b150207000100f105001240407160780580180c40d06050040e18481b9515141e0000702c02804651201c1122080a60550141104895000082c011462034920440d50a402c0035050400704800c04010401441d115904 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 932457850 1250 932456600 932456669
    0x1020307030f0e0a060305090606030d02101e14040b07020114010510030e06010611121905070f0c03060e251e050a03230d0509040e0133050a 62
    0x89070314524101103101300c107096100401298550043c0440c0d00342c1031003410b83c000400c0e0000c040400110708025515241c00392900103a9503203c82100e4284200503075000c0304a9414424415884401c18180e1448011581655100881c9000c03c6040b0f206009104040c200c100584205900b083d0800c4a140350078003165052655074060503107814400d000441c000c18140c6c81d13001c1c0c0450312094850421840d00c51901020703108100f0005e400742d624401d0b0102c450285071147c1c417081d652502c030713014801490f406021308032906400820087c080e04010641c1c240c4d034054440700c582e9002c1403920036040c014121071900e0103840601240ca505240b034034034031440011402070307241d495020882041c02c035042556a0040080054a030620f40814688088621030041c03100f1100407500900e64002c0906d000d1141c2d031145c808060000302508a4200b042c40c0a0b64403038642282d0103210f15203011407054840d01c1ca58220005801d14007040c1541c00c40c1e0703c240d01b480444010484e00d00800301113007003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 932459100 1250 932457850 932457857
    0x1030b071b05010507090f0608010308040b0901022b03060e060114130e0f060406060801210303020f030f060a1401080a02033705010902090f10030216080d0c080601020307030f 77
    0x1d0700c02040090080c10701034100c641b01d0360f451038100401102c04510580001042c00203070f0004200040816048400720341c126280c4c5a26000c1d1400101c0c02c0c004d1926101c100d00d11400b1440009000c0d003a401c009110f81c0d500c1c100000340ea680741c14010b444044414a02266107809400841f8090400078507908281600113444152200569090040295510403210480208021803814a40301d100c001d01414145614950303d00f0707188081400300c010032040491001c900c21810903000760150342220b4048148940c0340e1a00040103010100c1c2102c0b02c070320444001800180c6918403451021004e2010796030083e49a0f903461a0b40e0117544046d04080300d8845d05c0030f01e491700042c12103601c0181304c0902c0000070001140f5982c00c042e28030603000400420b104209503402d13503403120f4a602101c0c0055680c50100b483c1204142c00030b004082d900824684010700480070450900020645000442010420790402010840316804110390b04c03405030b4030400c40d02c000b0a01440288080240038074 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 932460350 1250 932459100 932459147
    0x1060f020d1d0303040f151e050c01021207020109050c040213060c0809040e030d14071209030e040501080a03020f031e030a060909140c0d051f020706060e091501030b07 74
    0x8000c04e01c2e40d80325500c03258001d00d0603a810700c03105644581d14120250180780c0000c02101480c108a081d00e080010001403240004208503611020f4060b148002070b404000c981e5842d00e1100a40a05181c03103048500f40580c9018041501d410310030380742c800c1480040801c44d1070400030103513200342c100142075a110b50148080a902e0b81d45000c0e4141413880c5001a5403104a50360348901600c01080000b9003c944000421001c01d52040082c2d0440c1a00e0030041000c01c080d090541d03014107040c60341034115082ca0000b0801900000d0a15103140c0f00340c0c21a601401d0390002c0da81c030f900510700123620301817003840b28441c40f009040c041d40d044420701da000994039644050000843e041c2000448107403000180942d29048240f04000b010401580c003011220303025595140c5840a1440c41c0040260000d0701010030400c0350305a591855000e081041f4264a6041006da03040d0121243d0007a8494031321007080890303441c0300141c1280d40c0043d019845484255050b0303241d45003000c042a0008040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 932461600 1250 932460350 932460407
    0x50405060403060207170a050306150c06010807081b0609040b011214040b01090b0f040c030b0904050f12040605070807020d02060d09031409010504030605150901060302040e01060f020d 81
    0x9038014401903110307000040c0c1d1050186800c00f481013186000c0c12540c141840b50b1507100d50420304482d80203100b103070414442c04201400601c4ca0240a2107191503100d49000451404800100c4501303aa0782c04080355811a80718801c03081315602800a917400440600101603c0c6c00c282d0040c0240740014101411b42400c0c50b0114000c035800c0c3c20320385405e1507005c0c0a03c0140320062442c80d001d0300b4510828420b80c0c00070b00110b4111000d01208500440d0740d545c03c00e030140c2c030a074840d00b02d08500070650400d03824603060142d41c0b00d02e064003101480c041c5a012081c004034100c111000c82c0d6080d29510300b0400c1d1600c0700c81e501d42100809a030042d01c0b2200c042c1c01a0340e10001070403e0404154001220151414000d080840c1107807030545c00002000020050781c4c200f0103a5080300c0e400031001c1860ba80354044d002c2080078040720303980c0090004002044107501034010f03100b40c03a070311140b00803568de075082c04483d400f401c03040d0080560012100ba403025481800020034060119060440d0000031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 932462850 1250 932461600 932461609
    0x19020f0d170301061d01020c0d05070b0705030c0705120a0807060f021903050a0b1c02030f0a0311010b0901061218051c0216052b0b0709170105070e010c0201050405 72
    0x1030403407150540c000001482602c0e005141244000000c0880c5100d0350344403000030f561280c0101403c0c2c860402c3c00802400c115042104101802c48440401e40740c00c4075180c25590703500417101e82519401211340105103420002c079010f21103145000100f083d10255107540420394000341c01610b04603241c602d18100c03284540000c0c076415403074203595940c1200358207009044841c003400c152000c3e42410b00c040320507582d41e08551000000c8100d58a4401c030248002443c0420000000040d030080850f164245904038904000000002c802400548007003820040d558801f4020f00010480841d00100a9a2268000103948005800c844854800d584034503190035411450780342400b00709640750480b2603042c410b07030348466800b50443c1151030401e8005080303104035418000080103281007540302c0780b02090003090020b070801d4021f6110300381031800402d078440d540074909150b10000701e40b1006243c1441807501c52905a40e9004400a0360001152840340c5510168100702050201040c1a9207 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 932464100 1250 932462850 932462873
    0x303050d0b0d11030124090b0a0810050402030d0905010c11010c0c0b04290f0a02070b0715050702060907060806030a0209010f0e07140304020108040614070804110319020f0d 76
    0x4100700c81d001d001d440f0406003540ca5400b042c10100034083c40759805050f480e011502070314544000400e4150790b880120b84140c50030b03800b91400d4801d5103603400b10680f00f81e02050196000380c040c0c41f5103a40050040c3c4080410b48038650010740300d007010070085010031032003a40038101450020f140c0c1c007a6440b003440c800b9082e00f0004100e0400101001007011030182410800e5040040c1e0711110194207044441d4094401c00c0b10b1b60031000200054164420300c00c00010b005029140c80d05d0f9a52030525014800900d4002002e291400d40400c041ca400001c0c0c840c802e180700c2004121050411108541c1e2640281007140c041c81815420801030b6a0304070854040d0501031200d4120502d00444c8000840300074100200380074000060486a50083c01125441502828801e4594481d4940040200b002c500c0e40e2007000480024000c2d0580e004120902076030041d070946c0f440481410400d91103240754103210554103032a800c603000505006140b03641c0042c000705419440401e54450003401417 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 932465350 1250 932464100 932464103
    0x1e070809040e160f060e060307090b07050109020415050f1009090f1407050415081914041704080c04091103011b270e091204060e010e190303050d0b0d 66
    0x100203c92007a4850020301c8220000c0048003c000441c43c9003200c050400c1080000e500d004a20000000d0501405404ca03400242000e840c1c1c0c6903114503071b05100d4000c0c4041c00040344100d0409800201014014060a003510002403440b200c014801c000c105004c44251801000d01c066010f0000303a2401038407801080c400c14050100308001d41200000421400901480501009010030721075503c000a0400003404203041c11002901c075010042c41140c00c080354030180d9070400060700400724245076030502851141100d2042c4c000d88080980e400d0045024010b49940096042c901c1460503800055109018110951118412001003820354880398000800190440910200960300c26008000b80340c92028403020b0f1304840c1c00340318217407000e0b200d0001c0c603940310404286000005d216024800c1002540299100e41c1c0c5d58002d4003100b0151449401f081c1038000385000c41c02d05004115135079522181d5880d03541c0c01c5940039a803e4200c2038841d1346080d91400703455116101c001c1c440d124507 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 932466600 1250 932465350 932465353
    0x100f0204030203011803050928031a0f07050d020f0d061715060a050108061f0306050406140916180303200f060402150c03040b030601020f031e070809040e 68
    0x503801d40c014036095444202d031100c1ca00d0544600c1c0e0000c80e6008060301d000d00001c44240707034070240251518180d030241e9604000e02046083d000420456102040140301c011904115841e80d95603014503a100780c11587c0d02c0100b0700810000003440c07019401003204124800000d0f0a1903050700128044030711a4015140300c00c8814080341c0c60540402c1896018040d03c0d00182441c5462008031348945039034401e213414008134078082030003943c42960030010807088031034182c440d45030540000c0240c4007030720499002d40c0c54008040f403c0c2607107100a081502016040c1001502c0f4000c0c00c1c280104a00c54600c00c0002c01408400c6145d00008604001e602a42c0da2040c8681d460890000016460401c001c03035510410b000711a410703003c1011075001c1d80403119610b4042da1031800020501c035041d40c4505500000402203100c00305000910b0083c00c00780d003210320415031000308669a1003030f0b1383c403900e40c1404401001c3c0e022070244000d01c4918480c1003180e0034000081b010500703446450010b070205 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 932467850 1250 932466600 932466607
    0x3090a0302060105030a1a06060d050a0516050a09181b08040c1212030c0e0d050637090305131211060a05040e0c0403050a05060a0c090b09060c100f02 66
    0x3030550410600d805440d0460190030b10501d1036490500c040e0400001c035043c0032000700040d0340c66580130140d400e00d0945090601980c504101e1039401400c0403134045601d0f41d5070041c100580e620500540d41710344c0050301c4513101c083c101511480b4420003944000a1355072101c0e803c9200c06283c038000a6241d100f502e80030041d003045e10349008089070036004034400040c02a42d8001044c86140603110442e090f090015103511000700859071650300070341040d0811000110301c401c210001030007503c5121854024413420340f0b406001180704018041800111208081201111120303500000342584681000740c42c008010101040a002e42e9100d0200b002500d5511400d000020a4840c0c100b8030454080e407904128a1000d0a40d0080c2d0081c01c0c040f0003444002003c41c904c902c01c880255401a003150b112003102d00d40700382d0780e100c2202c40065207420035145040941c0030703100d00800e49a55800720703030400c40c0010900c1110707000004484a42c0c40b980d6641c100302106881160f010014002c805030360b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 932469100 1250 932467850 932467853
    0xf02030f100612121b0606080c01020714100810050d060b0f0301090c0b130302060c0f0d0309020916020a1a070e0105030c0904150b04320d03111203090a 67
    0x488616902080d0310888004501002807020f0240240813090383c10001c0d00b00955481a5030315100202000382524501803012403a0b00d400201081c5018099003191a16519101c40340501a0494140d40d0401c527103104c00c40007940aa40490343c000900c8004140c0281e861300050103001d0a22020740e0b14580d0b88151b1241800d01008000c0603030340680081c00204d82c0344d0f80d0512038503e20300c1000648240482e4130030040000456080c01960000c105c562200d040d03139500bd843e04401001c40f0802d100f04a00380c403d03031f80203020f242c0c0c1c1c0c00d07001007041001c1c0d65844048918800d6105d40c0340218003031000350b80006080306e1109501601c2c45045104146051140030700b240115508440c1405014810000c0807992072086481d804016a40070540c01d00d084420b03210343c860b44e040071400490104003c81d00c0c00c4610f802c290815440001c1845444040240206d03080b8117902030342c1c2010141e049140800d004034484180307200c0c5075048400607000300c032000f0619002541c07941d44030b070030010400c0c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 932470350 1250 932469100 932469133
    0x9031e09120f120c070f14030d090e0601030c110a0606060807020106080304121e05150c030c1909051503060909030f07110f100513170c04090f02030f 66
    0x1401a014001e182c00a02d440005580301d40c2004012403510001a8080311000148482030041c161307034202d501e000c2c0c2c654485004c10150b1a42d124041d205200798000141d114040c0074003144ca4003420f103181ea0711000d00443c082c144144941080c00040b8a0503048010100000a56103028150008095060120040441d0350182c441d070210783c1000750074800080080100d5088030401070040e00c0c00c440504e4508042000c2d007040d0080d841a1a58010902070042420101d613600b8145100d05a40d0305036880f100303400140c500101700842841240c20f1003100380c80480c032030001d60507c0c1030030303669510010b024441c0f07440d1802c080403004400c3c0011400d082c0d01032600305580d20065802c00003c070001d521a8011440c02034807580c0588904842d0f42c0325000901e003000c10250803c1c1ca8081d42c00c0000e042d80d0320202c0400c1ca04200b40c0e50010f01450000c0d010220060b01101821001c0c0e0342c1010040074184600c03041d40ca11030244121801a507007005084c0350b0b00c0040b405408144ca1440505 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 932471600 1250 932470350 932470369
    0x209060309030a0915020717071d0f0c071205180405070c02120c0d0b101503060611060708011215020d05061e151c11040503160e040b09031e09 63
    0x701c006843c1c0d0007205da0184c0101717485094030039120a8000c0d60342c000300741c1403911001c1c1c2e01c55400c40400ea0b04181051715540c03100351040501d0780b01c03c40d07152100b1841c0141031040381030188c20501e8455407051003d200d80700400618040710082ca400400a1001a0071120103031605804112607100410071420401c40c0880e001d0940800fa05203100c1c40c0012800450100d00010091480c0b540080c02c4100890001000b80004890440b02c49140c060054003c0c5842c0c0103403000b00c0c0c5203003e1148101c40004841e03116441582d52419035900c0c1c1404901813521001c030484240e1910005100055040d101a102c14070b200480440c0c2d070b090141c107000b051071a0781c001005003000400b041c40d4a45821300c03205500103240074a190384686004051504030a118008400d8a080414090f01110710300701810a52380c089040c2c4108040e02444119841b20511610041e0351082c0c0024004c2004182c40c03c0c1e000380e42c14292460040c410708201109150011080b40d80c60001c503801c8001e04214404 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 932472850 1250 932471600 932471609
    0xc0705010804150903110105100609050d05070b0d091707060b060412031202091e011107080703060c02010209030d050403060b0d1104050601200102040801050703061a0d0209060309030a09 82
    0xd000c65003015102d4044000114107041d120719200c40080007017500c00c60009000701c181c2c0b0000c00c4503050a075004405240d480c441c120001d005160007041d01d291480c080c0804560100017000b00b180b0305050030403240c0292100c403140079078078442500841c01c003000c2410781e103038854041556000079142c201304544207080024001e140030301003802000e50103040400029010300f0080096051080d07980040e1080e0140583c000e00010725108402186416810081c04244c80d100c11003441c2401056880c03c1d148660035842d40244000c0001c11110360008007041d44510009d403400e1010404079140080b401c0020f0006240090100280015845480c0340d541c01101ca581c3c400c2500c0d00ca0074580050740c4007051045541e2004580c250b0b000e2a0062080c1c142802c0101c1e50004180429000b900300313219200c1d840d4205000514541e100340b0803d002d4030300c1248207c4031020060f80900c1c030343e004284085c90440e4200494580e513a15100914480d036640001076541e441d8003c4000c0507414203501 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 932474100 1250 932472850 932472857
    0x1303030503010e25051303060f020702040b0f150c0a060e030403050c0f06181f21090f170c0601121e021c1113020408060907052101200c070501 63
    0x44940601504050310f03000c10200d03e04181c440c5906e00351600780c442d50342c0c0010f22035450494907440c0556280c0142943e14000c0b90104003000070312041c44840001684030030750004a40700754800d902000405041e80c90035240481d40c040069aa818088900000280d08264000302c1c0400410604000e0050446000c1c0e03a2840c0c1d8001b1071011818900664034480b18800e000b501103009511104e0a000940e9003110b010702c4403800040029002070000e40101e603145e104001c0d801880251801341d031308040d901c000080007000f003503162844002600041d0b000c1d101c00811601816800800802c1c0c0070300141d200c09202200285004c000d2201601c110500d81400d4003076440260303880d03103000c15046960070700c0e903c0c81c1c001c3c0d031904071030111003003802945c8114034140d8401c0b104100c2c0c0c080c0c000c0c0c17442d07038040700c0e07003901e0f051642c0703650b5070040c815113900500303100c0d24a846900c100e2070610702100303507000410391001c402c240d07048840c0c900031450203040010070b0700c04020100b004071034020302c0e0a09 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 932475350 1250 932474100 932474131
    0x50609100b0a0f052803150e130206040f0323060712020a0c0203010501090e0d1103070f03090e0a051609051503130b0f0405010b0f010c060b01051303030503010e 71
    0x145a800c4038000c28554505003c55102e0f2005079034041c0003140c0c61051421041d854880c4880702007610603844589110010b403401d80c0414155000c1c800403400d5032038810070040b060b9114814000c034407545c410226000035042c480000c69800751060724001d94401c4111070f0480050007082c03543c08120112400d01d6911038020300900c039801c416216004581945c02580c4d5074005030040c0c0f44818000b0000f0740540ca8280001900d4075154080e4016032101030588060310b00c46242254143c010160a60b443d0300108420300024105078040c1070024400d080440c5000d6a0f40300542c0e41034030440d070b110400f0f0f481c0d00403c01d440002036014040b00c900c50415060217030030000821044042480320001840001000c10503d001c00445448e01a03071007001c0c490b0910302180b0f40401420700b640d04459560030800071031010301d041c80c1c150003e0001a503c49212055940340e280107002480d09080c1400b40800600c0b45124034500c200303010b14000d032506da980e540342410b40d61034103d00404102064a405 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 932476600 1250 932475350 932475359
    0x402031e0103080a54080109120504050315130c06020105040629040e0f03211003020d0803040212060901060f0e09030708130b1b0631150203070305060910 68
    0x20440d00c4404a07071072240380500307031589040560000756401a1721040b504a00004440074150401901030303204641035a589210703440c0907603040c05540111985500400030409240464001e065403220050751410800d61058407070090521203a081040142d45038810801030020901502d140b107400b0000c0f003007100e410054660100b80000c07208074401d5131110303420031140c07804015814031990309a040d80d994400f0030300d52000c3ea565850403007034064020b030001885d100501000408494018000113610825690b0740b41032584010412617100c0300d070140660a83d03808000240c4103400c3c0b400001045030500c200428000110303401100d0103454641040340780340d40030040d04c00282d404a02242c4a07503104500d0401d00da8036800510140d000807521016484c48803443c8201703400ea003c159001d503295540c020354400144484001c4a203000c050b5204040302e00300c07c0c242454011480b0200241c01402108180d9209480310b42c00640c981d0103202e114034003072030b505400141d0710005182c200d00c3c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 932477850 1250 932476600 932476667
    0x602040321081b0405031504032303070f11070e091207171e030405100621031809050a0c020d0c051b0a050918120403110402031e0103080a 61
    0x402c00443c0410302c41c080c0580c40031100c151070107000020199050003030200c003034280b48601100c041c0c0014504442c000c0c4100c0c0d51440310704064141c0c1e01c0c52861a9078800041d961159241002000c0154101e01001540030502900c00940642e41d134800b13160824290b001e290203200c28000d809281b00300041000a8040300a010f124000a02c00035180c603400e542c0c03007401c1c0300c046141d1410040c000041008005000c2802140010540da0400c02c2c592200d0901c0d0316100150003646201c4416111000400e00850414100301c0403a0000c13002e00340c64615040c20b5442c00c2e200c030f07003045d0340304c002e400c04654050007810030203089423a1070010032403240c4840c5d6441c0e6000c298070381c5c110480c0d4442e040e181c46d0070710204041c01d0050000119402c0000b110404d504901808924600075038880781c0c404420f080031078046030340100b41c002001100030300f000000e610251040034500100200b403503409a581484a00a50080c0b103903986030314440711301402d4440d00140000303848078095580c2d40c10000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 932479100 1250 932477850 932477867
    0xc0513170f0d020a1208090606040f060f06020c0a14010c140c09070c020f0603090307060506061306050304060b0f060f0c0c030f0c1c030905060304030215040602040321 74
    0x50059208102140030840e1034181a01d4041540c01030080310100102940c000403008241ca2050210340011901c0c0740b0b0403105c01c001903415041d6130f045100401c0c030600d065002049030b69180c101c0010310b41d988414030111400c1a50168015030413009502c5028a04420044000c042d4255901c0310303e403805000030001e111804000302640c5406009843d0080c040041050460000c1d01c42c2c0b8881c00d0640014010440540040b807150348000345980d4641010025203015088070f90045003080090798450001c1c290080c00303150060f4041c0320b40904d042010038181c00822840e101c4554904280c20048152401e03480000e00a13801d5440d000e030240c0b100300c1140c8040e01c0010500c0d0f1500e0740c0c05401ca05160b220310580e0b40c94821200f10b40916400480c101400f4201152110056005640003034100350300010302078007040c4080d50800540c00c00100a6511a200c0d01c1551940c45007480f09510300c10040e1025500e80342d000c1000d10401680c41512112078101d40139001c42c1d1403241000600300c04 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 932480350 1250 932479100 932479109
    0xe01060c060501231e060307202b02010b0d26070f06021819060f110d230a02030315240a051e21040c140a09020d09060c0513 55
    0x40203482c140e2032031105c008070005030740e0020304080d92030400b00c4004120980052440c0082551070b401d604004000040e131582c40c5800328180000200d043c81e500f004049a2401e003020355403074003031032185541d0b039018281001d4030501210034682052403070406000b03d18180d03100e00e0f05041041c6404242d060b5000340d8420703030000d000f50741c0b0b42c010f01c52a0300400206015940000d8202024024030440820500c2a241d15664040503007180c80030480d60b03556900166249a000781d8008540030340704188102e1405e6442c60441c44001c0d4555050466500000e281d500603000803050100c1c42e025548007490544d001c0b03483c490343c030700503880042c50034541303c040031143d01c400915500401c0c01001a15242c0072510081d201c42c80e49505420880e92010092a400461894414070341e245400102030150b504020410405d034105100c0c5c160304040084907503801070711040300003842000d900050a543c045103c01180104140c84d25506071071403a4058403c1c040180070300864080703040b490b2422503 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 932481600 1250 932480350 932480359
    0x9010306382416031112030c0a0e060a08011d0108101e0e060f0c0f0d0506060d0507030b0f0618010e0d080705030406080114010906030b0301060e01060c06050123 71
    0x20718041a0b02494254000070000400354007007801d00f94541c540c0d440c41c24a42c000e0b220109540f68450f04181c84602d00b1503001004401840400e021a20a0020740305c02c1c1c000c0c1c20501014450100082e0181c0c121480810000b80044018440f11125605e5116130058080d803110203941452501e0344c44001c40701c002d0f11810758a17521942ca14002400c0f04030f0024402c036082001280d002c04554071040101e03110320030781441c10301040100d480c1ca82120f11300580b40056a05141c28035103000081c200103809140d000ca418071001026104a00c242401203201e6100001c0c0207105005220102c00d00c40b89451040308240207180600d518070308031807401502441c0c0b90890010b81c02c0050221440180c0c0074154160229107001044000070090040d1b900540b00c041c000c0e0390310104135102c80c9209070074600041c5040f10030440c1354044e400054a40704000c1c00070801d15110007804071560402d178442d0780001c0408a03143c041c01a1407043c1070240840c0d90b8040340300f01070507070949010b8412480f20380c005d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 932482850 1250 932481600 932481619
    0x8010b0306010c06150b0c1e15090a0b0c180d0209070e011b030f02120405130203130f0308061318021012060e040c05060a09060311090901030638 64
    0x1005a280c5c010a00400301e05c60341108941c85103101301040c0c21000346900710f48100c1030541800c01c003180a0f06281900d100c014404900740b120b8019841001a107014143d00c16561030300001009920454843e41e10003071140d03100d008079111032030340d0320484c03a046006201202e0410701603140c804469a00600e075003481c0320201280b000489000030b424004984030031a905854080540c4624202c1c1c0180e410360031240081d031000e80070034603031003641700b0305a01c24060915044031070707030300d4001d550311a0500340c01020341c1506490300052030240d840104c00140d0510208003031841e100b0050380300c91280d20400c000c1e400140042d2080f90304129000f034480c0b90040707031511105102c4d02801001060450741444810b40c0c40d9405a1011800c0d43c0c1102c60841c4800c010031035062807002e6818905540e41d401224510b000c8040e00100703500d9007200c41c0000c0401002e0165119025114001c2d440341000042440c1e07109100c903680c49541c10101500a800c0401c1d103a5510210401b0110303040031141d40c01c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 932484100 1250 932482850 932482853
    0x9380112111c1e0f0b062b150f020d0605090a0e0a0b1b040306150504020309150606091002061f050a060f030f0e0c03060702070b18030a0b0408130608010b0306010c 72
    0x220f001d8a40c400070a1140701041660411074541e483da40102400d0711400c22842d241c8640c114000d0012501d25100d00e0b0081c2418003080e114483d03500040c0c0c800600242001c1c40052450907640704460317800949403641c40801040c10300d0700c0e00a50104143c403003002441c050198050701c0d601e00d18006440000342c035011541080142c0141d00d1014032115525035a20741d0b0786006005451540702c0c0110009900c200000e490808e07008480c0b103100c082014090424407040b0040c450394001e00f50903000303501440000d01a45800c0030311190060325400401c0f2600d480b1180e0620445415050000c452a8100402540c0c43d90f01412003a2203983c00d00c04020322100780304030010404040c1890215041000342c58901c6004288041610400d03802daa4403a500c4c0c0c541a0386e222901d110721079111104011210801e00e03000d0b55002c0208000701681d50f026255161042c1745a000c1d5010f880700080000c09010f141e40c154580c1c0010029804c00920540c0340140011072800002c0c09941804040c551080 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 932485350 1250 932484100 932484143
    0x1005040b0402040b0c0706020105090312071b1704050f03030702012a051002031608040314090303040e0c030105030d0809031602180702031b0109380112111c 69
    0xb40035180850768079480c0c4217280d020719a203001500c20000503510348408a5030b0001c0105c2290903006141c580c4a0040d201d084040301c418034200f84600c2444010800d1000040c3d1400000101c0d00102d0746282e1138509001c2000b0800703100c0301480f41300c1d074400c000c0180142d801840180030a408404840405c20718002c24100341c91b8120390040c40383c052550301030550f02c4554043c5010f0f0224103221345050403101019110004107450250102f00c103207a000c006800104000d001000010302640d040c503a5408000707000540941e4107031003103040480140040d00701001004116846454040801e0408141454503482404141526400ba4024420954031500c0c46013280d0a21419500350b50318184000035100e40042003210001c5400032286007020005004640d60150024815404030310003458208009400007100c420700c00b6081c3e03401850080300d182440c024080850002104065031811541c81d0054582da00d00c5900075207004104a1151a1980f0b20180d00105082c4e004c002c0c0c540d4003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 932486600 1250 932485350 932485357
    0x1c0809120a0c0911120105040e0f030c06040b060105071a13140606190e16030e0d0c0b0f16030b010e10090e0f06010c060209041107210302031005040b0402 68
    0x1000984600d003400d004002c02070091004035100d41c0d00401140101d00b05400c0c1d80c1c03041298045400850200501003890329030b00c1070140e00032001c02c482486041c3e802090854100c00c1100100d0b4214008001c207124480d40d803140e0000007440c080f4038103602c40e42ca40b0344001100c6c95000c0c01141c1030340000e1040307401a4940c281c1c80e8001200036401600a07034038039a140002c44106020f0010001e03052214080d031440a800d0306d0500e0302e825140d65410a403c6200b90fa6203503400c0405854060415080300e00340042c021034022a0344218040855003021700d014200501851031035042c8070100546560742110001c0c002640f864041219044007004861000a43c0c101e16805040d410190390380c2d98000d18a042200c41024103d100e80e0703101c06c52440048812510580807864602c0f03410b0018a0f00c1d8010804c1000c01800024441d0111900c0c0e001034124010441f108003001442d0340c00409a2841941d92611a10b015807941c0b0309280640a14031286c07180030f020740e44a41c40505d0303640d20354054 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 932487850 1250 932486600 932486629
    0x1f03030e13110318010e0a030c0809181f0e070e04140a021e03060109180609021809180c130e0115030309060f051e210a0b1c0809 57
    0x1401030004a60b082c8206500649295401c0c00120f2a42c0d00701c510107029a01c1c01c1d020400c003400d00681c45490558240c51102401c07104510204030030791140d5640003012102c8260b01e070f8001c40d00e1400c021700c0c5904800e540003e100c2011821410891200c10b0070203264414082c1c0fa1403901c0ca0034041c081406072040b0319092510200c03000c100503200140f94081e003183c00c0c01661020203007030800d2501c110303488180c800d02d0003e801d0700c00522042c00032403054003501c02e180e003000514940e2894008200d030402d40360f40100040c054400c4030186041c400650300f28042c101c1c0038894056040d0160b076500c80c071031099070103180d4900e14080c40b500f066010606246c0040020b000f000440716103407100d40400d0000b107010640f141300100705944034036040c80b5001400c3c1c0740c080c6001920750303003881d0b01040d0500038006158100009100d298100c0310320f400b019503400421a05040c4500817070291000507800500500d291420100701e42d03207607204003a036607070480c03051980d5141354000700b04c3c0d54010140 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 932489100 1250 932487850 932487889
    0x51b06040b070501020d050a150b071203150f061709030319050a020d050c0705120a05040b3108070501030c022a0a030807150b010509042d020d051f03030e 68
    0x3c200c23040000343c11800151248034400201e4a4aa00250f019400340f80c90207018445018079954500703009a01c0b6865a0604006101c0b05c0b607071f5208500106112a009140001c900110407001c1452500324581c22408d41c00246055141083c01c03040d5038001103011004041c3c5600108405038800e0303040b00e40c406d184800c244058942408030002c598460f880c200c0702031094241e02c013a070542c840c00741c0306411990340d6800d1a05217040d050840e290021081950a40e0048a1403008150560b60909001c3d000d0320488000303a10700b4180f1410141302e03600a40c185800c205004000c29400300d0003080031030501c2c00d2008000d05151014038103601d036062203500494450008011310001178050030700144642039001c45002c01019440903100c04068a0703010617014090240d0030314042c0c07c4000c0e04030040388402000002c00d030141098030041c0390201c1369260b0019501007007110b94042c080c3c0c0245210200c0d03d4011030b108036090300130310781d10001d01000f00440359a4040d80c2c4c0c5440c2d400c09040180b5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 932490350 1250 932489100 932489111
    0x150c140408150603010605180c040f150e0f01020d2618010501080a030801090c12050a0b120c060313030203090910090b121f0605120a051b06040b070501020d 69
    0x16956032602c840d0503804084403440040c507640f8050040d50140c131005081409046559210449010005810854032500501012403907089411003040100492101868410240d01c0003070040300b03040f100c541c040c010b6560000c0a81e40c001502c8203074400145072501a032804a0442c490f071040c41c0e0883c020744d4000106111040012005001c100a14040200b141c2d985e03070584150b03100a050f0005011031150401000360503141d40c07000c2c0c004100d40c10414007a44410551400b280c8080350700c0304038103a5900040c0d07203904080a10311140b16030392004080c0c5404110015200e03020060808410008910384101010f2003442a1101c801020b01403681390b0400078100350040500340180d1684a00e800002c400b40c2c5406280d4120002c80b22028040038452414454800c0c1c1c4000c00078101c50f0349829002415445452800308000450b90191444040301e2920074101104090044142d50080f07111840503520704040300c007200d5071610903e41c0c841e02850094064010414800405481c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 932491600 1250 932490350 932490359
    0x3150105241804090f110a08160b0a030213080319020f031e0f040617070c020d0204050a06050a091b091a090423060a05060c0606090709180c0318150c1404 68
    0x1040b40d8014100101c7c0c601c075170300d6142c034a0b195a951411200c640b0b0306140a40070403032843c4050042020420314034001d8034207050100009015022644100c802e5803001441c1d6440f40203242c54611200b450b0b1001d03014a050481e8143e589004032042104507075844128080d0300005074003101d14100f104068951102e0342c0302c0c000b416040e0394404410307821792a00001140d8910400c001510150700030802c1921109980034000145802417511a800c1d0744c54102059556400304207800400b22154045141e00701582c1c03c09003c4010507100062006400c0700b031202c221744c038115070704114400c03010b20386562503080010041c1034085081081000343c001e02d0032021180210a0b8498501500c50800c101c0d91401884501d110b0b80d004980c146c5c022001140c01d914081d802c480c0c02a00a28088607110b8076660000c000c100050515903200341d0740c52020039410742501500607075268246802400794070780d840d1041a003843c00c1015000130b94032004015400e0184800c81064042e0010309500d4907200c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 932492850 1250 932491600 932491613
    0xc070602061e160c050f120c07090b01050d021c0c0c0501050c03360102031014090403141e0a030e060a02043203150105241804090f 58
    0x10385450b000146200c442414a141c00342416000f4614461240707410900640200c80003242c0039012225806210805019444104a09030000e000070b0030450390350044031801c500e450030300d5022203030483c20030030620700685c1c012040c0e94100c5401000540d99112a20501000900c900d03110075002d0714000203480102d9110440310115880707035000b00f2158035400100e074400e01003101d1f81c003511004c491480c211034804416101c0104100e038149140d03008040c00d120700baa003048a05080b4107840003010811204000491340b01c0310010f5914480a0600e91401851440416002000d00200180b401c07081032070500080518000504002d4540748172980040160400c1c1c1c20b607031014420540840c60710382080c070840b421108010810020010103400c0581040303019100041301613201034010300503842c02d0006400706247c40c20780464a60400f801c001d40c1d0b010f11044005001c1050012141c05040a070454003810783d12540040c15115810000d409040361000042c0f40c42034010310701c020440b9 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 932494100 1250 932492850 932492863
    0x100504090912110105060f130f02370c0b0723032403100b01091a070308070503040f061e0e0601060305180303130309120c060f02030c210c070602 64
    0x41c01e680341007110f64140c5050b400d03a4000d88507203500030164052002c180c64080110300442c2203910000c5242a646d441d40422600003a0650003050b4035606209081c0c0e07026448050006480c214130307844158540801003082c050700c103004000d901c0c0359000c908a21301070001c0181447d0458180c0350002d600e1028100c0642058844542c040340c001c492510000c00080f042210400c094010500b4190429070000680440040c45060103003284000c2030b5000c414600a8014200103071041c0c1d505101d00c0c000344540310080125003002000d00600c000141204200d04034540c0014021443e140c441440c0761310b04c072881f4001024945401d211914101022540504850700e540b010011540c4105840d01c0e41200d03000302035019081080020200ea1400041501c520f0207031504c00b190039282c03c00303a80d2192070004142c0d05048651000c001d0a030b44615208241c2c403841c0b01031801c003800440c00c9941c9450f58402403006c4114034105203802c0c08004280d0301c104404208654143e607807440040d48805 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 932495350 1250 932494100 932494133
    0x110612180c040c14030a060f14090a090b0f070504090c11210d0c020309040204030501090c0f1206180614100e040308010b0702010908030a050a09140108061005040909 73
    0x8041e665985072801d481608414200d6803500c58a0700002504030219610003444440219030b6800d0105007041620200d00203803060b10341544410024008020b8200740051050406900348002d02001911044d40d8035000320a00d02e1449160300d4400096403240030f56007241c00c01c0e07454029841c1010f07900c0b800d01840d5100d0002a6500210b814100c440104000c840801c80318000704200d41c518a103075441041201c0452041c0e0713040003400350010301607a209038002c1d10103039102c03103101050092050b0040010910480000303415071034404034982e8003c51712030103401c0c40d17641c420030000000c1c8004011813480d4010300400c1103000010f002c41142400740c2d992a05018044c0010034041400d944481c01180c042d15000d145a2030400161010780c00020100e0400032a0b020014411404001804d8802081e031541c0b134891041c88401081c01c0240c0c0e100041065540d520700034030342d03000108c035a044601900c01207404118000c0a032014481c0d80d1001c06076919154205003408055075003a843d00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 932496600 1250 932495350 932495353
    0x61e03021e0108181216120305160c0609021f0807050906070b04030e030709020405031b0a0e1e090105221109070c081207030c0206070c11061218 64
    0xc070180c011400c51401d60400050124007164003040584a144105500203030984049501010036018480c1c4a600003214802d081c00b046444d1104010701c801c40c0704103d41652408102c0d07858101205030040c00d070494803200303005141c01da00c0c3c1030202c07581001d01859005809208807410034010115004e00c000446000200c40c0c1000c107000038030520840e90402e50080c80f0703505000058460072038019000e4421000e0141c2d451a402486c0c400740401d100400301c003280141c13958074103000c0c981801180503450014040e040e8011501d50b464600c031000390f40c0f1403081d4080d16034550300e5134100f0815a50f07500740c02040810400415000540105104000c03001e800321085480c044e04260011340c0603401401d03d05c1e100303084401030400c010820f074040d0507803420715420121600c0b0005207600c03010804000001754001c00c5202070305809580512402d03880244001d14148070000c08000900c0001041ca1040c10300c450300790f90350b001c20f40f503560705000000c2d821740c00c0000091020490f5a5114050fa = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 932497850 1250 932496600 932496619
    0x714041401020f0703080301030b072705031b0603190b030a080306040b0105120601080a0209190e070c080d020a0201090c26031309090203150414070905150d0303061e0302 75
    0x10f50070049001e03800c0baa440650103081d42d007117549620f0281c20050a040400200c1250450300d94143c0ca52001b84155401c0c00c048140d040c43c06240c1025921710901c048000207103560145038070b90070101c80c0d2085000e04088803007010000408060101c40010a50510508681d04144241c0c10019409564115410410b9078000c1005580b5402402507070f801c415817680014110f035008190300d03075002c40c007190010b01c0c0c000118005511810042c90300a01080c2c1002d0900c0480c1030404419040842d609110441048554488003207200c1da4811040e42d603000b250b2403580380e0003504400c0c41d0640c0001c9038039004c1c1d10360340003064240e01400389688124000d0007044911a02008031184041c0c42d00d00307000380505040e202400f520300d0480490b0548109441c4014003100016003038080d610927003240203000044407199160030078a40202d540309141000303000e040c1203040012600b8540569200d43c3c2c10501d420141c0042106500180d0002540720b040790900c01c0402008081d648211090301c0b9 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 932499100 1250 932497850 932497873
    0x1f1d0f0a170f0d09060f17010b070605060d02100c050a0c0b0913060b25080f190801060807080a0f060b09030d050301080307060504020a03061a0a06110c09071404140102 74
    0x60768440d075000c00004c5459018180031442c890409900050140d09048040000d000702d1500034503000d0344281c14006021070648108849030280c5034014000b150440ea01442c075800107081c0d200080940b0090190b0700c82c19100f001030500183d00720641114041507015555004981c0c25801454006e01c54040000300d84142c0241d407294030182c5220010f400d003400705250600801d02c8000c3e842621140e01201c0d40742c00203c48100420021034901031a640340d000c548040c3c50102c201c4071902091200b244018010141e100c180b07558003490a2030311007171684500286000505603a180c40788424100302c00032500000400051012907410340807103ca2042c1c5040c02c807071500080c003804013543c2003002004080790840d0410f0380c005000502c240c144c540c1d82c0d600c540c12244d25503801072480c0e190841c1c1c2409841c0005c000d0006255a08040a4102c02c0c540b802d40c6a580380032043e441502010b0105036018401c00715118100009079000f5540d940300c980d000d14001080f90040d00511a0512100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 932500350 1250 932499100 932499103
    0x1519090b0c071502011e0b180c1c09021008010303110a0804170f0607030507030522060e031e0d0501081c051602100c021f1d0f0a170f 59
    0x1100a8401c0000c0c0001c2401c0c10080c0d00300c2640391020300b046648501c41c034480c034078048090071849000000300044d0780c4040c509001d161804014034440e505000000c00c01c02c5102c00044a44600c0d1680034070321800480e03000340d4001c1809a0700170307401c07402403805482016045450141038900075220701c006002084e50361a60740a800354014401201400308005110050040c08d0310040907000341d4224000c0d50340c0e001d01e01034086405500181d112014424144c2d0103100c0c160300102010311152112000446501d2950005000104080c0d0364017030003020b04409001307031100072109070503174420041812103030f442542180d80e42c0c401c0d1a01d03081c000a40c2d1907001490200f998180c95910890018106083d41c85806c0b14000c0b101c2c01500700200c1006940303140005d88007102988031041009410700503c030b400645421800c42541400a10200040e00401d00600c003482503001000c1c10100c0401003115000280001d0f60000000080440c402e00441c000588000e810411990303810301200489 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 932501600 1250 932500350 932500357
    0x602120910020316180801020c1b0f092202060415020f06060940060c0e0603060402070507080601030f02120703030e0d03180b040f0902091c021519090b 67
    0x3018280b0741c1e031140280550081d0121704420702001c98401c9201da13a0000282607a100902c0302141e50004506110190000c010890f6240c4042e2240360000e411b1501151400740041c4c80804038580d0080c00d80810720350000700c1d9007910790140840c1e8544e0707501c5401c400c10081c50710401002d030148000d50fa00d0b0060020b050b80c441c581c0100128415114410348800d40c00000b414280c90040c039181e0511010b44010011050401009103000c0c8021a41050300032140d030b40c440c1500300691900d814901303039551030a0b00d0300804100c800603079450301840c205150031007035407000d4498000c540000041c00b009860300b1800038002c0d10042c0710417200910154861000e400020040380e600041198142408400b8040360b621038200305510a00c281220800090a40d1008000741e00c005001c1c0000618000010000e150034882507080000601c0026454400d14902041119070400c000007555101d480d0b4040e0011045c0305030303681d05044180e008108401540308404a4514440088c0e000c0001e402ca = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 932502850 1250 932501600 932501611
    0x61206120c03080a1e0c021005340605130201080c0a1b06020d090f03030609060f03080a14070605150f031b0307180203011409060604060f05040306021209100203 71
    0x1c0c03981800c5550b030b02d120380c0255500c04200010301c1c44800c3d4082001201c45070031041512104c256041d5072040102c418200703080031007049002c0c031451450410803909440360189540302400001540004001407104c050030140c00d070340c18101400000119480c0c0800518005e0740c40f100e2030750740c4020074601403160b080e061000a5844401c100346460000d49070010031300c5000c0151a001c0c4400070b040a542c46681d0a0300d09061200040301050b41520039200140102c50090001c04c0c50080b0320700f4042101d00c4040d1850000007018203095120705401607075038501700191a1100141c1c10030030020300c0304071048218584082c45064092502c0680290b000078010001c1c4844141807255034a201d00e481442605032141640101e0703003c0c1c038042c5802c9140565803006132290302d011003102000110038011030042032070030140106a101c0c0c00840f0241e40075030a010022000c880000c0700c0c14840c581c005000f09101080a4903245106d401c50340c010802c030b800b10381245000c150a0000c0707101c150344 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 932504100 1250 932502850 932502863
    0xc050d11090316090e16031b050d20042903030c071503200f13171506040c0203030f0c0d06031104050a0515120705060c0c1503010806070503060609030706120612 71
    0x208001340805624040c2c00c00d240c0703904234441d0f42d0348000c04e40d00c0c0b050a904a0328161100300140440c1424261100fa8000846082c8203500143d500365244008400850601c1050603156502584040048072800074a100803500f6481e030b9006107005460703043c5003031030009007021041502d007400c04a08852200040156074a0315048003041e0350250300c070b081400b82d124180400003880664800c40a0142d8400001400c010001c030701342140c16410051420380f04a1404009815a540c008180d81c2c5c0020054180e410039214404810524015410701258003814036030040100040107040135150041a0b50511071510b802943c4000d9400886104441d505100b01d019801c0c6007140d80e503d00c200004041d5544240c580300072a20300d038080007251745d040d44403202c0e0203024105074824508035001c00d0401030a5504110010f612080042c051104101010020946507550302080302c21148000702103502e01c036641d500203809203c0700005440d20b0340c81c1100000301402640d5181142e03e50040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 932505350 1250 932504100 932504143
    0x121c080412030b12010e010c09080a05070b07050f24010902091e0d02090c091008010e06190e04050a150c0e0909011d010605130c050d11090316090e 65
    0x80303005203d0350b440d156221800500c0f01c01980340030300c103103504016143c001240004040c980907121262a50044449034007401c2c481e0003050380440c01c503042c1c0e070b0800d412941c0e5a6590502c0d0f0303c1d200503451504070500584a40b108036a80c01e0703440516540c06001404100c1e80e0343d01d0030000b240260b0b6500b94101207a416081c400a6031381c0b02e940103030000104000a00038541d000306502a40c201d84440da4040d00107410707400f51070100d011600101d52807030306511540c1008143c0f0101a805030116024102040a81d5028500d0200c0700003c1c005480c82ca00191815040c100c0c2d0701c0c04400401d80b008000d0000c00300840c20707280102101132000362122402003140c42c05008034607000411a540d1550781e94000b22101092481282c6a00c08050022440c5400c00c4100044a42140d515100c01450240101c00c11034010742076031424210300c0000108000c500d45e4411151051002e915414000d869001c2150345035034070441c0507a08642400c00c0880c9100c0c117610381d18040006100c82150141 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 932506600 1250 932505350 932505383
    0x91002010c1416020f240414100518030331060f2c101e03060f03020f0a050603070309051e030316020a05070303030b0f09060a060c11121c0804 63
    0x4541031750740c0700d101410340000d01103039241c04254003c0c070308100074029030001020007200001451400c0120000c07102c5400b5180c29a80183c0b02c2d210b00681581d85540200c1a40207543c3c00344261180180ca186030032445060740d0030103001c0803144610f0350314036640041022501a208841513640444a62224a2001c4c6180c1c0080700000a642e0220035400d13a10300380d4a500c0e1a441903002580156840e0400703c91070401d205a070101c10200560105441e2220421426811500020482e074058030400c040c1c0107042d01062407204141c11160704030340004144201c0315419804551000d0090098030055940700802d002382601100c420200340e03000f8804944a01110001240740310001c2c0100c4106198035654681070903160341c003e0b00400d170b172a4030b010340c1414184c9c40003c1a95044030001c08a140c24800641c401c401c80c09070208000480400d0803c010b200b41440810502c0240550b00700d00141200039a01e452580015601e1901e1041030f14556028001050040341d01c104c110b82c1c00d80f1034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 932507850 1250 932506600 932506609
    0x24130506010603110d1d07061b11060d1e060f080a29010b040312031b08090c0d050607030b091e040c030803040b07020c1c17091002010c141602 63
    0x300802030015981003103617040c804214031400602c1404c0302000d1007002c0041825604045059000805202c503620a80f85482d803034030000024558480000c011841c03a200c041080c60091320b9010301481e00d0441c02e20702003410ac1901e03401070b42042106000007900c0c2c03084094850864418540390760310400c0c40074002580da10385e420400720300c0d8002c00304800d9003041d8034800500a9010380301c0c03410300040034024002d0030702007420fa0a00e141828060840b0700d4820758200b10380003000c14200404171010405004c001d0107040000400140722449290203030400c2074690006451701000719140031006006801d115903210320654200004c041048a004040a112040280700f2550750384540f1002c000140c0c024042c0d8012030081501c01001d1504080180c50414140c400c0d40c410141c08941060340040c81d282c810f80c86902055203491a1a2024448403901501030480e078040600c0340500d0100382d056100b400c02406ca80e4400510109030100e80c541071040000d03200403400d25000b04005800c2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 932509100 1250 932507850 932507861
    0x7030804031119091505040c0e040c0e101707020105130f02010e09070c03080601050309100216210306050109031e15020c1e07241124130506010603 65
    0x1000c1c0c00e41e668074148407a89014400990450a00940d4401ea45c685118045020a0245c035041d00c2c20070550344485005011107498583c514860b07030b180c8401c0380f18948194080005540054080300c6000c86101015000811843e5604886017000d0000307100644140903150050f42c2d40072068100840d030b501c81c0648009888400c0e81404082401c000168480030241d40c407501d41540c0c0d014040d91680380007004079801130003c0781048070034801c0c00007202c2e001c50409c00404019400598840051340990048603034000090580b014000e00382c581e00c00d014800301c4011006550420255403100010f65000240380405410710781180c07180d9810035000c5043d403144c2401045802e0b0010004044072080c0e0380583c500446c03a810001c510300105d003141d54110b080e49010005000c089007000081e80e4244251558018000010800c2c00c2c0020700844991443c0013941094401405080301000d00045d10850407101107078080000569206804084154480c2e00801404450740b9140c0101c0c007404 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 932510350 1250 932509100 932509133
    0x90111030f03040c08011a011b060e120a0809031303030804030e040603140106170303040308100e01030507170d120213051305040204050717010b0a030e030a0801170703080403 77
    0x40200202140c80358860080c5101d0f511541c05044414207100380d0318252407440b0101c100a003c662071041082c0c2e080860709d0180307070401140516100090400300050a42d1001034555402444003a80754550b125004048001c65916180c040d41c4902c0c0f48a5a01e104000c0c207221596a41402031002a105840454000b4000e180c820085095036001508440c51640200c1e070440000141246080f000c3c00b4020050108c120b08000068418603003503183d100c000d00040820110000081d003072862003c00301c014000b00d02da490440d42c0c49103441584c600f0540210a20b007091560304503901c0500081b0920036280c540c2c0c07503500213298054202c01039040500580460b000500d004a155110f0134821002480064008116800d00340140f00c1140c002600c07a00400c0354903145000004051115607044800218619659030f02c0340300102e0080011344004002ca0100240e0400b401d40e10088044c141ca985412000c01c208116078010358803121484004c0c0807000501080001c904540018007092 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 932511600 1250 932510350 932510353
    0xa02060706140907031118061c080f070b0c190e030f10050103110d051f0212091c212a0216080309090109180203120702130b0105090111 60
    0x400345200b0a801540c000c940214003540102c0c000c000f400701e41c1a03680c0001d03c0c2a21311103d2002140400c500210700105542d004200062100c3e48401c0d1b8110001c0c41c0f181c00071082515040f0a20310f2060aa10040040d600208402d020618100d0f1000c22a040b20840500c101690300c0c41c11400c2d102c02085251559060003440072034075060b54244120310030303c45c0840c0700040a42c10b5140031401c03000f80f801001d009482003001c02002610004041001099809801188100c4580240060300c2000010050b070802c02040c481d01107000202c2071000200c00154001c2e410110b07404a401508aa0103441c00112f60080d814090545074402102183c000c84000311450140c50314030381d40c003801f03140c410059102c1e8000040810307107101c040c0003a02a10024516101c0b500d0001070032141c0c18022984101ea0380d040300710070500410500540594090150385c0d0b0386400740030507d8560400c2100764040d55800c2404100301c4140d210f0544480b20507100c4070f0074002c01b80011901e11200c0d40800905 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 932512850 1250 932511600 932511611
    0xf07090b09012d0f080109050c040317090a0f1d091905030f03100e01061115060112060b1b010b1c03170112120c0c0527090604031b050a02060706 64
    0x7040c0740c441c0b4540307200f2140c0d02c5403c55052a031000801c1c02c1016032261101a14200500690400040489044070b4204075444009480302500d020144a00401d6652201d02d00c2e00c000380c0c0a01a006010494559980740d001038804c5036050064032400301c83c0383e50550880100c80c00c48046131804405514003c100f12400c1c0f041001c013210302170340140d88070010800e980204000300041910814090466840e01c3d11810901940842e903c103504c6942c5507115000b4000241c00780d204101d00344030801800c4003808050303500c07006540c9541c800c0312911040c0c00711040f0f2031040201402161007001c0050880d40c2e6010800309a1148503e4800e01101000305400004640480c10400035010340042a010206101c083c64100d9003409181c03006401e110901403d0400b00342500d0103170044803820340e20180003042a010703220f00c01121812601d008001c45090021030315000400b00e200e14842d8440a05043e40c0d026400e00b0704aa132030703004120340d00101c0c1110050030080301400702d140c442c2801141 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 932514100 1250 932512850 932512907
    0x608160b030907050607080c010605030706090905190912030b01050403020319020f03030d1406091612020418151208030403031503020a060807080c04120201051602180f07090b0901 79
    0x45c030f0350000780d05640f800000316909601880a00c034110040074110024a00c16141c00f1024180480911502201e00e6550001410001c03619420b5035032485200d90401044035070745482c800d108040803156002a2402e100d00c4159401101140c080e05c0d002401003500180c1000f0301c00314a408220201d0304503d48281c6400c960301c0c104060007414218480204842034070f0140300c041040c0040502e84251b524074144500c0d01e20300d88040303600c030400e0b10300b4610581d104800c12010348520750058800207140700220002056030350000024640c803840006099079a51a00c0640d58030110b00a40000f00030000300300024065800781c2d004522040e40d0700d0183e6035035000107924079000da108102091400040000095100c0d0180c0d0340940500c1441d030801d0f0034411203200c40c0e0300c92403000f0305003c0000b844031001c10620140070360b641c3d401020342840280c8000801d00c105d0090b1009068407100e90042043d081c01003120400780d64414402500340719545004540c00c820384101c4002d5140e0100300f000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 932515350 1250 932514100 932514109
    0x140915040504050312090303150108060118090b040b060f16140d08040605090f0d0e04020d0e0c0a1a03070806041d030a020d0305010b31060906030608160b03090705 72
    0x51080340a000038548a800741d512249656a00401486d0140c20800070032210b90381051038109480030030b1030b040030255990401610100c83c0707030214640044904200050504440e044038030316150035141444025040c009015960054180440e000d90041c0600003402c00f110f2507101400d806801c9907040711942c1c510590811040303158590000e9034400c10041409903600901d50000014401000140916158940c076030403030040780800c00c00003405200c910b40d601d0b01512103500b44078a04000e020407800d2101d580741964400c45018640030f500015240c2a903046120071001c0c1c190a071499999100000c40b55078000400960380303d5a101881070340b5101507a0805c440101e0800216030b12401c82802078038003515401540d00705810503006100c045a82e500b5500010340c01840b06280c5104000d035001d2071281c9003400540c030407900d81300044081c0e000c65140c04903151a142040b015880d00882da454440c0d6031140b10740f4000710f1104106201c0c03a440150f41c002c186030242d451090b150740010307 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 932516600 1250 932515350 932515361
    0x49032a03090333020f1b0f0f060106021009061d0106290d0c0207080f030306011425060f02040e0f070306060c063215090114091504 58
    0xa80c00140e04003014000c02c40c5424000c1d9020b002c4418802d903003180755401182500454500001c42500491484000c00c12642a2025480c01c2005099032407201c4062594410040714a08580e10070a008800c0209003c1003207030590b00154080d080010124007002e01600b00c4100c101d071855540c088048003102821404200400341c40d00200c7c4240c9002e00d072403040f00340c1c400c0f40d050348200c4020201d81502c50380201d801c400e198080104a00c01d0401c02a42001c007541e1203002035004000f06c00244540c040005c601c14a400d881b0211900a6260003c003d80584405a21005400c480c0030451081d03a503075003441c243c03240c8404510030390344039100002c1e038206920400090144005120806446001c0706510200d14603040000b9403400030018040354645a024217869a10401d0740340d404506255001c030f00c00710031b01200c03006000c021400d0380c0300c1003199104200710f03002446c10050b2801e4100e86048526142461031324004070010011652005081034140c210b03c203100b240c160705c030350050 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 932517850 1250 932516600 932516603
    0x51b0301060e0f041823060c03180304060f050702040e070f170a0b060112020f0307050c15010e01170709060324062603070249032a 58
    0x1401c010400c1d48090124005410700420f00c900e0402c82c01404880641000010058108807074900c800c02c040c801d16180b401b0351403010040d01650080104c2c4000d0b0100031802240418178020324100410891074032402a805000e0004201c1300d44568490b21a130042c20115000a00008503001a0040c0500e091883d9100040800d601402049280d13158040c0c03d1424804502424608002d640ea05000c140024041d505110f002110940b00c41000e42c103a038280003e000304280e0b00d09042c0f43c00340c55500b208001010710300c6100700c0310b642043d4400070a0304840c420321046074140d08140f101480c1141942c4848042d20403a200001e055040e40200d00c011070051030803840c0c4021540d12100e0100355103540040c01420030030200328400c450261800d1244164020000700d212042c141070840c482c880b0080d520070507080f0030508034540c280c880300104041d4079840c02d4503801c0303503030042e80f17801c00001c3c0103d030507801120500824040c2000325451a055004001014280a40b800b060901c0034070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 932519100 1250 932517850 932517857
    0x204050604180311101b081e01060207141f1412130c080609060c0703140a111c02030304020d030c2103050606070809040f06091d06061c06051b030106 66
    0x4000e0701c152040c80311440301c0e08034805c01d00c100044a01c0644807850041142000c000d510310010b43c20311400c2c40d2071014258505d2840d41305581d0b90b0701c001d540b00d00134003c000c81e521008001c1060392505144e01003418421042c441c00072080c011007130b2404512a0010310903440200088004400700c001510b2140d03407400d00c9100d90900b941400d4403d0103031034004001c00d622001c240900038034006100c0d40d01800002c140c0f46d582040346401c4131141e4094411994880d40481c0205a2a401c0500c501c0c0e070402c034000300c51030203035118112103d184800302c07104056001000880c1c0523081143c0e00c0d400d02d078000c1c03d00c2c543d4103502c0c2e561400d08000e08042d0b02c542888408040401944c90b015072904490112200d6060880740c0e141d5a10070312400b00d2941c402c55030364001d22241c0056400000040c603a00034100583d0601c040240c59000400c1d90303074456800f850002035070510741980c02035084846030580c0007141c4500d68500004001c05080302da145c10202c0c15500c8209060740045018040b1950f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 932520350 1250 932519100 932519117
    0x106390c12030507170c0a17120a201c020c030f12100504200c12030109062108030f07090b030a0b0415030503031906150302030402090c1602040506041803 68
    0x701710b54840041d0141c40161307901085078520042c00001e41d40142c42e0040044d180906011044c6000d91081c040041080c1c01c041c803c100040d501c0c0e511822200c1c40b4180c01c4100e00300303a00080119441092010300d080e460340c0c04503410143c4c80f60701401070b000341441124940244980001c07007a41115208070801c26040c010070003440080f072084001042e065800b070281141d510b00101880145880201c03140700c0115910300c02120401842e00b010140c480c040c0c0e503e503101c41d00b10000e07020314010021006d162005140f000c480e09801d007440c25030800f291038196215049a11075400004d0060350030000102d00118608241400550148094400019280c10224244403e4070074170b4082401e0405c41000070000700310302008a030341c460f100389880048010041e41000060070036411110101945c170545600c0c03503416a0042d40960300846400805507a8581d020000f4440c0a20580d0195241c00784000181000e40105800a4000704081610481d41074031440181c44090260009036100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 932521600 1250 932520350 932520353
    0x140a02090f06161b05010206040f110d03121a03060106030209010c050106060305040c0b07030c0b071106090102040905060d0302070e0402011b0f0b060d020d1e05070306050106390c12030507 83
    0x21484440300340390030700134000c6035864080040e4550800a1015045802d841c180f18100000c2c0310700441550801051100710300283d0030000c02d0001c1c1076410517600703480e0070648400300d0404a9003515400c001801000c444c1e0909204034040e40151541c181030200702c080c6100090800c0c029440680301c541c0d0002014545420480600c0c2134550102c29144c2c400c02951000c25031106a200050781c1004030070911382c6842c1400c851441204502c03c009020714010b2008a070419001442210004038050155407a07000802031178492a48004000d60310880042080400404d041d51340140141071440740415140d001d07507800840350380101c400c20080c064841c100080d400342d0030780025051701d03010340c86030507030780804e20226080c0c030060404d01c412150400216084a02c0115882c1d101040e075800c65079030f20b4010040c0a00380500804210780030012800300885061546000c2c159a1205140b5181c1c80d52140071715030340c104207941000804501050092418843c542d00b6803290b0b5819170b69611a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 932522850 1250 932521600 932521613
    0x30a03060506071505180106092c030d090314160c14131e090c061103121501020c0a08030a090b04140108070203120403080118140a02090f0616 63
    0x36400c0076100d15018402c0c2d10104041004038803200700400000103454865a0088203146204503518007190f08004001c90101c000390046400380c170076881030325045110346894490b203e442510224440d070050100304016401c68205960490090920900c21840d40c00101e000d94028000203c00030201c1c1178840401c5108240d4800501d13007145c86440b10020040064602002a602e05804503140e80d0b15005251003204504039041000b041048090b0140c03416090381101803107620045042001c541302c070b1010101c221400c5441084110710302e40d075030b0b07070941d07140302c5680d0b41031030441c40b03820000692034440c6c0c0340e94000340000400643d2584108900101484080c1c0c0110074a0f00b0180010060350b20440c2a04444501c01d00304007440d542c4d0100e0807446e5000d207208500080182078280014540c0004a02d8145c40d080d43c80c2506251209012105565241300ca86046d060014005103038009580c0c00f500002c5001400100c0d00c003106400107402d03802120b41d992540d01d0014101c000c000c103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 932524100 1250 932522850 932522861
    0x4030c201201050c1605031908061203030903090913240c020f0c090618011e170706140409050108070e060111070501050a090801021801021614060901090b0408030a03 73
    0xa00780024006882c2251000c800b41c0a185105000c1d43c0a00c1406810402c0510a5919103035004401c01c0002002c604014114182079404c40d0040f034802c8140d40840c1d0012003128491444480250700d0b01d40848180f0220780001051100d02d01c1c40d10340010b000881d22040382d400300d00e43c80845a03111007210b210404441d030311054003080d513201e08500b248010b03012480d03210082c002c0b1281003440d0f07a00b0001c6002141c040507030b14034021340d0b20008594a01d4240389041c15014440d0201d00c4c0a468000d0880c5c503680300a0380710541c0d40840c60070411584100c00d08913400c03244803469824681d40341c01110a5a5080c1c11040b41d642080909101c08944980e203160b000c8002d18040402421248801c2e80712500c07030040c01e04209000400000f400e000780f20640040c505903008540d991407240340e0180c0007071440e007141c1c0140940380004400901d0720b4a000d06032101550300211014207442003065562120402e2414407600000000c0c08802c2040030304002c281c90b1014543d00c20069500404855 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 932525350 1250 932524100 932524129
    0x1020c04090c12080f0d0e12040b030f04030306260c010e090a020a2a0203120405060904050a110301060c05150f130204090b010807090b04110a0804030c20 68
    0x500d0203550402240c0405042e07011124402c0ca9024480300a0402004901c01d50400c02c0f40314100003595440c885032603001e0740b0071041e9801511080461134076410080d10461140e01001d00081c008180c000e81006025500700c1d10034100014225034500409042d140410f0341c03d14103171000402c4004143c414083e40707070100800d1070100c0c411420b04000a01014020300b1654219501103107001d9a14081d000204168020036401140090140040f403007000c0b241c0030480c001d0050071070010070043d000c402d450036984018070032410041c1820a1100420000303215244003504c50417115030210180700194003130300042c2e940b0a40607086060061800b030390001030440c0e460b10041080b03103a01000380d045030480303540da04200c500c1c0d4841c00014050510444c0c041c2080c414000000740c05640011500c044450343d80c03003800038000f24401c201c1114200102034541c100100066a6a103100b15002a44240f0a041140e4408025250306070b5840880c0d5021401c2a00341c3e0b0543d00518044014042c0003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 932526600 1250 932525350 932525359
    0x80c01150f0512010b100503041106030406020a02011a0a090f110408070501020d020c060d0504050a050115150c020906010c0f050105100317070201020a080f040b0f0301060314010b0406120f0c020c01020c 89
    0x1c4032000072685032082c41001d00c0130840040301249c01c002031f884003d00460320082030b143c0c580c240740c100f17000250300c15143d00c0301662a00b0840042e0407444107080e4a0120028107030409541781c61315403c050031f40c148649540d16a2541d600c0803201030b400182c4003a04100c001031071564144400640340896550405e401e561290094500c00d40d10799040b220700707010f528400318840e25940f90407440c084080400034007030350900d04111502c034400e40320303001110b2020504083c0020b03d68400d5030305806400020b50844d03e21000101c0550240340040c900764801c01c401c00100071140c90315421640180c8070103980080940040091011000c982001703044480344051070240c8a5002070360b1001e401c040100403a80108144280072071b4030040d1001000c02280c01c66a41e10f9500044803036500900407000441c1c6002d810003040c1425643e02c505032903510a941d0318090a2030403c0d94403c140204980c00140c9a1444450221b142e021741181216190010b00e1103112500000e0304240742554900d004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 932527850 1250 932526600 932526611
    0x30f010204030b0105031605040b0d02030f010e010b0a030b0c09030a1a060301050705041203080c13092703050406050c03070606060c0308090c01210e06010609150801060507080c01150f051201 84
    0x103d0131f00510500440703908840001d074099503940070406541d004040603505000e070340e08114907808190001904200c0d00c10003048100004410088118000c7c0005803042c42c1020000f0148501320004250009004040315840d844d640d0341e1040c8a01c075041c0c43c1000c440d0007010300400d0b04090055580044a909040303041504040c05400601110040501040b1090010400c0403411004451203c03455000c101280d68403a107010001d0640d10050020515584201400e18065000c1a401043e4103603295031520345030180442c2d49412400d0400b08a010400003040083c0091040030014070035900c40206602541c200175110b864003c20201881c4c11071800b19005aa002c0d070f009890040e04024032951f0b81c580740c00f141c0100066620340d01d082c41001c001180294001c0440d80899002140740c00000003503d5089400000c2071041101007042480710100060702000602005650140006004120350041e800c5000440e4406c0c641000c44c0300090050f4144908000380c1030001070000d024 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 932529100 1250 932527850 932527873
    0x310080706050a0e0126090d08090114010e07050409061401030c0306180903200a17090306150d0b160f05030c0405010e030f060a0209090906060a05040507020c030f010204030b010503 80
    0x83c6032210f8032900c1c1001242c1c045803004d5100c11000c22460400044011041d11f0117424035940d801012541002240d07800c000a04001014018070003001e0000741c0d18035140c0d28045084080c20406403c0f642070150030701001c42c40311f610384a020300500141c01410b003201d01c410300140843d030085580f4404c140c1040002e01c41c02c40101200041803c078040300060510780f0342001ca651000c41c220541030701c4809840c051000f0400907001400a01640c441907044006a4460010744141040300f501504420000761055040b40480448500042c0036500e14820b10399640e104080204d035082080301d182c1c48007088180d804114001079111a090072807443c00c1a040c1d006c15400b50384030344c9040107484860055182c4003071013004441c50710582280e0350f60500d001d041001e90001c0060300c5c0039984540015001e08030019055010380809071100307600c40e003804140b0010b400024a850207501c0b44141c001c21075201003195061007100a00016156411407411059070786040e03020307a1007644034080868 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 932530350 1250 932529100 932529107
    0x7050303041a040f1202030f0f090108102301030b060a0f11011514190e0105010e06070822050d03020304030203060a0b031b1903150608030307020d03020d110310080706050a 76
    0x4922a030082c040132145d603d13100080703203903110301d5000f424034000110f10380850442a8001d4246480b00b601ea85209546042d451564000d8501c5200e111680070010341c110078422400c02901280103240101d040c0342040d010070804c0e0720418018001500c0006032851140d4454078221450a06000910070302e00300307054210000e0207902030410b0749225074200c030340d140e03462403c0b043e000400109030712402551100070510f0b10f07000b4410203004c0345440e110700d0450724190f0104c07803400c0da0290025041428a0b400b8010100104540c044030007180075010502d50303906402800d159200740d00455450307046205240c00e2002c09040f0f07000d12030900140001540d004110051100030403086800030000701000510b0080c8400700034514140701c0e00c004014085051021141842c25080501845070345644a650381c0c44100d0f05000140c110009010344d007842900240b180003000e10f00421400060b901002d0903901c2613610540421031000c0400c0174280620802c002460b40d03040190a0410404014 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 932531600 1250 932530350 932530373
    0x120a0201080c0702040915060803071e02130608010b041b232502120604051b0d0b070507030207060c0b0f07110a08042d0b0313050307050303041a04 65
    0x38144240c16000500520401c0140c5076083d80050040c0068001401d04030f017440c0e40000c01c0607025052242c040307208880081180c0240b40c0c0b065140002c00d09034540c09901c6002007500f20b81c4000c48400c580105413040c015440500101400010014040c404010450b803120340900b2404001500301c1b4501d60700400300800320009003c0c4e0b95002284110404242d20a00b1192000034800715260880d41044240c4504454401e60707004040b4000481516500c04084900034541d600044100c0c00400c0c00350307512054003001411038000d001042e582c0d800c1d602c50850314080005c20114024042c95810044c3c08001d00550404004184440e124481000402031a0349081e2140d0300100381201d1090083d0607490700c04c9004da4107886aa481d050348541c4c0f01e80f0500d416848040040d0400000c4141d01d05100820300c0101c0c01881c0c81c03c5072403000383c0c20040065280803810444000820010b0000b404800d120340d019681c0e03407419180045900700342a41002004058a00304000200140c610 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 932532850 1250 932531600 932531603
    0x20312090a050d02150f19020615010815040b2101022a0709021b1605030607030605031902060c031303120f020606120111070b0f0f04050a1212111206120a 68
    0x107036a5181400c5c8041c1b152403281c5001030100c80310380c211000741a84d001c03a00740c0c05030450861200152228000448a44505aa02ca02da8107865400a0b01d1403500303034000c10a40d000580308101e00e08110520320501c412050300e01c425a50009907004a01c00050740a450b010fa242d040c0d9001c0d0750501e40450759683c541e015142165900041c2620442140c007040010504168126040306840c181000d0504019108a0703000b8402c1c603000c01c20440c0680100741c10f54001500910080c01c001101190b0038103808800c0e608500c08000c800c0c80360109000a001c41e58000a20070300403840d61801c11080c104074840c0c442000048034140100503408131f503081d00070308100d0300030701030408030040740d40100b070f11805191a403200080e1200401664500c5030b4420240308007000490341d01c001c003810f18020100d80003041a00300745604800201600680780c0002d22504c1c280c5c2c0701361071b0301b4150421507902d082d00d0550140d0101e00e100305213140e02c1c1c0707882d402641510540004034a0907802682c88400d682c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 932534100 1250 932532850 932532889
    0x30314030a061a120c190804020a0305010c180602030406080103030507050c0306011203020c030f0303061003020915070203010e120d09031103031f08070605070b070507020312090a050d02 82
    0x301d8100100c03500b001d805807465400007000c21458004440c0719501240c114010150b1001c001000300d080c03082070760181941c102c101542c0c01c500c0300c4c00700c0303d030140148100d80c009a0700b1404004121b003441a0a400354003901c1d1900da200c0310401c070900f110f810341c0c0714408541c0100400d2205030b520507070341130450341d140c24429100c840074501305050030754903400c05425114230303000010100403248162618034000c1d001d5400180d600c505054550924107c05041d42d8410400701c0c4642c103200c2030200800c149403078014201202e0000042802c54640d840303100300a070100c1d109056207402e110f05e001c2c080d8110018071241540e61185015801401107030040d482c3c1da2a0b4020901d80141c0307000c0018030001d0262942c0e485c000e00300b01001003885980002c90780500a002c5003c40001070020142c0c0c1b035079110141000851381ea900c101040040041307040104c00d10803800107031810045045411903810b01c4d08d0311401140b0600c00c1c186480e50029114801c2a0018030150f112615407200007501c001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 932535350 1250 932534100 932534107
    0x10b04060f0f1e180b0403051c0c05010606020709050c090907030c03020c070902070c050a0803070b060a1206051506040b0702091003020904060b1f0e220e030306100306030314 77
    0x4081d0741200c46401c810ba400b800001c42500c00f2903208000f426113071403410740c84c0030003500c8654011190055000c0140190310420008810740413070340300d0f4504410a8035180c802c40100e41e59003420f45d04160b00800160344001c00511100c1d07500c0c001e20307138451040ac13403c908250900f800a0304010000d0700303410038141d99083d8860306521a4046031134610f821400c071401280d407101b25034000c0d4800d14040d15062070740b00020591b49401c1c40038404851451000310308041080c0c90350700d0500409400070b584220101e400140400d14034940b22641801040c0000306850207400e00181020800c9002c1c0c800c0d0380030002442503420b0708064a071245c0d011f0701c601c01d05030b0390070454002800c441d400c040c1d4052000c004000070014140c000912200c42030b903070071640103500001001e4040f18144a4808a040403813207143d05d090044c100140d08051181c083c9010110100d5a0121400c8269090494000008001d09400c2040034a40b81401e1840d040040c50b145403001082030030144c0d040d280744d25002 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 932536600 1250 932535350 932535377
    0x30f0b161d090402060c0f0a02120c10030f09150f0e1f0908090316140303071104020304051f1401170304150302090a27050903090409030212040603060608010b04060f 73
    0x650760100e4031041181d1f50070346440351080d40e0741c1311078004922850140a00c1882903001203a10f41d65480c0140c1b840c2d01e00d04d00300340c059005c1c05040c1c0300c0d402d07010758890f80040480c484d400e40709040340a4640c001038131080380c1508003e50740a08480d0340540d21541c0700014058504103201c3e4004408400010840a02d04d03055081e8030822030000d80c50703c225602c4494800031906c0d1034084070307912500b000c08008027009143e103a000d9410060403040d031041c170001544c10140c0003185c1c004e20440030f0301e52203d50101400001070131a40406013042d5507040f0164212500ca100a01615210f00c0103042c4441c0085100c1d541e20450040801c00b000c3d1445052100d406601a1148080000c1081c400030792900c140c041e0081e000b107038a100d41d502c840202c08510744148110350007581e085000c2c500d06110002403202a001e001000c50461203044075030840e081c440c0003d8000381c8419900403c0c00c500c0e00c1c1d0020882307141038010800c0d12904200c100b0610742c004544c20303075210507418103000395900c9 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 932537850 1250 932536600 932536609
    0x11160b090118030b07080a05010e0112050a0614061c0f03050a0908030403080a031a100f090317030402010215091005150603041506080a030806130204030f0b161d090402 74
    0x2020105450b030352000808802c00000c3c04010b44140c03981d41d10001180d80750401c0c8001e0300d8081c031032468001003000044c0400e04d400d83c41041c01d140500211080d03504030380c1d40c0701c04035000c80394060100180b19051220783d1900d0101c0380641c0311240c2c500d80301083d07140c03070b41441c00120b240000c00340304000900281c201d0042a00e01c0050481000b569101c41e0b803030030412000da00c443380001c0041d20300a0070555012440d004c03010340480c080c1c07070030418242c07042041c1c490459034a5400c003408502c110020000c4e0440101c02c04000c1c466030303902d440782001c1c030001e07240004400d43c10009006503800c000764001c001400301880501ca1102090640352059051021b00c441d030801e03504010000104814002c0c2c1031740780318883da20341c07000f00b041951300c44045490700140d40d4000e000800c0e10000c69102d140c000304400455800fa00e0040c50250740f0341c2c0e01c440c0310322500c404070754003070801341000519162411b42140510341801c005d4468544410707584100b50001418600c581148030108095440c1c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 932539100 1250 932537850 932537867
    0x3120a090203030d0b030d030c1b060b040f020408010b030d0c240207050109050705190303050309120a022118061b0624030a1703130c060f11160b0901 66
    0x1005010760750b5500b13050440c00d0143c003e140a9502902c44c2c005017880c018460b00c502a82442940d6410f10440100b2600200200d000074098946940300c0c0e08000c51030740d6521686481d0f801041c00103a44a15154250b420364001d0020349100350090b014160600b50404015802c055001c080b80c0c0e00c00705841c216420038440d85051040c03161011601c80c0c03c0220541c00240c4c0c041c000c0c0200c90886660704204800d008907515041000040c456082000030302440203541c1101c0880162a09040000480c13a07082d005644440010303403003e058800c2141161030810103e1341032050302884e10700944002c1d289600003880040c0900000100420030010311542c1402585100c8150307929400c1c0907001c8000b210003c04880311410304c0d031402c1c0c1c03260b01d0006036a00d4080c0d4010900c0c000300500d46140d12240d00002c120070600704403c1584400644407e24110140c90b45484078031152001d100c005100301c0f00382420901da64411074600480c61241c034105003c071910070041c03e42d1002602c00481300302c407 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 932540350 1250 932539100 932539103
    0x8070606030807050105091b1e03100204061d03070b0a0e12060907090209030d081911030114120c190504050901140603030a35070816020a0503120a09 66
    0x600e0100c021080203100c0703005105550007030300240a551259160251150580e0a02c2100d1032080e00340c0940c0350804000900100c40320014008617025100e02207401c050581344480c2c9804da0000d0240700440c0c01103024403080c0e400c141c0f0807c08041c5a004030f40e81c0e07039640c054000d03103400100300001c0c8076100d148154810b420240c506929503280f41c42155644006490802242c02441c4002c01c02614074407c0d102c0c4190000e00a00c222240a10b0903504003002070160075101c03a040440201400d050700030b039190303144408a4542c0e2503140103540c5d5210382ca100300ca284250782007120b050912500042c0802c440340100c4545c5549225807000c100e00b0a1103034800340d082401e0800f003202e40c00c8190b01010b002102c0300c4041446a0768041050380381e1080c9080d020100d01840050780032501c2c0051400e143d100102c901d000c18480c1941c080707804507811120b41c3c001a09007001c018142e1002c1d424181d8011036400103001600055450f1a12401200c03050094a805440066012105074101a5600703 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 932541600 1250 932540350 932540363
    0x6070f05040b0f1b0d08010914010b0d23040b0112050d0f05040f030308011e1a0d090c2d06020309090603160b071b03020d060902010c120f021507090b070807 69
    0x42e000000c04d6490300401c04031000460102c000006541030703a4043d00b45000c5030070021210a03800c0c00f40d515119045035410b48074840c0d442146400c0481c42114001c3c4c2d4201e15011254035242c9803030320b108203220503081410240c04020031900020710005010a5203032a900b401401800110f0f41250140280d42c402c00c2400300c001e000000303141d0070026450689007544007291f0343e046070b031903681811020b601c1101d94000ca100350108a5000120182c0081410b09102007a40c10480d21070a0b1901c5054114140c07954003e11550a00c0c030340c0d503110407400d10f50400500751003032405c10061f441c2d001700c0c05020f02403840840092000c4ea803c0c010305100803440c440c039644a076103078400300d0f07440c1c1c0109a0444030701800c1d00c03042003021102e404901c01c8950003000c01801802947d508005080311510072418014076030031000c00a0114144d0b0510611181e488a425001c01d00009140c4450600b69a044d0b092200600580d547d2100309201035500d00031000da50b840c400c4c9815282482001c01c05020f9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 932542850 1250 932541600 932541637
    0xf0302011506120b0f030a020603040c031a010603200a110c060a35040602072325030b0f0423030a090b0c0d141204060c0206070f05040b0f 61
    0x220380c101d600f214040c00403003c20031494201030f050140400742c4201c2d0540c594015040781005140c40d070300950f0f1043c0328140c850b00322980e96031401240b04000c010880802d120a005000031a4544680207040703080041c0390042e0f4200105001d080d10800d4407440070015284021070341ca07401000174521a0201910b85075a4109841e40105a20045c20082d0125120110400b41030141401d0107940f0b40003c540391120f42d00d8990710a0000c0d4092403089502c0e85100c1703000a940c800543d51180704003000300c05058006442140c007489a01910505d110710990048140080b80c007028840780d0001c062850040951100d082c5184818181501070390404280c110003040100c0202c040c01e0a80c0030380d01c0300543d0359100d282c0b4403c10b00880f18400c60310340c0001d901078205445902200c55100c4002e01003032400328142580e0b003c200b002c4170155811500d03844e035034540d0359040000755070104c41807400310728240c1b140c0d000034071501c1244203c105000c001f02d03461503910a007400311a8440002c8001c0d406 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 932544100 1250 932542850 932542859
    0x1a07050a06060306060806040506070815060a090602010f0e101d100b1305161409122b0503040b0606090d0308042f0618030105400f03020115 62
    0x36042c1404200d035500d0078510300151880002078020300480d404009044580d403001400c8406640003000940c072034002c0c555103291350325190005c1c401d40740300f941e88509403420a40c010b0b00392225803100e400282c0c50030410302d5040c100841e1070141d401c0c2d07801c404180b80120320445c2080b40944100300c2c5e40b038003842c03880940400703031544007644003401542c403d0f41d6550f516007854221a0304945440344980711202568144e07218041c1c002941003908142400c16040d940030a44480030341d9070940c2181d0103000706d4480280c90b200c201d11241c0700e20903d10498404840020108d00015000500c508540f0b004201c2ca952540c1c180c41000d58003508100e60344c5c1c0142001008088240e405035100450707440000354104601607488080c6885116001c110b041410920a26034001c11030340595504204203560a0354080c00f400e809142c881c00305611622688080c640304000a190038515502014514ac1c0f40303020b03090741d48140b2034210500800d12449824140d02500a0000c0705c0a035a40340e060109 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 932545350 1250 932544100 932544113
    0x3030f04051905181b030f0f0402240405040501080a030203040621050a0b011d22090b0c090a1509030809030f07080d1b11271314060403091a07050a 65
    0xd12441d00a0301800c103050820b29100324600c010703505e407d080e03540d00001446103030100c2c4440da0002e10140000c0c0848050b0b5130003a0100002c42031480c0c0d031700340000342040780d0701d010300072103014150440140c01c900b0900d9a010755644590710485003071003c590002003245803041141c255100c0034200038406490081e515000414610441d07601140355052003091010100921500c6150060b2540500141c1d146405544c0c44032070a4210307241d0340342d0001c070001500c840486405401840d071995265602c170820000303010760b941c01801d004114810a5403120f90712090010840e42c00c00c5040b030f40d98010728080703400d00d100d140b00340c0d59521071502c0c00991b50200080801000c82c45030340390700561039074184a031450b0700c02210240c030500b07102d249802a0300d0850300d14944803d803107950400c1e01701100401d00da00c0004540b00c80480e154405200c091064440d00c8405d45407500c0c000c0e00c841e25007585c02030030701822405800f5a0710302c1c58403014042650b070421a00c0c81c0342c006046a2007825280713401c5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 932546600 1250 932545350 932545399
    0x30f0a0513061701172d150702100b0a0806070e040501050f0f040b01020313060e18070c03030f18060203010311030304151d0d0b0a05010503030f04051905 68
    0xc0ca00c000c00e9820002d5074501c01c40b03803d142c510b42e28040191691801c4140051400c0e140d480007007034003420b8410503201d00c102c441d517104007100705400780c031150042d0803143c1407042e941001c0c88000c0100742003040e0075502140c4258084904040011401001c4020640d1480f89411080c03aa220308414004580d4100c460100840c10841d000d000c00d0303880304c0074400080e1800c00b02580040b800c0307a15500510301900000e508400c107104890811100c035a1350741c2481b8882c0e001d20b000c01c3c90aa052041400c2c41c11100191144801001d200e5050000300180811900780300a4101030b40e40035485901543e40d0082c4481a401c20515007645042d42070110081d4000e02c0103c406003030341505c208040c1000710035142100c0c490703050614400b290280a40300c12500310150341c0c4140440c104803d05594040115402c0760081440000c10310b0103a07101411500d068100341d1080c2d10510070070002842610440f410b68a003034034401c2c50401c1c00a078100c8070844036040140e0003a40c911421440700303000001c8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 932547850 1250 932546600 932546617
    0xc0e091501090e0607140d020d090203030412050c09010510050a020a0b090309040b09040b1308090607150e062e211e081803030c0a06050a0c05130e0603030f0a05 71
    0x940e90140c03207001e0180c4146c0c40741014958014002d00c50142001a40e41c043c0050841d101c1004c6034011403603000a05540c41504903010110140003288103000040051000e0390b80e054544018950500000a079400107508040040110005400e10520701c244074443c03200d40c0c800584405030500c429180e0326604072848441c01140b030804940c403140f402264003400390707801009125468840795940700e44080000015074456908010031480303505c84100a01d80d513800785c01408680c000100b103100580364040095040d50b072004080c8070140d103100103040c01c03080100d00d407001e12142c40d6410604d0100300d9030240e50010600c034000325601c51b110080c00d2007541310307038840c1007001000c1e01ca408510300300030409003e4810a0000c034008010b140808a121900241103e00f0042a01242403811660803000c0b50015100c0d400d200c810b07040b902a032904040c660401e41e0402404c6030161040c00c480b8400c170441001d50001081d021344082c0102e46004030710941c00c6a99500132039000e40943d00c103041 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 932549100 1250 932547850 932547853
    0xa050d0921021f02030705120c090909010b0102060c031909050303330402090a0803030703060302031b0f0d171612030b0d020108040827090a090c0e091501090e 70
    0x5840707114900c00320341d00b002800d034550400194a1002c15410007504000c081106000c41001004500b0228000341c3d81328039070400b07486a40e960ba600034042d181c90080d0244149a05142e801e0b1a1030f80c0118809602c940030320001c9440340e070341c405d032030f04955a8041d02048443ca40202030040c048040019841554141300718241400c1c0180480300300d0702c199442911940c00110142d44c00e245c941c00034560b40710001c11034064151213040032400c40d4020707103486020982c0d0700c00810071810180701542403040101e07040150000035401045400f5040119140305050301e030a0001044500c05078490b030102c1c020302c126160303000307828002003210300001c2c15541c4864026610310010f101e03015a41130044043c11030b030840f9501c0e900640300000044d1045074034917014081400d100c003180700742042c0c9040b40803a0b243c5a400700b900b44125180007814004025083c4150f200103e00300c101000219140e110780541e00f0354805403a5410140150304040d6510808800001c4005042e049085081035500 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 932550350 1250 932549100 932549153
    0x60b070506060f0a050901031b03120e0307060201050108370b07080f060f0405070e03101e0b011e0e030619050603070503070605181002010903021506150a050d09 71
    0x808011881c203440c41917075889543c4000610004a01d05800d29003015284100750308581c032599545004a5519156000184012a807001d2441c003000004004c0c00d450008100550400ca011a101c0e50103043d40d0140480b00480c554800c00380035142036800070400e03009000e003185850014113114003a10807000050007080401e0b0000b5641c082940a08030042500c6401c1c2040d00500001c0c6c0780c020300c031005021a0a4000302c13039460a10114200d2100e459000415810000d20000c580e03403a00c41c03d00c0c1040c0b82018654542e40c01c1590700e031402e0b10414040000e17206101e4219510030030340c60310079014016901400030740000503401c038508a8080406000b075581d41000e056940d00d0911605505901100d8204070a40c010700c010600d1990a2a554140051050204c1c440181e00c50300385005039075400310013041c181c2c103001c901906c1148500d4403019051080018070314010b003919070500e00400041f11038040d13020780100d408076002c0603010311542c41681002c05100f80a6140c1c01811003014 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 932551600 1250 932550350 932550379
    0x9020f030124172703090a0e1302060f07080f0711030604121b02030a12110607050d050703061e030c0506070206190504030b0109060f06030c080601030b04060b07050606 74
    0x184804201d9070711591000301c41004101482e00720341011300340007000c00155291541408811012001c060039070802580d8410100c1e0078810185a03682c0b004000114603c02e200d0300d03a00600565101580441c1d085490b46d070200c400b00b05501c0b80c054000e0200e80300088101c083c0714801d02a08140303001b4003003100c1101c920b000740754980303108580007000302080d6144045102d005402c2190410050003000030710300440e50110b850211108005e403020481d64100300d901c0d44d4422112138031020f10a0180030755080c84036001d0603a00640088800721030300c5a00007805284a0340c003a00007018078071801d0108103007030b801c0d103146c03d192400240c0d00941e9884004c0380600b0108211104c0301e0f070181500303240800c01d03600e070100a100c0329030b4117041210401001003ca6071500c9158040c02250308000341d56854461018195126540310005050801140c4101d20b6000b079401da500040a086c08504411031500140042000d504210900400825208144070700010342a22580c800d4910501c01100c2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 932552850 1250 932551600 932551649
    0x40210020312012306040e0619080a06090b0109110a05030903130b070203061006120f0f090c0f080703020603040b090a1209030209011a030105120c100c1112030a030e030409020f0301 80
    0x482c01100b011f4440080130034454108821500c542c0d0010540b10361003a9200c1780e040b070809056049c241c41c1992103001c8403082c44070f010003a80c010504240104081000b22084121600903841c0c20028007102100103605084223100300c4245030310000d2101040364503510418802d4000c40302c20703400382c800e60000510004524281c8402e0b140e0644a061010702e04a504002820b14440d24100c481d0300c8103030517280018280185a0300724850300e428050b03a030070200102003540150340100600d03030041d0000c10250f1a00002c51340c1058200e80b03005425034807445050b25201111400030000c1c4444100d00e40001d9000140c582a03900c220755603022079a0b1943c03c1c40301d003101212503250001c000c000402581c9000f07005611200410000c0c0c9031604501c3d1b00186d040c03510080d010010480c0c040c90b400400840c0040010181b8040321020242140044c07403035581d0040714114400e240d65071a00307826500040050f40c000389061102556034406e6150380c0d80c6103070003e220f4000c03e442e5550701401440310 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 932553956 1106 932552850 932552857
    0x507050409080318060411131506180806061c170310050901120f11031009140d210519051806100509040210020312012306 54
    0x10200400d03600861010102c03401500050b0411000600e8030311203081841c400d491010210b81c00800c5540281a902400c40e4048403100d80040c4059000701c2140010b1005050014be040d518194103035901415180507901034401381d071822800294040e0b10130203900038003900c500c1c0b101c58840c1405030740c41a990b1030004034207003100340982d04064070b42c0390040c518040103040d1241240ca45078a40e4410880040c642d806a016012655908001e41c40381444551410080460985030440c000124460713075032454007a909505101e64016424001007a058403051403c407400d160028009210080003580c046803600c070f881c4000e128a1003040e01c42c4940f0810306814242d00d0030040d20703240c8000c1022552003030310b090900c4240c40d0b503a101ca401c144d058400401c00100b101d0161b00314000c14016400350b009520000800305140d0900202c102e0041d6001c44041c40840d00b407115621 = true := by decide +kernel

theorem cover : BRFrame.Cov 932374100 932553956 := by
  have h0 := BRFrame.cov_init 932374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 932374100 ≤ n) (h2 : n < 932553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
