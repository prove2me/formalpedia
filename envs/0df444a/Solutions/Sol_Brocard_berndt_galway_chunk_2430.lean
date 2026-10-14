-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2430
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:41:55.521567+00:00
-- url     : https://prove2.me/submissions/4a126ad5-ad50-4add-8fd1-d53b53b69b5b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 436870503 ≤ n < 437050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 436871753 1250 436870503 436870519
    0x108010b07030201020d050403081501050c0601291914130501050307021906271115090d1b0815180712050d170702100905030418150902030402 63
    0x8001189558040d01c0c0031001c65600f04400c804a0486103c1c43d0300860003955186400c0c509a258502e00c12003000060381400404d0103c000c00e41340000f03240b419580c00f6260f900d0018400303d001d180721980e00b03400054074880403801c0346050640100c0b000b850f4419644280b880d0303011500d01c3d0001d104041c83e101e03083e000d000d004d000310350081001790382080c4030b4411280141401c418002c510744420a04981c800d480340f00040381c00c003281d030301405503c0036100c411400580c0c1d07964001d1051641d10741c10b80108003081c2d44442c0c03601160705440004030081e00c82001c200c424a05901c00b003416102d03072f0b14024034807040420300c0c220004022107401c44041000c10240c643d4104021009561180c00f0410302c288100840c4120b540045a0001c81c070590080c900a4103500b80034020a4000c2d0f40125080782c806d04018a490f400128039001a01800b00081c0c041c0850400702e007140b28079000420031100f01c25014000b8205640841c442c00e4038032441c1c0780c895440d41e40070700503844280c4010b5030291007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 436873003 1250 436871753 436871759
    0xb0f0d02040c050f1201051008071706010c0b0406020c070b160f06060305030a02030c12030708130318180f180b0c070605011205012a050a021203010f03140c010801 72
    0x1c0703540078405084103420098100032912a424040e0751129110340d03c802040c1004002c40e082c035181c8138050590a0030002410701d08413400900102c81c4143e040c091844241c04a4001c4e4010148006210341100c10b5414510b07050906c04080c0d0b00c01003a0720b1262042140000311458005d065801480d125441000c0248a90700c0e800e008891050301070711080d9841500100080b4108000c000007039003900550b4441e84130441c55030808045800c0710020400401c108045190b210100c141d200c000e03900480b0400f4203a0074111440b800321000c9803506120f0b100c000ca0017403481d224244403000e02c20014802c65000407440400ea50810401c05ca4141909100358001040c0c00c802540c0449400c401e45c1c1050b803180c558409481080e44804500d0f403001d000b04051001c00e02950281000f6903a480c4610400449040f5101c0c9920f00d80004000700402c03003044240c404c0c0321034a01c90a06844490f2256103e41c0c0d00c21008115200c1140c12022030418030104510109550300c0300c05050312040c0860b07107 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 436874253 1250 436873003 436873009
    0x7050f091302100507110a08030d0e0c0a1202100507080a050d02070b071d011d010c03120c090302090105030102032e12050c1f050a2307030e03100911100215190b0f0d02 74
    0x20340ca428a104a0043300310580a0b600c80c158240000c004000f0024100031140c0103001c0d101c8801d081e51420050100700140c0803440000450b0000503503440c01c03940ea00310100d00480203000720040284400c5040041c8403200d0b60004224014284203103540b0a0b1492500040d555480380748082d07684c03a00d4084000c0c18640c00380a03490603540c000d0820840ea90308020100f03088580a088541c00300707154080a10079030030030740341c0f1902504040d40210b24509218400000600791205600700100791421288000c0760421110b10083c01d5502066003449910b141458a0b0310142c091503005402071000b800700b007032140712583c24240c0309403a46440c001284004498010b2403c510100d241d019543d1100d5000e002c07401403c00501a0740c0f603800f411141e1041500b007800c07581c8845241802c09050401085503030000710301691044074a8540c41e819844181d00f84841500845c2400c001001041580c04801c2c05000c1441c4680b04200103840040040241070b10707442400f5504206003000910041c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 436875503 1250 436874253 436874261
    0x605060a17010509071d0402040c1101110d051e1b270102010c08070f05090d05010212040309060f0801050405151509030f07050f091302100507110a08030d 68
    0x400152840031810744415800d04001840c50069040740c0d55901040168007050010708050a218400d0030900034445151014541c070151019200e60f0751203002603039090041100d1044030789084000e211038007085129100310380200038a502010b007041d0008030b0200300080160b4440c4046102c03450140c8620300c01e2801220200d1020b0039030b4904000e1a20340050075075202550b009070303103510b070403242c40e040c0020300303580d480c0800005000a0301c00740031409410509442c017540c15894110344030881c50b03002401c80900d9090103407081d44000340b100301d1440c1d83c0403414825806038440c49117581d41c5840c1282c01403071820381d400003e44a500140711500d090b03000305400c070004c0b0710008401a205400580d030690f00e003000080d9900006854403035414140100080d05a0f100e016080070351504c0c000c2108001d840c046588200c040d00c0c00203034011980001c00030055000b400403600480304945c00380c2981e000ca0700648001510031303030701d48151030140172800075540803c001d14140182e40e103030780001d4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 436876753 1250 436875503 436875511
    0xb06041203020a0213061d100b0702010201110c031e130b030402010c02030106140a0e011202010509060408010635100c020c0d08071109041113110c06011502190605 72
    0x43c02007401c0c81001da0f4818403a90421280f1080c0040c0c61483c00103028071003585209081e07410b043c0e0000700641d05601d01028422a02c3c0c5020702603851b405032004038010b06020302841c2c5541d43c08102030340c501ca030000103040d000343c2407038010990b2610750100c81001d001d0264030841000030240706116601c400c80185030068810304101d20391820036030029007562215009101c88030f852a0100c003107450008140c10080c41c00c0000a401c80d4105030030a0390034085128003a040c00000039040b00541c507207078120b13001000354600030056945c1303c0300402c04900d07154400d9024071316460801010b180180c1c46000c00ca01c042c400030b00000c0d1410b041074002d4046403810350b0950081c100ca1203269114a08250380041c465125566a0503862401e0101d8400b90312440307020310000002c04c00000c41b60f0448440b0310000b01c81c030780314511800341c01e10f000d00b80344000d81000031b40110310b1078640640000c040f410382e148800b40091500b0a0700301240d40300480c1525220a05842e9042004105564426030700 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 436878003 1250 436876753 436876757
    0x50c07050103090335100303020a0f05120c010903030c050a050703230f0d050a56131a0f04110c030d050903090d0b250c02010905040b06041203 63
    0x42c0401e80310300c4c1505c001c0805c03c401145900c10b020010080040501030b90b209461401c9003070858150b840081d43d54a50600050280641d501a2024880108072540c1c1e10f492051450341d4030585036403424081c05225104070003080c20b10186c180058003d80079920142950740d110b0342824190380f03044503000140601c01500c404208100710710703800008000d0000d100c04110460b40d43c945500e415088a07001040a10781502d801c0e104c0501407044440c50022800c2020040b54114207400c090049a40d02000c00300c14040c007031085003640e01c80c13030317210b901c0998101c80ca076802d4034800c0300003005c3e10a003000103035021a610098260900e0300b20000c00d40340001a000045080000f01075109a500045140c00d0b940e001244498003500c160003040e50040c00303600035500300350002001ca1030100410000416008407180011040100304080c1d11006030b080c101100d007541c0700c44002c0c00c644050380040c0e0028100c21000304180c103040c02842c56180c0d010b0100c81c6007920b030028650103190030b400102c3c2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 436879253 1250 436878003 436878017
    0x603030f0302161401060f090614090c13060c05150601050a260a05090607031107060f0b03060c0a1704080702100c0c0902030f071106011a090904060b040c050c070501030903 76
    0x4110300e01c4c42d0280141d4120000519641418120000503200d54800003050f4140b40040c4445000c04140482160041d0b82e0800d994480517204a9580180c4070b04002d801d0342158000ba949a10540341c20b5041d02410030380d1509400000220101c5600b2201c1c94081030b403c0240b81c0c100c0744a15084240080c03021240134200c2c51542c00707041c0d500303425151070107a41d854000b0304c140b40c1414410203070402d46074202040f074000c05902041c1103014030740c0b0203884a6502e91000600f8826a007000780000302c010281d503030710b00e401c17016486a40c2101d8030890005034032200341011b441410500c50300507074015205500f096101c0e400c0040c4c0d96a024140030403c106203c4d100300140001802e40042c0810420150b02c038580b90f03542c40f41c45c000c000c0001e002c0100764000814024408600b95056440064010960210b8168030309504d1003a04800758110020904200c18040c55074810402ea21080710f090141239065001110350f8000c1503071150480e001000700704000c1d0b0090780005a010701c0307420400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 436880503 1250 436879253 436879297
    0x6070e060c0624061615020c011d0c03070807050409111e010f0f08041103031614060903040b031f0b070303022d04060305270d120603030f0302 63
    0x2c0c1020010b840e4140828042c9801e028004030000214146042c2640c466052000c0c04051445900d00004041e0805200036001700052130550100c1d2080e524000003407104041ea581c07034194074003824007042c4070380c014010000501c1c80c010411108031070401e4014007d031800d11042000a1070680c4e021a1022684c48406a4a13181d43c046903107801e100801008100c880a40050544522004001c0802121061880f26160801081c540003a00300b54070314090700300702d00802c0c51480740b40580e00305e61200b210074208015400070503108000001082e62020786403031043c0769403070207140a0800791410034400a015290100349001e07040c0300c1d54a124100c10f030b4450110030181c1c030080f4198000380c0c00285481080c0c4034010550319200c0001c40907002142070306007090450240c1d001c1c0408050301c03078000c03805055501b1001d1b0700e4100808000e11106d920041015543d011600b807040104492244458500c182c0c2d2240c4c80840303030161984207550040c0c60084000307501941400c141c1140c156051 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 436881753 1250 436880503 436880527
    0x40605220b0c12100f150503131401020f07020307050402070201050702010f1b0b0126071a040b0c06040308090c06030103121211030603070902180910090903020c010e060c06070e06 79
    0x604c0c00340c00f1610b104281181000f50f022207500464000c810703400fa2940c501021190700000f2298400e10901329405126031520381031760261001c0d000ca0f5450740c0007103821501040588020100940300f20115402240d9810501003039008403000603020502c14488403002d035000368401c1303001603030604e41181d1000030b032404e450500c1c080322010780b001909600107000141d0a22488800105128000d50581c40c5144c03115a0310f45603030049035040210404042610703011032041e50003802c072007070764a41c840502c3c5000980c1d4039401c58080e000202c6150101d00000000700300380e03000280c081d095500c1d40e030854480b40c100c1100d211008040044480703800e90401c04ca403081c01000c01401c00110390b28100403007051b2401c21550400800c42d8410448040c0c04c60b00102d008814510507201c4003442d0360382c100603100c0900c103540189203d90501d031028040ad40d002c0358070746004200340c98a520201545044c4421400790464924032540941d0200d200715006100b02411214001c100b81e250441c00b041c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 436883003 1250 436881753 436881787
    0xa0809090c120901050a0f090b06041509020417072111060c01181209050334030302031201090501030b071103130f080d03110f0c0703020406060206040605220b0c 71
    0x40f45240d55460038001072124038042e4a5500100740424499840d0340d8540348162080940014800c81c0d49a030425011505000f801d4002c0c1022081191940d0795000c06062000c0500c6221256000b540d0002c00c4560008400c1c40300c104801c0c0400d01508103a545080c0b402c001c000c40181d01c010140f2149481ba2024040c00c00c0203100d032a0740d40800b0100c7e16203070442c645048005001e101841c4018001c0382c40004c1c1012954401e0107142c040c0090582c0e00c0c2140c6143e000510313031141c1c4030450100038960000018552658041d10700b400d182e07660007002088500070301006004007199000701d182603100f40c06102e4803582e02030070b5070b140805500c40b1200010055022100138004d4040403c2101c8090105031242c9680d81000d024540240c036902d940e40c03088034103031201074002003203401852504001210243d075003d0001c0010f60b85030b0602035512501160304850320f6007802c00269403080700713030b6907421524101d40c0703185090f09403551000c140b40300081515540071390500a04103145840b001c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 436884253 1250 436883003 436883011
    0x113d02070804091a030303090a03030506120303042906010504031202070e10090f0b01050910090807060905030d020a38040809011b031d030a05100219020a0809090c12 73
    0x1000030301070502e56280c0c5213066690040601c640c01c00c0c400c01094490116407200d030b02d40e040c500040c9a41c0c40c000051540c2c00144104410351001004200c100520854035110b039540c0342c0c3c038078150a005490404c0300c44800329199800140c0a00040000440407400d480f030484d641d0043e1840e80740c40c0d0310000c0d0605001c907080c02e000b115074401004043c4191040309016900804148120340e50400042e2132032094850850086422003038506140788181041c102804940301551542541e4034001005101d15001e101e11a009060b01341e60b8050000034108417007039001c0d0a813000b8031809a001400c580c5148030351742d0300303103480a03480c815004110701c500d01c0340744205d00d104e0f101c1e142030000515455060b5401a4228204070b07544006c07a8001440d10b16078050014580c0b007118245011034185030101074014841e101e44480c1454060060300501501c100c411403201584103200c10499a0b10702250700940000c40030070514080d4100038040c0e80d4040d084003140e0389030411080e428035130039504075 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 436885503 1250 436884253 436884269
    0x3030b03010c0e040e0102042d0902120711030c100c020a050f0a050607050304050604080a03140f33060a030617060f0a110d090203010615113d02070804 67
    0x80d40040f03480c030f00ba200303840d21001018001c500b82404c1c4903d0705480802c0c280c001049101c2c0d40030303110109050000c0c1c1005402005000c2d500c034000c0c0a0851162941920400c0204420b080c0388804c8031400020f03540c5c152088801003034265100590344004004410080f0214040c07022120003141c1e08000c0e450202c00084010108a401030070614244807000e4400800c120040091002045000039aa500300b40c2020460307940d007100d403505900402121f03038102c0214085100300901500e101c20780f02d1003401c40c103004100700386000500b034080c1c00d8403000c09442c24050350180d0010b4100030001d00b5a0681c2414005085911110f11a810031828004150395520200400990108080e079a40d08004400424818000c041400902074002c9100e12440c4644c0c3e011a441556025080040242403c07a5810290385005800420300d298000341203c2c24411408010110181c028001c06500c113103c0c020003103a50800898420032841c4006412296001d02020010910910081000701004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 436886753 1250 436885503 436885517
    0x4030c020f0303160c05100c03030b0307030209130b3102030a020402040b03150316060f170a09030e03060912070602041503020324010e0103110708030c03060a0801090f03080403030b03010c 83
    0xd00e0481c4844085402c21801074452100425502c8d0f00028003c2d40c15a06040c0401e408044001081c03504c000c07680044c1d8821194801d022a140f050754400030554059829241107a4840c85075103000e0f40d0942c03610301c040c401400701c2c03000700003107141c068042803005040d1101a00540c00082c01da0308550080385c8010000418080c0203903074584402c480d0882a409051003182440c529205003180740300d01400d00c030180300400c80035481481c2608201c0e080f070160395480d0030309081141c001c08984d03904070082088d036041d028191030009400c6119650361070003001e180040002a0049411200c3c00f2180581c0a01000c1600303d0003090520031801e00d83d80040e103038030301313803403031480301400d0f039200302106103890300402216644141c007401152800e01300400c0b010075070004c5600c00d01c10080060b00001011041c030000d1200031000b5400380f0710813141505019210013129080310039200b0010b008000c80b00e0795400080c01082590341c0f003806402c0008122021901182c256101070949100103011 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 436888003 1250 436886753 436886797
    0x50102070e041a090307020d030306080c1516021801080a0209010e16050307210c0809061003150b0d14010e070e01120f1703240904030c020f0303 64
    0x104000c10001800030300806862400c003501e81c04603240c1c0f41d807070409800451000003041e10200f001141d140d15400b808080880c8030b0b50030b004000780028051000d890151003602040c501e03040c00200c03482d980411041d850554801c0782d02c40760078218038080f6048070000040c01d03480c0d2000408640204507100c09800e00c401e0510400c040e1400c140c0200c0c2d950213142d03007400701c083d0304204000188039150500b541e894884100a85d0241c0c0400302105001c9500ca070b02890b104030750303000050541101d8549a5003610340d50811602c0b4102207e183c410700c5100e9004002043e200ca182c55072100303800800060060094012589903807100d6015903844040e4042c01c00000400d125490030483c504001e080c120741407440c260f840c031b10107216443c504864003c4c04003d0080811010038442d62142d5403918070712070384240100a0700100c1c1c1407a5031820900300b202c002c0724030302c0c4c0c29010414010948100c503a0360356130940b01c00712018070590300603160700c0710010b207600d080004101c1c0403a010810007080304 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 436889253 1250 436888003 436888007
    0x50105010807050c0c0f0a2601181e0804050d03031a030d020c210d0809070509040308040b13060222050a0f121511120a09030806040b0307030204020d02040501 70
    0x3a002c1c00309410090100259000c680020441c0810548221a012065400c43c00010b09040c0c09411018014070540580410b40305c4400c008802c0803500360080c48650700100e40e100b000226400701820840c110346490004020708070b00c40713240f50710600107030341866255000b107103060300c0f000000c601083e42c404500c2c4500c07883e451801042141280109072030035600170300075100d000d0901c031140540405480d042c48040c0124038132041c0100c0b002200c1c002c0e500b0b628001e25809040ea050545402680408600c60078900e030058800c0c1d8041d00c0300b0190361071300d60751400e20340401410003030080c074100c1850323000404a0008085492560644949000e550200c0480e03004440e802180700d8a0700304020040e400d504040801154480790b0200111000c40c100b12107295805d0000240300351400550894400c0d07250b000d4000004e0055040081c0d0b070307904a10754101d03003070b0b22070190200360942e00180e0302c1d2a094000403035425000e8161800c103990799020a090ba0401106c4480300b40d00810103100550b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 436890503 1250 436889253 436889267
    0x303050c1009112d120118061d0607050306100507020904061a0303030f0a020c0a06060e31080a1701090204080d14180d05060a050a06050a030503250b0a05010501 71
    0x55286200e164403862032804115504076021612402403035010a11700d403440c801c0d4407403d0b02080940380c0c1c00134600285421f01c010404d0580b800c65074141c500c00000c1c003040000300c03540314011a807039007072858964104200c2c01900710342d429020071400704403500068070303995406402140320f041d002c141001c005000a501c1c40d05482928000d034418000c1040040103441c00301c0d08150101c900684d00c0041c03400040c140340c44460040c01c401c1c00e002000600922129440c2c0c407800c01c80141728124446821958075a01240011070402110500365034042050440101081d18207404e00f0401c4084000340c070f21401307409901280400b517010070108035000c001d1240c1040c0c510189070415008000c0c0f900c4080500540840d03050614041e201002e198549501c0b0f000b070582c10030115600da00c1d11b0201c038809084119001c1881c24100640003c890400b1000101030340d07071000145062441a88291044405030111700e08000003c030804c1e0086403443c2210781c018803405d10089110340c1000e001415203 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 436891753 1250 436890503 436890529
    0x1090605030a0c12060e0f0f010b0612060f042c010c17131b030b06040c02280813030312110301030c0302060a03060504020f040302031903090303050c100911 69
    0x2600030500240014850800310f0090300c400980c444903095107420705c0e0700105090b150701c00c8180300f140501c1000c1d010001c1c007604400195002807004007c00b8091208901030f080c00380300c01c2d400e010702103400d1385818444418407003400f44c800181c2c0c0150f2401c20380407070842e20300040d1000410072121000d000078000d6000760700640c1002c40d0308483c044071404054200810000500850070035442c100484151069a2400d0308002d4401e02d688a00b4110307140074080d11b400381b041d840c0616030103545001103542c1d0550904203070744914001d0604801031040d81641c1c2d0464080310708101a130350400c04031020801840c004e0b0740d0b0707214146480c03800008440c0d1281681c114403101b400104002218007203550242c1ea41a80e0031034856504500c154042c0007240c1101c0d50090001c1118280400c110000e0400c9a000310220b4001c480043d206900b409449907002d0006503000d078050004c41d001d07200034254240c2d12421070740d84a42c000c03103031001c45200040403929008030215000c160300e4034824844003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 436893003 1250 436891753 436891759
    0x2101181e2d140f0906060d0c0e04060527030a1b0204050702030c061f05040c030207050d1d0103061827051c050306030d080604061a070209011e09181a01090605 70
    0x904d040c10910703180d403044000e1402c1e20403100907445000b04800c07980b03c1c000030f00c051032010b021803c203450064040e20049503c0b81240c0c0191810300d0003804a01180c02141110501444c03910240040844a0766081d0800b08190046810300c1401601d56116003031113011a507004e9925003903c1041d043c1810340290813050301c001d020002218803e0755800349411030b1001c46000410031003894041d000ba0060000160241c0282d44000300c80380e810204406104603000015680e407190350005404490440c0201800c4021000303e5043e456060750001104d004c50058000f01d591554034100601a1110802c5620743c111480003031b202d85003030010560700c0324941001030031803411b0000300c1d43d00c100e0f00381e10b07004102480c2d021900ca07803600c5d808000604141149032082002040e000c44460780404002c80c0104c03c05400010030030031000c01400d00a840c521456266403900c10075902800005040101a01d040000741c0000790b58140c0c0303010241e000904d81c8a040d8540501c9404549040d170003140 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 436894253 1250 436893003 436893031
    0x4090c080c0a020d05030a0905061504061d06040b040b12150609042109050a0b07020906100c080904020f0309060f0114242101181e2d14 60
    0xb09a00880e119000150602d02283c40b5030b01c5420070409400884000b4010340103550900441c0040e100706840c91301c1d010f59042c40482c0e6103284040280306907810140000d040c810200300213140c1904041240c92000b040490190003c80000d007444400310502d4140d5480740700070100c03807000c059003560302c000110b44810b4645032548640003040d403000402c2850080700000403200c4e60007a04524042c05000e48042485a1a01d4804002e030f0310807001a4464005c0400182061134800300d000c1070f507201d030b0744c40744140c02d1144d0310b501c001c0c0c1040342c92940c8241c09000d20110081c22401540c412300f00800109040d09189081802c0c1c41e5040c0c21990042d606020000d00d15241e0050018150016122040b80c02c140c0d140c8041450082111350756800806070040c40036194000d011505842020307003142910070031440c4800c115150240f148180d403100c001420043c0049501c6184c40020301d50500c05080030100c100090455150601c1030501d07900e014100f492a018070210340c0c0410352511101f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 436895503 1250 436894253 436894267
    0x4110f010509010309021906020a0b150a050d0c0e0c1c0e1e070e040501020c0706050307120c0516051b1806210714012a1101030e0304090c080c 63
    0x8107103108000c407040c1410f45070b2084108648030007030070407070310307000c41202d200c112340c55442c0292100d520000985134180e544d801b14410328150180301000384002441e60791600e00c2c01040c0003500d14400d205448030200760400140b414030415403030344a00b00c01c03406996127100003d90000d80d080e2200308000c059280c8400ca185415000543e0320071081c0300c8004030380c1d0807101400703c0d14040710754222541d90040c1034140001c001c2d054000d4032004019074140d6200c140c0b01c410407078a070301048800800084c00000e1610b4421100c1e8420204882185807241c0b81c2001c030300c0c0b101928801c1040849081d4084201405082801607504448820840d6400c2d041c041600324101000d038003516141c4a00e11444089070f10444c1500c810136003c0d4964243d643d583c3e41e401c41c0203001f14648112601241d02c4810b0b40001c0d800300800802001c0008840d071228586644515201d80d512682c40c5050554854070b04654540030406403000304103031040070030f210b07004000060420202801850fa540f00502441e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 436896753 1250 436895503 436895507
    0x2010b01020d0305060a08031b012a050d021b0c090a06030818121212060f0102100c03180f0512040503030d02160c0608091c0e0120120304110f01 64
    0x840005000b510340498551035030f000148034411254030482030780c400055414030b261140c8012003d441201c82c0200700c2d500311070345000200000c54680d095621174810302c0004403030158002d082e0040b01c8aa0050603d403120f03180200098640e459251254050b11200b03c1c80d01d4003045840d4405d4103420284a01031843d0385204c9a4081d440240d440b016800d0301c244003907144c550b040c016540c2d15070211152014a1940e0302c000e603001b0907415203040606400074165040a25107401c050310103074020710100002481100c014044420144205501c90381c004400e041c40c00ca0514141e03000b0040c8514654446c90064a411b590b9250801043d000740f002f00115900402510300e6913100d810b000d0b944886040704031030300c00c0c0c007500010318601e41c1241c08519680d1041c01140700e26041c000703c2e400c1d03c40c0135001d030100d45260b00a0000003008014418420752145214031082190203103000c000b6004100568202440b95200c24800040803003000280401003d01c080a850207444417003a91350b0000c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 436898003 1250 436896753 436896763
    0xc0d15050f011d15070606080706140a03110a0906030b150403020603090a081209010c0c05030406030e1903080f1e01120206071506090e0304050a2c010b031602010b0102 74
    0x401414400380383c0095070440000455001c004200401951006513009031400c0c1c141c10920041d24101d20300b810100e4054000203490f001e88015440b92000f441002203c90015440760101c4d104040d210f4002c0f90340c20300300c117010701300405c1c42c0c2d20759103001802e002004040b50401440d152250620084c0090103200b00b2049400340c940545013030f44d0b030703541d5480d0071031419081c070074018440d000005030161101c4150200b24060b221000083c000605150000c50b0b00d60712a0304040d045030410041009128002e500004c0020340c24001d44003c1d00780c0c4055080c0e060316519064001c24045410403000c40b8110341044da10140302110540b0042c5000161400c210307050040c603841d031041803520f8081d540d40d04c050301c1130568490b0000700c4604018010303101406851155901590605090100b81800441901c05680c40906000c0c011450b0923070805007040101418441002031207450072012503080c0f5107501811101e0102652800c00841c064200003c900d00c417001c5903d00414812140e0f0701140c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 436899253 1250 436898003 436898029
    0x20c060901030e07170a0c0510080c1803060c130e010e0f0a02040305101e140f0a0e1b15120f040201020c03070603091e030c080a030209090c0d1505 65
    0x29000510940b00749125141c240542c0060074014905c040789402d605000a00c0c4405603c1001e0395164565900b00b408200000d036002a008079010000103a0f401c1c1080c405018012440c140a0320042c0c9500301090801100752030844180c800007406c1c402d0ba480c034030007507001081200450404c540c5044c24032008844098001c070582400d08010070f10030340594054401641e04942501c56420784082114000d00a0850910700080c3c6001004482c01d0944606402c000d081c0d00503944e207a50b61800c41c6010710300101050205c2ea0b0340c02c1902000142003101e11464418204500141c03403100303040100c0d442044d2810081c020341003141c0072104501c18203460304140c5c1e130707044103000e0345032480181d080a050160480d01803045041c00914254103420000c0700900034000784010900b25442c4d2103004802c65005804a254500c04600041400004081d817000c03910b40142003903101400178070f10a80517a24003400c0c030703004a9502d250300210b106010262007105801004240780002151542400e02 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 436900503 1250 436899253 436899257
    0x32003030a050904150e0907210605090709020f0c060a0b010c060902031f0212100602060f071e050c0c190b1b01050108010501060f030905340303120c020c060901 71
    0x400c103052181c0301c5401842814103444040d01c401d541b03442c920708a4510884040000c1e2180200000341004101a001000110030030131340c6003891162a42409010042d140207000d03c25400e0019070000c461015000e0041c10b80d003095030792030f000c00e5260f02d0001c014107905891450454100008e0380c00c000e80107040741d881640451f541c0707071b640002424030f0000c2000c482100074a01642c020218541e0041010221407409103900742c461410b210003040007400781d04e000da40b0010100c0c1c8120f404140c2d641e40a0039900c0c00750f40700501320120110a00c99a200b22000c2480441c140c42d80030f8080c0001284004203072010360b01d45480d4a4558030000e1248564ae01c002c0001445000c40021b602c01c00e416520402e00070710940d40d54a07101d5008103400d2007400c0c00a804000310a0140740709010f00001c1c5500040204640350800c110901c2960580c00b070a403040d4042c403894100280c00001c104011030007a110214000c0a00308000161440f900403c000c54000c1c500d01003003580c1e0303d8207994500c1c90038 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 436901753 1250 436900503 436900507
    0x201111b09040201030902040f052e060503090f030408100c0518040e0a021206010314070308030114040f090308010918050a0807030c0c030c0302040f0b09060d0c05100801032003030a05 81
    0x43c00164014008001d0194000d0700709040c42c9000840c60300883d016000c4a4050002203000c80e554034201d03000b07448926075103500302c0300401c0307080c1c440d60185400003640000c0d222400c0c070008109195901941c030040b29900301481012120050348a800c9100c80e10382059071a0540078051403400c4061000076501c00c40e40d41150383c0c10910304005aa081e2540a4404a100f144c4605200d640350f000b440304035414645140300c411085008110042143d0b13003c1600e60070b41e403c1070390702281e4006441c400c90300190b8404022140400c1c9000c3e4114890003925410003d5040c01540010b403200360100324000700c500710b081000580000380003c40076400044094944601d40740c111007624911401421240c22164084188000000c0901c1102e208a80400080220f02d600c6c00c180c82c0c651740150f40c41411a00050068140f0a00050601c0d00c10740e003644600d034a03034000614a144507074000f40064040e40052007000403401c10700b80c41c2580e0410255840c0d918400003552031040a064100300000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 436903003 1250 436901753 436901761
    0x20c0109141504091e05060d1505040203102c071a0906041502030406080a09021008040213020f210103020607020d0c030c03061b230c0c1c0201111b09 66
    0x203410b050320094100444140203242403941110904014085440700030303850302002c1100ca140c900c88490000350300500214161011811080040900500582c1c2501400d035079404484058804e01f0301c1c0200c1903c45542d04500c420407000191109002c80c40217134013001c001d201410007280c0d02020414452031a65588071003001040c03882c01103910086000241d90135801000e9000720182040d542195a21782c025074401c8542400c1c1e8000d4907010350041034055248095510607510a5071040c0080d01c542d03400b00300b100518040b60301038500d0842d144004104525110f4031030341c008518072040c0400c01101c3d41142c001074618840c0c030000070700c00c9901c02040c10410a01c122803c00550b0003180003260b03070341d480c2040b002030003004003184480b46410029042050251701c0c200080c4210b40d400750420112040c5500b284c0d40001c0b2400340b9071188a0b0081c04a50700c100e61860b5000010a0b2548014254400902842c01803000c10b40f580d001980b0318010b0b0441e01c485c0780b0f403040d4119955407507500c03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 436904253 1250 436903003 436903039
    0x31e0c0b1906030213051617010e0c07200f030601180b01021c1716140a020102040503010e03190f0c030f09090207061d010b09131b090606020c010914 66
    0x192030f4002034026104031001d40b56900c1c10341c416446810614503001080b41711180444800c02c24004000c0c0003444800184040090344141c0da03800629144c00354074041041d242c4445a440041d0007100e11017091128007102c0c1498503841e001e2410030340c02410340f9410302000600c0301540002500441d0343d60080c00009a10030070880c2c0f0718684c3c0301c0403070701e03542400d1400501c028448a042984c1d620340c103002c908020080380301034000007a01d5589819a0144040c00c520551109648404541d024130000c61565000c0c86804d12043d40040117642c1c5070309000440d0400f820580c294024403a580c0075101c1c100790840c0c140040b8030f038180380c13000b0b500310046001d440281c0c0075080300600b0b40c030204124040000c1507111f100c8501c0d0002c5100c6038806a902e41d542686c0f600c19038280c21140b41c00100d1000301100400b01c580030320480031050021085a0702c10190401e5a00c000003442d15075804100c1c054050200580e500400c2c6045004103040c60880c820194200364031a0158545400da204400303 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 436905503 1250 436904253 436904261
    0x10e0111031b2110060e011d01110106060e031501030309290a0f091502150903070b090a060e0105100302060c0c1002070806010b03130b1909031e0c0b19 67
    0x70f0840c980700c548104068402a9030454100d90b1034000007070607100821214040e200503030001038140c0d6042003407400e886204a03111604051641806a042e05100c40c1050a000e02009420179903a04506080d40000300b514050100704082c1207601150010300100e91300150b07034410f48a03800d081e85108194014801d02c3c2d5018500c0d515040180462610000c2d03901019001040c0c2055a0711082d85031034000c54203104030030b84440700159005c503110b14068585402810f5100300c000e0166401c01c10b0316110300c040e614084504103569001045881d040000f1485002c0b140070814001300000e10706808514510034940c0800386c49810003003516107a0700c03002c019203103100303401034409501d5a0300403002035503494060280c00485e0040701c0010810303920901c1940d200d900c0540301541d648400d5180c03400f00c0c02d405005000480c66003a07075003900c104140916100316100703030346100c031900c0741988008151030104041c104002100c202c54002c5540619169008002c0041544568000781c00d404010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 436906753 1250 436905503 436905517
    0x80a090f0f0f021f180b0306150405120703031202030403020618210d110c030d02070503070b010b0409180b0610020c19030b07210c12090f0302010e0111031b 69
    0x1210b10340c01002c4541000046400d5403400035180c4003c0c11032044070049030050540a4401c084501f440003c1c6180382c40c00c0000001540368203485d2a107074440300840c1c071810413040208290303405441308004055001010307071000c45000f0310460450071f06540003074661002421014810700010040700251100344480700341d110005000e0300ca001c1540d15501165000310304815009842c0695500d096680f100c11103200d008084051482e02a01c0a2506d0094001e0745055410744070038404800002c1e52250701c14042d004003c000c0b9103d41ca0010114265040c41c03c081c4403150414562000043c0010101d5400c40c804407203001400043c0b0000f2464280030300c140652003202c0004000b42c501c00031a445d01a40d025500101d9565140c44041d50030b40e0040c140c4603601241020f031540c2c41e00007540300a038804170614240e103ca8284021000c00c0d1804810280d4044016003181c03410140c0902c10030352034400a000a1040c942283c04040c8903010003402c1071011983d602d001c00c0d408103a9012501c2c2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 436908003 1250 436906753 436906759
    0xe060405090709060e0d020a12080415020705130c121d0a080304150504020616110604090b04050a1109040203090a02030a1a010b09103c080a090f0f0f02 67
    0x7903441e003080000c0c071048182c4104000324488000e076100c41d06208641112030b0750054401e094251130442191490400c0c1c0f05c040d00c42010501010a501d4148015940100265070060102d541850204120703e06041815a80f0f903151a0100d009250860002d000407104030000041e450441544010740328100958441507001e51110b40c01003101c07150103503000d18080c3c100070b01d1820720402e4810403260b0981d006980701e40140306204000071308542a0740c0c0d0030700c10101c8035080100d10b00030607425041504542d05107030b144c24241070707181001c1c403035698080d007071000071322009240c4840c401c174504c600c049480c0219000800500416402c00c20f01040d0741c1e0181c110380520b002800c0581c451000e603800ca83d40d03108600000134040700d001e02a01c507440d000a10283e0004848603080d511042d4800d4103910f211040208101c10342143d0740a005280518407210000e450b10f544010500a002085413282901c0c20002c2004140d40d40d01c01d004d196480b2688a65202142c03c0c9902480e8a20f580258 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 436909253 1250 436908003 436908019
    0x1081b0f040f0606090e0f0c0f0c030c1501330309020301020f0d0e1b0609010c050c0316080d0903050a031b080f13080d08160c0602130f0803190e060405 67
    0x130103a60050b820350403158292028009030b11200050380280005589445481c5000d02c84058144510b100600c0e0100c402d02c00c580c9003103200c404040c01c04111044282c1c600f424840100f100d1481d0300b0604070b00742407105942c81ca46000044860328146002c1d5048105580c82c020702d021524250304880c0014481c004080d16079200c000100003038100c071b10140d4002d018214000000e46140d1400060000c4002c00b1181070004c0c61004583c0740711903201c240c50a04c6a00403505060300e0900c1502c1c402605426400001030a0000003490308013888692030030014411001c001041000c01c222130321580c0741c139043c5c0016001d840c09412904000c200074020142c00a41e0000500310f43c0000d061544100080302000c568a4100503150340504884030041010b81d000900c8100d0190510604031045c0e0910000151054079480e0403038200c00b80c0d034026039071044000d01c9210b680607255001806500019854000c40d400c50690b0308040304440b070148400c000c20341400341d0302c0b0380075a40a85400350001e2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 436910503 1250 436909253 436909259
    0xf010501080a06060b03190506040207140c210c0d080c03030c090406050a030807140f01020d0b09250e040603120315050a0f14060d020a090e01081b0f040f06 69
    0x1e502d40305020402c4800742e00d0304c0c400144200d070282c01d49200700d0803400340115002802e03d600024141c0240320550040e820424080050004101a500e000c00400100080b411540c00e000038000304e000c20104003014921f4003010a86c0014100c0010a01500c003000288644e25101100f0301a05449c18814000801006100010b0a000d030004240444003800030959440c18400e4403880c0f808050640c5a041140760302160054801d01849040c4c04203c075107a0266180140c03c98000321108408035840351000c0d4403d00c3c0002d82c0c56007004642d1444140719043c68072101c00416298030440a02006400b101020b80c1e0304d1788000025030308801c000f1000d00518000400418110500c0206c1842c1d9101c04903107420b20b03146010a403004003030024800340c200400c41ca140928000000e601110411440d0030340280c0e80060000000103441e01c59041741040c60003407040c0c3c4142c02042c2c40b42d00048000c2d0903046144034500e55000c007610120342c102c1c1d681c80860082d10201e03401d011010f040800c00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 436911753 1250 436910503 436910519
    0x2060a05310b0f040305070305151e01030204020a090503190b16080439030506070c0c06050c01181109070c050304060f1704050c1005041208030621010606081503060403110f010501 79
    0xb08401c84400c2d081c08007240c1c2d07841c40b081815980c804110702f20001b2440103100500b070507801031001c1c02c0581003d104140e5103000203450f208680820701c171111095030758182081aa0403865410030341c00c18102445810418002b801c0a10081c0302070401499500e14440345841c07140020482e14103001c3c0804803a1104c42d4000103101c191000322400d12450001036005441440c2c4c020006500c107002801d614900b030401c8401d038104100c003986c19561a81c44015505c020845103402c184a018401c195203d11410081e1041c0000c10700c03002e201c41c241240000a00100c12503042d40c01d1414200440246410221955601001490030101c0b122003444280640064800c600704402c03546110341521041c01150140110f214079100d0000b420507070000141018081e42e8089006081d006040790144920306025580108100341659150300600003540d0144415a1002812040d14218810030010035500d800042019040210981021100140620021944903240c0009200d40c1d6114403074 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 436913003 1250 436911753 436911763
    0x3040803160c0b0703050a060e090d02010c0f05070b100308030703150617010314030f041401020709020f071502090307091d0a051b010c02060a05310b0f040305070305 73
    0xa06806402024501445108030b4040725010707403141c2c00740a59190418103074041c000c09489075187c40d4440c0008940300d044944558480c47c00c01c0005c1046014401c00682140c0a01640d0010480801c8100700541c1e00041200c504907032081c100040c542d034144d01c014850402d5000140f40082c00420b120300345605400c101e50b1341c55002032048141d07995050544000418a61a01038494244010800f14030300c0c0341000d0400c4c1f80001540e140003621100d03d2210351042d0440c640c8010440010141940c4c100040c10103015010300c02c62605021450300b81d4079004a21004003203050004010102d443c568060741c49189010382154000d5803542c1c0401d028240101d1843e03d007a4404091001070200024118587c0307406c503025120030120004c03034946052411005a05011f44820810010303141e500040c40781b40c207a40c0d40c03a038589001c0554013101c682d07250f4810411144030010150030307078a108100030468030482d03440c3d61340341a940d40c010614081c0b540064480e0160745000400c3c8200416 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 436914253 1250 436913003 436913011
    0x12030109150e091207061401060503090d05090607020603061801080307060f051e091c05030105010810060e06090a090509030301150201020a0f1b0b07020f1203060f01030b0d0803040803 81
    0x4215030090380c90300580c0c816090111032a44944d8007016404024150100c0217100081c012100801d100c20400303c0082c0d00c0e8400e91040300007940010401c03510704418855401400100e140462400111070b001030050300a000029216000000209005940e0000401c2c0e0300c0180d032a000d00306694583c081030322500200c0e42902c50506002c05203680d0300701481164411440c1011280d0040310345801201c9005006050030524031410b2192141b9480010080c004006150342e007581c1c030341c141000105110030282c0610015085a1010708c00507801050104265000780d804580b20150100040c0c0c207003490340e020180071444cac80180301c5695004401181a505101200001101ca1503403c074200d22469151800040f500c450075462540f1801070ac401044108004440ca49202e4440000310306064441a015038400421580d10341d6003841200c007084031703001e440c80c00c6162040103e241c030a500508681007541e901d02e80d41c1c05070f813140d10200d0446e070481c081d5622481c1c036240c10301141d4010742d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 436915503 1250 436914253 436914281
    0x306070f21061701200a12090c0923040b0c040513050411011106010501050d020d0c0c0201080610080a0507031401060203071a240307080a030905130623010212030109 73
    0x192030403103c1014003540310803010b501c505030210150704031094601d4210b07842150400c44801d4240c2e0507003515019070001076019054064000e0700d4140540100c48907060000400454a02e045403582003040035198001c0d00006982440e54031040007000070304c20b5030040c503449010039003080c03c420490b901c03681c4918881d45024003c4400078006440e121502e0010182581c80800140a036503c501e0140c296811880405420540c0000c8441c0541e04045540300000303e800300307940195039002c245150820006e0343c002ca02c903204490010022140100400d84681c1c403103001c110b81c0c0d44680c0c824240340343e0041d200f0b409541c440c01d000703489500002c0250303030031014032002c411000c4410035114010440080c51948600c602001040c03510500050f056042c0550080058000b000340b25400700320780300f9626190118202420008015021820034030420b1800409114020307901410320302c1d1428060585001401e0400100c0ca070900700c00c20f801c10200d0100c000180802d46411002c400c0441c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 436916753 1250 436915503 436915529
    0xe0f0c031603380307050d0f020d02130b0301060e37051f05060a0c0f03030b0a0609080f03030403020622050709020a031805030d0207110d2a050306070f2106 69
    0xb880825030780f8005405082d40c40700746800602d0000f231700c840d4070350301c0e451001c0c19111902055070000b80d01c00344500607128040c1d85568032904180340c03e100f00c00180605a400d6900303400c00c080c20400007260f0724545c0d9140c9440041d41681801c2c0203d80c1221889091000d012510701a040d0218861012042c45454488641c01240a10300311098420155140e80c2e4510700c1f0070725485811094107910410ba080c0f517a00e801c010f071103488051040010b0305007501c40c040b1841c503042c0b00c2d80c6045101d1020054a4005006101c0081d40c0803840940101c9000c441c403522801c600c4041d042070101c4d200040c800d104e1200c002401c84d045401501e000c03501620100546c0d12205507946065200080060080c3c1082000305103a004503070140c04081c2c040c4055000c1050030101044501c0ca4406064a0180450805101e02e0954000341403141d280c0c5006041103d1034040030071f95414001c3d05410500c003107070b5020704e16144110b9203e02d041c0140d40c00c0ea5111600d803046580100000d01070700d104290300d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 436918003 1250 436916753 436916861
    0x40b032a0403020603070e190b03221a060117070c170a14030a0b18100f031703151c170a080a09020301240e0f0c031603 53
    0x420261070840b50041c244602d03590b1060b500701c0b40060049921988649000780091004a01e2000403020303140c0291559540c9c01c240e6506641410301d2089070595100c003d003034000080c10003000c20b07940000c01030012025201c410061b1041c0480910003440500c3d50410010703415070010b0400001402801e900d440303d2842c211805191280108072408584543d4031042e200c041c55000715800f50110900090f03182070800010f401c100b5640c0c1c2c000e00e0089039000d008030224044190070042416018440b0114615603604a01e007011721040703402c5a002200043c11441c840c00000038601008040191b82c850145940f024079110200680741d4190588003005001c0c1c83c071080701c0880d0380d41d0b124a1801e46c4c0e4904030381c025001c0588120380654035410308a046e040d000d005800000c0030100411081c41c100070442c10354070750041042d0006d0700740b4030500c00c039404401d04032500a4036804100155178818007064014140c8181d000082d000c80e0001c4199100100c8034800d08062501d0303400c0c0a220f4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 436919253 1250 436918003 436918081
    0x4060801060f0c020f130e01050f010f1d0c1e070605060405070903020d0516080f0c01031503111504060c11100e130e0303010b2101030b130602040b03 66
    0x802071003501c011a401c81044000f5140204400e0407112008048000c81c483d0441000142c0f014048010300b6030327441e4810301220401102e1010301510103801a12811407602a280d50040b401e81c04850681040b50041403000046000720f5101d8410505025410200842e2202c41d035031080c3c0065504a00c5c00000c1540c0e0311305070007018000e080e103554a0000728203580030880c2c0c0c5600e040707088070301d84201404d0141c541d486021820041c140c410140c046020158640e50a02c10313190740081c101443d20000c01c0c5104c0306d0910580640303401002e001c0b80c00040030b000c83c00c0317040c0c0c101103c0c400e89001700d000201c0381d51010320207124074411036216441e505220305100201103480c44000c0401e15800c090740890070002132282d003d0f214581c010403250b0201000906552082c0c02040100200080700c03142c075032038280c50a86a8500401c011090740c550b4481003c0d4500241002c00d4105041401c2c90600c5501d405035000740510705020f43c2e9078100b50513068042d01a03014161200002c1244c0340352814 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 436920503 1250 436919253 436919267
    0x4030810030f0b16140d0e010f05090616110312091014061207031a040309031e0b150d080901020a05060a0914060903030a270b01030303050a0b0609060f040e09030406080106 76
    0x300d1702d082550034141111054070240607503400950b544d44d070310201c003412402c0302c2c0141d07070162501e0006010182005280c03803c02c010000341940501403030010031203614800101300c5800201e180e0f40300320603440b103e00c1e02c1e04201e82e2811149a43e4100b50402d252030f61480e0720701e405058115050008956406e04094440d110391202620000c517038215a4008803441b030940364800d00c607280c817014a6803290350300901d805044442061070350b4108003001c02c1050305106582c00014140c81685100306900008217034140004000f80308500c00f240d000f2a590081141d2424076920005403815803805505500c001c1c4001141a1113125000c8a0402584008100c20340241f090801862440e9101400d0802600806040c002d141040c04000304120001942800e00720b48660b00310215135141d801d008007a544050070000728186001841041c540e54002140c80300b0106440441d00c0e500c500d000e880e1140101d81c130503c03800708400c04003c48483c002c801002030b100f40382c40b0707141d10303076256041100c40c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 436921753 1250 436920503 436920527
    0x10f0e0607060911090a05092404030e0301060f0e061908031b0c130f05070801120605180a0f0c08030a090b07050f010e0a060b030f0604030810030f0b16 67
    0x40810440e40001c5281e903003246030740c20b000b084d1421444001c00040351440360112a280c540381d90390818070050040a008070602a418455000251288007100c2400c101002c0d00040078400700032805181904d007908030100030150301050020503541c0d85400854034001301c83d414851034080d4000c1c40d1a59642c146501a80ca0700c00040d0b0a00300d070380360302c5040440804c1c038460700f134426204204183c2e5a110490f950201140c2c0e0081008060f03240c220703058a0026080348140042200144100043c14054100940d004bd2000c101500c5110107002411902d0700c1c540c0c800c0c050880c42806020f0315400c00101d41d44030744091a02c441d035810341607417a402158132041c00190050300411850035420081e1600364010021382e94081d40c0700804608682101005503140e400a561460600c0468442c07a12a00b9003500a82541420300750500d44030140108010107010598004c03c0d07000041e0000c8402965011a07038040c210b4690030041500c0504503400104d00d080c000088100301d101d04d141d5820 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 436923003 1250 436921753 436921759
    0x901050d12050304080408070b22030b060105070303020c0613020114130603090203010b0a0f150309050d0c030c0c0308030a0f0b01020d030e0313030b090c03120909101d0105010f0e 79
    0x1c1641804021a029400604241d41c0d01406020104103030b42d05000410090900c0302001d80d9a210103c9060400c42895120450740643d01c2800c0000c00c507541c109a42c80305007441e10590b900c1c0c45181c01d60090085241400c0b09208900030410703401c0200c919401014000d03202e11840314425030f0b840009104000300b4001034004010204a20780c000d07001800c0c8144000e00110310402d00c180820501000ba0740000c41e04c402224042159442e2184031040e051040d181c280203190315601c403a40e0320803074044800c040282c44102c00050600c20116107007481d03400180f03401600d80e81d052160464200351003104042c2d2805020000c4a2030314458216102c2c03068020b000e00d4203a01c0800c6d4020880e4540030301c10740c00300708011810002441c106c0f0703000c1e5204820508180c10b03c00d0500b4035203c01000024041d503c0841c1420307000c00011305440000750201e9030030b252541d0f4240b50000c0e012080d80010111401c0b030300c42e141c0711610404954161907082e42c2d80c07880380c7d0103424110f1300b0700204490903030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 436924253 1250 436923003 436923023
    0x6060a0c0f030c140706090602010c09180e0712030f030504030206041b12080d0509030405061903060b0c010905150610081f06020708061506040b0702032a0901050d 72
    0xc0041c4600344448001c42c02030410400740c8040d0703101e070040050b0071418010b0542240405012164200900e040503203e54030080040100424020300008098004c14400100e656500030922081e0307044483e108a4507030594401a6a49116040c50a010281103002c609c425080360700c2d00e44032348111031266805500505040e1202d45031180e000310004d040c0040900441004585030000f004205241c520aa0740d4958495105001600729640170700101d1042c1c0042100f0400b6039190803d0701c01401c0c2c22034041c0400140600150001c0000c1d5120317203240600032858401d01d8106510001c1018043d105407520021380c07141c01d070703040e0744100c802035070201d080b2040044941c4590303103050344030301810031181501080501c520038504081d030080c0016848200e0074440100b042c0800c43d00700541c1c00426a221000ba400a8443c2c000d9005808400001242d030b8000d40d5020017400d00707044c0c4421200c02504c50103581d1850a0031f02a010b02e4040e00f4820300000307060402c034400d4120b403500712071504 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 436925503 1250 436924253 436924277
    0x30605010506120c0310030b0c0403050708010b010504051c060f0b04051303080a0209030703020603040b070f0504050f0d0510050a020c010b010203211314030a030605120c010f0903050105090601050906060a 90
    0x24006805c040c3c01100d41c11040361b004800620110140c40c0502c04510000b9219859032900d5480d21005130481060b60741001442d03030301039030460700307890139118110740101c10003000c181e01075201880e031040a1b2001342080e0103400d2011980d80300d24070700c8600340e40500560b5201c4002075503820320100c0080000b4469400501e10314004e50140820705001002e40349620b80e02d40008496400c02d6606841121411041c8100183c0040b00c0d07000490307203818410704042c6800c0001d40c0001410951600a00b404101241041410b00840c44000c1c1001c07401c00490900b040241e000f50001d40308407403a903190400b44150342d8000425201280c2554440220041d0042a0981c06000181c42051800305001d4260009000540d01d100c2600303400c4021130f1034144181d0f00070180c0c0c4083e8801400b0351000810031203c80008910f5103c00300c000c0c2415000c2d42c040b6070007299151030301d0b88094603552a1074140901c411010880c5070484004030780745a100d868034002c11009101c0c80b600000400d00364180d1b2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 436926753 1250 436925503 436925521
    0x6070906141c021b0a0809060706020f030406060501020c011706040b01020a050607020109061b0507031d030f0106050907140d091a010608040209090d0f0509031006030c03060501050612 81
    0x80c0410070716070030200d040802c11070081003280c0e041c046007111140c000c5240b0803a003101d09200d000e400458001045030f5625a01d507103030343c0d01c1090302ca24000c0754002150300502c81580c044440c3c00183c07440041d42c0c0d1405090280c0141400e00a45005029501e0804e000d0343c0704a6400181c0011620301081e95220b9400f0040103000d0220242c1c103502074886103001045041c0f200c54801c064640000c50918400c0c0b6080c8100c0740082441c0d500d0400d0601c224204a03481800e40b80d0990781402c059054070b00d43c0d001c1003254074040c2c04095152052292208024006400c4902194000c1d00e89a8081d281c50009540c41001d0141d800308080007481110302c0000d0542002d20014002d48100c00554244038091319143e00982015000c40c41150500007141846001c05038400b070310300094407483c510408000d00e0034081c01d00c00000c2020100d9001c041d91b601703100d40300031049824001c1041e00c0e40c82c50030a040460074801a20711910f41400024242800c00848001d050380c4070102d120b41c2e5801e502 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 436928003 1250 436926753 436926767
    0x31814040c08151e040c0c120305070f080718150e030d02250b1204050c031209100908030a080609100302030703030c03030f0e0f1006050315133206070906 68
    0x41c1c540324145130012482c3d11540f1400c03144100355130350001d06180508214281c00401c06000041501e440104180141d112901c42c03590041440c05161540300c0c8142100c80c10041100740c500d00510010001c3c072920000d07a40022246c01c1d44544000c400c00c2000c050301c808003a4011400768100f21000030030440003201c1c091000c1e452181c82c040f4540c644119031996041003890000c0400440107101c14002d01300000744001c0c2044001700f01e0f5042d004203003525402449841c2e03001c1c1c8070024200c0660343c01128410081c1050108998030b032031200c0002451f901050701c110f80100d00d07500204401600c1d0000304401d80f07030098002c01d030041c55a03400320b034000301a12040d401c2655412008203200c0d40750158503480c80144004101440c0448042401c0502c0e181c074850005140040030806501d011070101c1e520a13061889004039503402800600d105881100100b190300d4502919142e07001c489035071414a0000811070410640703000c401c503901c81007510301002282c03480d0410494031788140f407 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 436929253 1250 436928003 436928029
    0x4141006080916120b0c0a0903170d1401030c150503011a070609060905010606030614040f0b030a06150e09190212030708070209090a0206070f031814040c0815 70
    0x21520f2900e01c1c0c2107940341984030303038000c0c0512092454942090081e08200c0c0f58100002d80120f5181030540900908441d903144001000310001c1030307000c8400f860003000c4d01d00d02801c0310800d0110404840c0c480741d002c81d090104803020300b010000421501e00c0c3c040c3c4014403408640b100c5181d6404c0203515101c40c50343c03403d1250b40d00020040000020554002e02d0701341440349002182904107450250b0960f03c454202408061400d0030400c4480100c481d03000559609070340c0004c24034604400c5901401040d8003441d014441c2000301c004000040d40841881d5580d900c220f90526114082138100740c900380c981603441d6126001806045642e07200d80700381c651004114444541d8609046421a04010310640301244040b4810096081030540d00e6803211251029101e01211035000076a940201300d07000d0840e011a0f5411000c05020344120366500c0c90225562203542c1e6038081056215500507a1940120b0a0800078007185025070700c000e014182c0614600078180c450750500200c1d4040b82 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 436930503 1250 436929253 436929271
    0x9030a0810050a1502010501090203091504050123070f020a080d05090f060126030c0d270b0a030b0f1c03020a081b150c27090a0b0414100608 62
    0x314001030b0036920745001100a05003862080384400108001908551050303100d18a003c1c010030402040f00310100742c2c00c0c010f04520030000703115129801c0590050294a0b240403040f40c6038004400c0c0089084070151254500d80d66a000ca80c2e00b00c242241c43d80c00305680140002400d0050090800c40b50700140c1e8820b0840c011500450000600c0c0c6282c61000c2e4051002c00c040c4078441e03070f0134204032503142c0f030f03000d02c1d590046141110101c00d0b06c0e45c401c5d07920b034220104504508500c0344080c0101d41c1032000311010060038070041c0c03109443c480c5a4030066000003c0381c50100850907500300a100e0b002c02d5034005240b4200c0c0f514130704007140e0b010403a1400318114050000000001440d081c003a2000325120035074010541c0910713204134544040e0096141c40002c200c010045400c0701031045a90300c0700b90561100040d60a12542d140b1040801e400710381c82001da004106902160b0390210b11200022a8140088240130380c0b0b00c00c8812059502c81d01c4400c2c90a81800821702800c2070b40c2e0032000701 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 436931753 1250 436930503 436930531
    0xe040602070f021f020c09040c09021315020601050907030506090604181a01030b010608090d12090209091b040207031209030219050a0c0e0112140f070f0503070602030309030a08 78
    0xa0340c000740c1092440d004d803118a0060140a00380c59a0402c01c1c228041015180d003c0242490744441a00003900d2007404d01060700003448551002e070546904004044002e0240344640700e4100107910344800340500741c05000010300090b01c0600c07a015031400f0310409402194951158130a11001c1c140460024160300001005100003038191190010503906420f1803c2c0c2550461401298136031040c1e00142c100700452003407101c00d0f07001048504c002540c5007849000d11043e8041d900280070301c288080d41c1b1008000402410038808a1815407216183c001c5030001d001d0309003003200b01e01030070380064005440e0481c180000c50144e80310803c1c0074000e0049510600d81e407882122400702180007111b064003e51049401c004100d500040a40605042c011043d0f061040881070500c401030050141c5981c44001091903100b4842500040202c0d81070f100940d49500701003921840c40c3c0b003400e00a00c503071000003a400b03201000303803800740c50314102441c50842002c10480742c084001d021264403e50b1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 436933003 1250 436931753 436931783
    0x3062f09040e160305030712051908090c04020f0307030b01020d090306230705071101031802060d06080601080a15091a09031c0b0102010f0b09180712111002070e04060207 75
    0x3c0b001440046105100a554665851400d5800c07180e6042c1d182080c801e090240d600111001f206400c030f500d00e64980641a56240c015031441d045c0b50719000c41d003152000804039081c0a442c0c0046102d02815101808500d0901c0700480c6d462107070155035000074803865000d000151280d00003031a9170000c0c1650741e038040107840042c080641c00361140404550300140c00800c01030702220a085044090138102300d545182c203410450810002d070028401c001c000b40005904c04140d12000103840380d0802c03980d50350b0711a01415902c03140c0c1d11094502034417503d02c08000d0b00e07039405880c450503440241e00706c40d0040440d5110382e4000103003090b0500d000c1809402c10171101c0c0368004000180100d40400c804a64400181c21100e81816100300d05052000d48512500d5103038542c0c1d0064841401d5840d12815070010b6400c000060b04141c095005401103501400002090080302a008036901c0c141c04100304070a0303aa40c0c0103841040034207548000040e002c10381560250010700d0044c5050000c0182c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 436934253 1250 436933003 436933033
    0x8030a0e12040f0e0106091a0a0302070b070f0e190b03040309031b0e15010e090a231e16140d14010f0b09150a020a0c03062f09040e 58
    0x2042e0000c111128240e4000c2100d1346040000e07500409043c146400c03614200103040321403a800c0e0321302400da08400200d036802607200798104c5000c2e81e0000342903a50340c11702c540003c0900e448140306200041450301e414400703207050000c038180740035480c841082d0ba41c540000d49400d500000c0c415000d00520780c50000119101000300356806c04400d21611426080900003440030101521130700000c0190f00c5644002d03600810035040130740d070440e546034255a031024404090a5400066000003070051040340c40c0d0054200d0fa90b0083d5500003548064000c50360400d05103800840351310541c1440e24690b0020700380580d81440c912908205414904424401c0c035030180c07004000500700800040004201000450841e60302400706031180ca480d0564590001e0115038030024000380c030081c00580e01d403900e8001c0121988040d441000300014a6a0f82000e00c0200f0302070403255540da02c5d2042544a90841904030381004043c064014149134110091000400481407010550f226122890882d00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 436935503 1250 436934253 436934257
    0x803030103050c040612080313150606020a060e01090b0f07090b0f0705010b03012315041b03150605030106030903020c0301060902071e0209061e0603040303090501140408030a0e12 79
    0x41c0140000c144400f071400034001100e100741c0c8944051154041c1c9440040c03501c2c400c0326000068a5580e03201f0044500f001038011040040d485499481d045d00010115004200c0c40740d51405a1010003080e06104461802c1c0c03021040300030516550034000a035005c3c9040748282e00003006107400c0900301d840742000849640301030360b01019640d01080f1801004000d00a60403480c505500074009090721401d0a402d07030484500e0f500c00c142501c0c2c0003c8510328070301d124007101d500c000c1042c02001e1201000003615100701c103044001a0a01421280c5140344402c49001c03130b511940c0340e80c0356a29008085004180844003203046010704202c100542d80d09008030300c060700400c1c0d80107955030010b28192040c0c1d0300c0107410100304d00c0c0010410340503a4841e0743d0b099108400703940c08910822544801c1081c80b0402c4205a40a00003100740818103a05510003402e4a11603c02084138411416141c01002e804980040080408000040107079805800074001c400001041b03c414180c0c088150440da = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 436936753 1250 436935503 436935509
    0x402060c0f0102070c0311010311090d03020c03060a0501051807020a032706050a120b0904060209060d0f0209100309151a060d020309060c03040302070902030709120c0e0c0a020a021908030301 84
    0x100c0e08105c2403090000510140d10710007401d0804000105190712410114080c00c40c1c0d5501c11402c0200c003106160090201c03003440000201601c4c070f1494810090f10051800780101405034425144082001c0511407005020b010303250020310074a42c1641c0d0444a091500c0305006400c0010840301d0380d04819811210050715054031180c0d00e034070089a0080c8140050020700704c0560a11003920a103481d4010000d800582181c2c0c0540c2e1103101c80301040b81403050308002d00002d40360200d5a6107030f100f26409401600d40484102c603240d9011b12007103041e40c2c40000040c111485400600d00c0460310741c0d04c24a501c14003a81c0d80e10000c1c00c903a00003803d9400c00301c40c1031a0135400104210b03d8400503c0380706c0d0300200c40c1d03100300d0850900b80c8000350354a600b030090300401540003001c030300c1003405000703d18020b0134040d1003900290700302c1c540321180d02ea0314441c2002070151074012901d00500081501c1108105078010443c0540e25020400c000790a0341041c500d0a94404011560000c10300055000e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 436938003 1250 436936753 436936763
    0x2601090504060b120a030e030106031115040806010f030c09050603030324060a0206061c08070f03030b0607260913020d0e0105070206010305060609040c2303010c170c120402060c0f010207 82
    0x2c1007424098102c00303200e00b0701c61192b407602c442440001d01041d1003911840082e99500c10302c402c1118528014461608050381c0ba00c030300b40c000101c1c003a080d81c2901c2a01e12503011105200e544005080a9803400c0d6001c69040d0820b0000525140c4190004900d0030290300808502c1ca1000001c40c4480d48501480303001600302ca001c1102504090315060365130b0041100f0302141c0b42490300c1d08100c9001d07201009001c012030048142c281840b9401c05415000c008240c5580c4584c14600b18100418001792141c0290b0400705144050001d0015201c032600090100700000c01120103c0d0020741c4a40d019540b1580d0740c3c6403214481c0800d114103480340005400034280b0b54114141103180c48801005148101a00340401000404d0100080c007180c5c250407074032481d0420303102940c111080c0d0804041d05580b174002100c0300c4035800524141202048008036009488001c2d51040c02e2141d58038003a518042e51000c0b9006060250041c400b03802120300341c0c0c094130100000e087c26030b0f2256200b622 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 436939253 1250 436938003 436938013
    0x50405091f090f06140d1202071d09160602060c0a120606031d03041406030405012a1205090a030804020639010b0f1c0203010e0d2601090504060b12 65
    0x4440301c504c9000701401404080781c0140042400203881c0c1001c00b20003c0541c42c0320780b1103c01c070030300811001015040c12110006041e007c3c15564019460880d5588030f50b100390881e1800f00c103129039100007900e410b640035040d07e55824042c900c141e40840310400030801043ca03c00b803524241d206a20103810180e40121b0000007070902c0442c40800c2e01002d440580003000704200104c4987c00c3c4c80c81c2e410701a62908e841c0c1c1d4030b81c2085c5005224800301c0340c80e48503d20380d020347c1c9060b0700c0f1171041440d0001d448074422400c107844058101e410442d507200e1190701444828011030b01035144244d0051000301030034a4280c10a2a440e1601c03103c0c084400d144100001d40c072078511400c2451f0064a807800002c026004000300002d0b42d407480c5500703090045400c40b100500e0201c0300071480182a4020b0024440c0c12041e0310101e5890740ca11045800103411440350f032501c0028120a030008514000e803030b820590034007071813000034040039200b21806907403001c080d1b01e59190710513400035518000010345 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 436940503 1250 436939253 436939271
    0xb01110a1214121522150801090308190c0912050705030a0c06030c030515090a0b0d0b040c0501020c0607240905030a080109060810020c100e0a0c050d03050405091f09 73
    0x3001212556190b02d11580e01101c400c5c1e0742c02042070400402c0034019502242c6804c030500e01102c0d104681d0015951542800810f00038076800c5400f885c026180f05080c1c1c40b5511020241c0412a00c1c083c0142e030000d5402c1c4000c000241c4010b0b00016070074094802e5840441e50780000a2918440030800c1304c0101500208100260b0984030b24a0b01140318202409a4a00380c841614411b2860821500c1940303820b0205003500c1c1154082248132101500042040703070a0b080002810300700f2541100d201d4101e80300807400b54170109114411910107081c160074400595205c1c4a01c3c032420054807040c00c100480400d0500c007a00071001507500410145075101241e18009000c1c41d0305803c003002443c1060700c00c0100c06070000d2050349840603c2d80c01070b00c0c3c500b048645c0e0305044140704c155151501786541e550b000b540100301303100507910410b0f00107040e686c1c840a101c1c821400e0b02000c1c1c003140c1c091104022600b0211002e990107a8076202e00e007404201c8c03021200f980c1c205a0464060503a68900c40 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 436941753 1250 436940503 436940521
    0x1150801062301030c020a0602031e01080a050607080403111e06061005040612021b1c030507020604140f120a0201060f05060405010513150e040b01110a121412 70
    0x81400351140001405a1180c02c0405280c0305141001076410950f4400001c0b807400c0c070900c2140c40c25580300005650385d01705030b00ea0410150a685015943c2c2e10903400006802100091040b030550b40a005000035a503807500648a50000801c20340034080c4031203050244210902c9003100319400240100d282c20f100003543e5203401c20040c0817034003462841034551101908081554211080c51800ca24840c85000781c0d072003e401f54125140403d0400c00020fa004000803809002c8041c19203241852201072040440079144203542c07650260300704c000860086150314100608c034054040441e411401100c190a280007507100316074209003008510f10000a50a00642c00140100d005d50200389040c07800042c40340c0300382e2041c103052100000303004940c00c0a28030504000d08082c8107046044090810181036809c848605904c00c40c0703800c003c0d41c0150b0003582c501c2c00340c1d100030004201d001083c1d6940d0110440001d500024091528010301500000394000c2459954012602a0b03e0800d5500 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 436943003 1250 436941753 436941761
    0xe0406050a05072102030a021c0b100207060e0d11030a050105090c0a0f183305010c1e171305120a150906020906030a0207030e060414011107050301150801 68
    0x260307000c014014040700a0900603024050a00c0c0003520016a1b9403544601c403402031090b01004d190025141d06003d100210940c8485a0390b64140c4844500c0d0307110090407038075028180181d0021a42c00d060156241c2003652198a400f8460358003516030440a0340043c1c070b08018400c04456580d1a1410042400828010000161420368040100a01306a90500341c000b150080f4165034100c0030201c1c40b2944580c0000060341074142c4025400c1000290500e03021040c0c05160003044180310001600d548035807101444203401a07411400b5042031240b00c03503010141c0106072144020304984400e541d00c2c1200422090401420f190851407400c0e052001075500c80c9410042508071580785004180d401d5030444002021480000301203080d4034041c0028005d10113115080b89001c001c0088840d140d50080200c0c501030345401110000420400031a4030071800b8007a0608600003518806502039840232031410010401d071040140c0710070110b421954192041c01c00300d04e981e4401c104e104400c0c49 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 436944253 1250 436943003 436943011
    0x803090708071a091908060106030501080d090905090109150204060e1002030a2706030b01122d02090607030806100c05070b0306060c0f030901090f1206050408040e0406050a05 77
    0x10182c8000e40c5040e80e29600c02c080d4031158820803000203204030b2295201c60980180c080711089944000382c0b540800c40d030703440090040401007840c140011a99440004103103582e00640d960300b9111506140f0f038035025110242200700f09640311240d200009403005621031040c00c07041c50058560b0701c1c0142c010304560b9132803900d601034002c0184024a56502000316013001005040ca50f030700c0c0300362681240048828000c20304a0301040000804c5007541600b102081c030200740d8441d07805010003183c160480702c00a90800221004290144c080e00724418a070020100e4800010709045145e8082050f83d40021411000904140300300034841c82c0c0f40d04100804078a80c60814803400480e40ca045d614415401520340f507840c00310005850303603a000d0031185a4004030060b00e40f240b6088400642e00d0b000201c0c164049500e141020504088800c41c860842d4030304c5204150060607500c0783c100902c4081c000781c17040d001c100720100d140200c64040f01c4c003ca10801000500d860f0843e628030850304090 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 436945503 1250 436944253 436944269
    0xa170c0d0c090b1603020f030c012c07140301090f051005130f03050f1c060e01080d050301090c020111160c1a030a0b030f0d05030f1005100e031908030907 68
    0xe02c0f800c00302e041038440c08030b034400d96081d48010b141410383c500b0080c0e020004080c030000448a610380c5041d08400c1715221800008036071400d809500c0300820000d0314152101d60300c59101000180d001c05000e10800380e0213800010008070540341c0307042400005400791210344c0920010603295980744221640582d40d00f480040300380c070540d02c8407483d1008601c041c04102c00800d03003100c40040501281c56000d520041c0c414110b0000031018040d1109114042c40c094072100005407810000c00c01090b05071881d925030385168200381c2c000d001001c0341454102150742c2d8080448038580501c0003012500903000c041d4001d041c203841c0002c04031840b504600f1800e10351550103d2142c01c0601902d8001c18444030101e03192121801013468a43d01d40e040106900c504080e92a040750064002e500132030103218001041d0b40c440042c12280441407203180d401c20320358009880101e01c00c3d44046c03942100103084e43d094042480d48256101c619085c29102c1800000c14080030302420407900d00144610 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 436946753 1250 436945503 436945517
    0x9140105060a09020a090504021b1209130e0304030804180e01020a050304020f04090204051302150405010e0d08070c06031b03051611010603060e0d0908070b0a050a170c0d0c 76
    0x1440c0070606007205440f420b0119038001c248603c070070340a5503501c0041c1501401c219160400d42002100d1042c10185c0e1001c1401021111000008008200c5407920b402034808000384d0f180c80100c0b0b0040ca01d2141d068650300041c0004000101d8900c010300040c04c41610080003503500e04000790840c1c2500a08800d684e2041000c1280150044150ba0f0300070740440305006800002400b01e0050591110002c8d03009160a08000301c40f8406050710300c01074020354000c1398035648491100070711f01c01c0d0702070b60740444d22440344420b0620301a260005400c1c0310354100780c02d2030200c4e55800c81e4140e980d00f1500100b91507080c41c4030b0307203040c80c9802a170030685480c00b4440b50a101200307404602c00c40c03409c070081091119011170180340940000740295404803041041150180b08151103c40010410b000030b031600000140074000001c441041d42e00001c44a80b52240c0000d0a036401e6000e0343c1d070b1000784207181d81101d0004181002c02c6201d0b861149100e50780b400451402c0003141c01c8203070030070184012 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 436948003 1250 436946753 436946761
    0x10e0a03030c0f0519050306031908030106090605040e15010c20011e0f11071a09040b0303120c070c030210090503010c02030c06180a1514060604050915120d0309140105 74
    0x1d81c95403404c1e485c803281030040d03036900c600021070f080071012001c00c50400c842c0d600c90000c1128020046d41295403540e40d0300085901c800040300c05101302e124998851a1010100d0311102a00c0041050b0300703014100170031944042d42e600d1300c60222864508a000d52980103c002c0c3e96003003107d01e802e0400500469412000f041c3c005002d0484621070241000103801c580500380030304000f900d014240340d4496010100b820300f10031b66647e000300005401035050a040b001c41d13050000684001c00705108800b4900c1d521040380440d0303900226001c0d10380610f07190000025844030441c40300ca6034044c0d0790304410395091405150944400110710800c5500402148200540106e20355400c00c0b0403814220482821141d8503280c61000c1074050000252042075128401d000d91003185c034904029096106a40c07584200142070145105080c2c06c0b104036800140ba00e00100c040d50050b4200514094a00c0c1005280342d02c2c050185007440040396861540405000041c000000f03500c05d400028045890 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 436949253 1250 436948003 436948027
    0x1c12050f0d0b0a09021c0b060a020d1206030804080f16060f0e040e1e010b060909011206060801050a020702131145120a1112010e0a03030c0f05 63
    0x1003a458195002540c0300c903040c0d080d580d5000140b00a1900300d109544038a158030003030801b110704c1d1704015a160310304480b00a0350f06103001900c03034030500ca4001c0e05d40c80d5040d00d02981c030512403003184038000b903403054048001410140600003170181240203062000c4843c06071880c020301d8004504101d06c005030200150351b4807147c0032110380542d24100076070661040200740600300c450202416805a10720442012604044800c03025060400a00203d400d140038040c1c0d921507a03190303a0b0001000e400600030482c0220420348294450580000d580b5038603082d103030844e1000d0314445c2c13000750001400403e41c0360202c01d00035000c80240303041201c580e5481c01a0300510421006419a4401040341d801e24001001d090400c82948400409059116403040e0fa40c1048024018032925040e1030381c8049400005807202d030b0350b50142e8000f41036075440301000040705134440000869900d414814010382028082c034109144240c402107040d40028102078180c64802c0c1805041140c00d00210043d58 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 436950503 1250 436949253 436949257
    0xc010903080d1e05040f031808030405041113030308062803140312070905090106030b15090f1513051c02100917061006030204081e07051c12050f 64
    0x51441001a5603101c00c0f50580d03402148100a11070146400100030600000c1c02000030710503c41c1d502d44040e001c0d0700d40381ca602c0c00224020403090358030038002400a41056489000400340904070b85040094201c10351590b103015070800c0313000403524800d00806080c044200300c000742c1a0f00721100c0e9420b05200114548a0301d1101510044224003c00c0000c101401181c0c0a40400c81100c0c913a4641a1070160540007180714181c050076803800002200c03440b038802c860a81c000103001468492402002c0e4005421024902e0f522080c0701c030f0068403a541d201c0341e403456426146412520343d007406e048a41000c078640e0046010380801c083d141d644840598410b0b9180303a04a507602c041c0e141d028012140c8004607003044440c04000c25042140420026005d0302c10842104610841511910300720182c1c055442005076a03071003988030074107500014014280e020303072f001e08950b03209550300e001405002021010300940b00850111006005520b100301d80b40c075507a030a01c9440d00324182041c007494 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 436951753 1250 436950503 436950517
    0xf09090e10020714030d0605030c060a0e010c080c1b12030a02070306050408270a090b0a091e060315060501050f09102c0306060a06090315180b01080c01090308 70
    0x10507400070b0500d0801450641054002030301c4c4040b203840d0601c01810000070009809024424401c1da0521455403520401b1036560a01c3c550f0717102c4440c1c2588006541c64002c424049075410000c0c400004c00000c1041100a03003d84a50004060300310181845040165088035804a03042004410130710398000440c0b00c1101e5000c3d500003115525420035620f940246605202210506003502c500c03942c0c00011410482c80881c2d6500c12580c0d5025680210389208000c070703400c248408030410107024243d00c82d0418408030401c40d001d0ba00d800d01c1d00070132140207030001c07524100c07041042e06448003180300d4800036100070709001d803401104041280d240d00545c44080c1c403441000c08005940e03031007800294101d54818910074034501c89000c1b4020a00c420048030343c061301c104400201c191414000c030074121006515004400c0f411500c1c0c4810b1400401190201d0585903a003566605001600c210030300c6024071503803042941031141035030610b000032040504003d600042400850300420480c0d00b0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 436953003 1250 436951753 436951783
    0x30906030903040e010605030103060e0f1b1201050f0403120506031b242116200a030f030c18170c1f030506010503130b0717070f09090e 60
    0x301d0341c44504103491481281c002c180440c2410000180040c1c2240c00303141645c1c81614180540004032804981c2d4054400300f07001c840d4404684c02145020640d83c11000039000381c6003004001c86916118207442c015100300c240c54215804100516074046107410b4038811108081c4071608000000071b91701c3c440000d1002d030302e04554001100507555080c1ca4011444040c0b00710040120540101180d03400460b002040c420114000c0003644038010604c034840d07004000b01980403645e01c10b04461040006520b2004869038042c4d01010302c0080000c00c800501c6039644880c0c1c450080320050075205007a503100103205268010000e0700a804031600107441d1044610003091070094822864210f0002450741c0050f101c099040d0140e00c03050144140b40c4103901e0900450b1601c000446661000301d40e4000d81a0100032407500185510042c3c61304a082403601401c04010510b507031105440070b43e0110086050a80ea02c00003c0c1c1040b51034004002c035075010080e050005020541ba240442140d81d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 436954253 1250 436953003 436953007
    0x8070501120f0c0201050a060b04050d1407210203070909210e040c0c020306060f1c0302120a0302030f01060801060c082d070b010e0c2b2c010509030906 67
    0x41c0c1c9440e64490308696107504824800c41c030303003900068024082544d041d00550b06100000c2004403116048270304442c4060500d42d107003081c9072144a00d0100341181c0d21050b0103969000a0a920951003580390344040750b01140881c945c6104041c40c1030680d62000c104a4142080500859000c3d401461601210001c0c0206600d18860403140b8044900056030300034507100420301480da1149092420520a40444110741c440c8801c016250344aa166958400c003902c100e619001c0c4842d4a182a0f103200340110384950158074240c0c83d4070b4003c881a01c00080d408010020404843c141203070042c1090305019425504000d801404403182480141202100180c003503250452165280780c0803c4101944400200c0d48811240507800030700150740310201c6074000f15110019102143c01030881c900510324100704000703c0c1210348410b640e20300420035090001040900c00780921140180512108568108441d020006020f003e41a681d10344c0c0c504010400440000411221540c5084908c0c82d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 436955503 1250 436954253 436954277
    0xb19060f02070816031709090c0d06030510140a0903020c0118050324071d01030c020c090a050a060b0702100806060c0304060302131d01060e180103080703081008070501 74
    0x203481c1050a81c051800d9100d0200c00c4ca401255419400c010380c0e2064025007071a400304041e519403070140350345244c0d2100e0100041030900c005800108645040c0300804a205640d039101e00e030420f8002280c808540e0345904103075043d2294070709003d0303201040b48402c018000f12503d0095581e8040500c0505110003800e4060350b140845d0042c10050ad001011102a1800800118030106080c0c03801c80c142c60300d9001003014039008041d0001030b1181c82d240c83c0700719204580110084c000101018003580645071511500340c40f0f4150542c031419071800046014140640c020080f0340059001805030302040c407035480107a59010312404107100a00d081010b0351964000110f1510499a141010703110005001906a41540150001e8100c103803034060300da60382d04e4017081d40d0007502040341500c81c4488010f00080f40199240014034402504018004101401d456000d0800780c006940c011804501502010760090f09203a11510460440003254581101c03a50740d045140035450501a2000d119 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 436956753 1250 436955503 436955507
    0x2100e0d0207270f09021f05090618120721020105031f27050f010305100f060503010606271503050a0b2e030510140f0303030106120b19060f 62
    0x1c620140080f10081281c1c901c0b01000200070030803080100d01800c03403543e86940c00038a000c40f40f5071160f1a52100c5280c60b201c4404c01440398003081301c0c1c00c8410301444541c410754485451440045044000030103480e030904c1d01810a0101005100c405280101d980c400143d80c00003e036500000f04190710071408910f8a803e20050369150081c11070144001c1c6200007000480e40803800c5151004810441501c03079855007804c56500b40806400c80d03000d840114600342a40c2e01c18400c3d210b0030580010526203c0c0d00003030030b48006600100006441c0f0000d215181210785111000503820814401d0f8a4075100c40e40c101c1400745881c220078160780d0300c0003c5078030390b543d044680c2c80d050003003160b103288400c0e0f00c10303031452002011400d200800307569905000c3c9000384129401242c07890804500103180c0341505828180612070190090568480d00c0d6241e02c08001540c080d201c3e949400c0d4010b6085a40c800465622941c0284290002b49003520808030001945050b0f580c00d24003140b40e14400c04007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 436958003 1250 436956753 436956809
    0x20307031812081b03030f0c160b07050a09050d170c0709060b0c0c0d080301050f0a090f0e2811120a12020f01020304050601120302100203010602100e0d0207 69
    0x1030301607400500c040d010003c00100400c3c860000c0310380901d6203008000c00301d40e03d0004444950740c070030342d6a000c00c100d00711500c09012513036401400030905104540d200f21a0600c00c0d20340e940440c0022403c1d0003580d81004a0001601082d25250f40c5074006803103400d455188a5002d80d8048000150004003c40611201002d0854120140516503030f802c084c103680c0d444402d05181c40d00a4401ca11030b145404103a6101d015088451a41980d003040200180c0341940c0e5600c91740000920400030b40d04151f03014540d8025090714000642c0d44103815600d081107000408641c501c2d100c1100a41c1c4018044000c504150b007102c003d0412014180c0402d8210140c0301c0600c0c05881030440710b4013040b681c00c01007014084c00e5800c3c1e46030b0351515101c0e6401e03400140d900070031642184005000d0300d44280c080020643c02441224000145031014108983c1f0030b800000060300524210381c028405030041c9c41e144407020000b4020400e0805000b529414503002c0c00320764102d04914034030103d00081d1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 436959253 1250 436958003 436958009
    0x539011d300703031403060120011805070302010807111002030a0921020c06090604030f170304110907050a0e04050414031c0e0706050a11192a060203070318 69
    0x201d007880d918a54441c40c0c0d0303602a803204800168a8402205900b28000207503802280c041c3c481c01c001000014086051540c034144c2854950350722003250740d400d4030030500312111038090000350440a00b5400010003c2400810320350030b01c50402c001c410301c1d510002d00c1145400741d02c1001600d030784075202c4403c040c01d110200904001107001400d50001d1302c1c480c90803100e140c0d6808a070f81c5001c1301c00501c0300a0003070f1411650700180a10041000c10032040844600d584030710010074412885145a031102c1d0002c1d40e0a540e0004c0da001d0405260404031200c039001006414254100001804000d081e0301702d146540d4021030b1030718081400c0180400c1801c030200140c0713090301c1c0c0b00c00d400980c800e45080701c2100d481c4020304000360840a02d6000c07850400340c0341c440c0c3d1a641340281d0914159441060801d00b50200d108400501303501c01400720040b0901c600c10720028140d2000d100a0240c0903030540c064400202207880100300a0744c0000403518080c1d0b050801080b4895640021000300203254 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 436960503 1250 436959253 436959319
    0x608010509070f020c2e090602030409051f080703060605030a0b13050c10121505100c032319020606030d0f050d02030106180803070506040f0539011d 66
    0x60300c006d001030680c151749101014503819a541b400b20120049401d00781d50b03c90403001d42c0041000303104405841d04a55070219081d8026205810f0400c000d002c843c11642c00821181c00c9601b060040050790f02442000b044120010007028200392151040354001070100c1407081d141381c148400708881840000e604040007080d1107107200d82008040c1c200321103884000d28241c50203602c3c1c405800921500b0050340c2c070141c40c0b0102084004d1080e2812040190180c0038000b005000946c000c0410340c00000d10700c0e004000640b20510f00905401a625030030074035080d5084a400c200c1c41e600e002038100c400003001d05d07050401d0812010242c03010f2040a201e4040c440c000000421800d406c0030545610010103240b241c0541d6580d500f20f9100c0c00748420013021600a08082000704442e900506138442c050030640741c2e02d40c440a204588a05088030f08014400d0680855088009003120001203003001e003403407220b00a640030765030b0130500d1a04005100d500392444003812180e518180d42403d040351 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 436961753 1250 436960503 436960519
    0x70201030b150309010c08011a090a150f0e1e130f020304140d1e030c051b0601140d1a0a0615121109030a0609140a060608070608010509070f020c 64
    0x10040d1032210743c8102c0e19040c0d558244040548800d110b0b032916812114810920003401c0b21410500c10305130f1048104540c0b180c000c241c0403a428403450241d4070103644584034045003070552803000d80541d6162441c01c7c400c14810314180b4800c2c00c008110400000100c4036036a485850050070401010032005555203130380b000c0100130800201804800016003034400f110303e5195021401c507801d440d010000200300181039540b58000c0c0c0a40c1112001c1800785c02d160707041003a00301606003210120300d501e0000398010750042003a416a035000d07580c072400a5403d0741c40da41198690a090621800c3d10049590380400001c500e104141e010760301030f00c3e48407018104407002e424020a0381d208020180c118a241250f48c5101e44041002c0f08c0c0180d0300540517080781d03d2651036013002400d02c60700c15106102c088045842c14807003403142403490352207104001501c0d810040700e40d14100b0140c21071000d0040f40b00050043e941c0708180f45a12a05034944066581c842c1c850480c106510b16584682013489 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 436963003 1250 436961753 436961779
    0x1180506010503010509030906270d11040c090b121b1b06060103050411010e03070810021e070201170c0d0507080f10050a060f0e1207031a0f0a02070201030b 69
    0x4500c150403140e04a00901c160740b03a00700f101e42c5911a9140c625030007101046068598060031101d54640c1050341e56501c4004408000b043e04d810400300304032912580034006030074901c2c1c21303c0b80503e003d4241c03902c600c0c090304211081035140f1030f5561601c260301c51240024110407410112201541e2051020b907220100001d980303440e5800680d003506a406410f0008046512a1007203a100d00c0d000071603c1c00a00140c4015a80c40d850440d285815006108011404d45010051002c01c1d1040c144016603408100ca000c0580f40d0743c2c440718606408040100d1000341c5ea100c08031403001d1444600403072560700c800c480408148500302c400700c0f0090400c01008807143d042408684101484880c810300c650f140814045501c0180c0607a66200070200000e100340c5200329840c150711502801c1c80e00750350411030001444540d0303203400b00403158004681841006070301d06041a2400d0504201e8800381030841c250104840001e044014a45d03011424a0a5a109070400d00000e800a400c800703200308 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 436964253 1250 436963003 436963013
    0x20a0908070b0903060606031f03050d0905010503101a04090606050706180b270a05030d061505270616020a140f1c210801090902010e040e0118 63
    0x6000e11822000340556000041d01c038401e071049590662000303004e4205592031108000c4990005450001e41544040b60b40000c08078102c415005580135000a101c00e0600c294014810031958010b00d0401009000b4080b04c41003158407801900c00d00c1c18544000780701a26110010f002d103500100c0c60a042110014000c0d8102e170080c812180107820a001004080310100310804254100403c02d000c0c03c40000c8034484c41d00607074239440a0480ca4103005400030301d86246028554001139509820014081c8035248003441000300515800b0003004084010304406000c80c01000844001e420400e05201d0b407542d034040843d90407810050207142c0303d001c020000480c903202c0082c12030041d565500007103030854100c2c00556120100500205817040c80c0000e10110075106c4440384820032080b07200600040300104220804142e403240c1c80051035495400030151a0182e001b00c1074545003c4030040980d038400c4808100e1801030307c02140310300d05610520f0041280c07071307003c4d00464811520201085 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 436965503 1250 436964253 436964267
    0x117011401080610050909071101060308040806060306041205130e09061e011415040b040b070b011d011e08030f04050f04180b0403090905070e180708220501020a 71
    0x3100703a86021240e41c5920600900306007205546000c10030a11542c140c0e8a005419175034008a00e180500349141e40c00840380c00e650144d001241c607404041028880130307008008141e4004011401840d5a050a8941c2d101e090b00074012002001400180003164881302c7d031030311004064510151201c1d25007055280e48420040c0c9200c420507104d201241741881c20b20700441d0688480344100d0308403011140410000d80c0d80d80c560212910814000081d9003281c00028200070001000f40c035998220520b8042d030300610580002044aa841140d6003444000103a9903056580500803242a20450003086400413915030107180c90b4030002405102180904000d00111441690510f1884000030100700c180d4868042c100105110f8000720301c08111700141060b0060300a00f01500c0b0a903d40c920f5200f44c4e10111900e00120345a101b14440307030b05100890f510880512850a009401c0c2100010600f12000d0084030b01070042e00c51841d02d0b08400c00100b0f40705a8030500071035440680d40d2010b0222 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 436966753 1250 436965503 436965539
    0x8070b16020d02070e160306080604050c0109091104092708092403130201050c071217030411040c032408010501050102070819080906130e06120c0f011701 68
    0x14040c0078840e0540364000581c06007075a201c00c54101850b551b51541a0041300342d0042003041686400300010403c8061008500585c0144081c2a40c240386500140c0100e04581c8a00b02c910f103080b040c3c48108407028141c0c1c0c262000f584010452103c2c0840c0e020341980700300321940d903c60040d00400208010040100300c00302c002d0b110107040f0344140f50464540858030945100d0150301b04000380c0c46000b80c021a101d0948141404d90030f040d0402e504628011450304114a543d200d4000c02043c0400c059062406101d22081c070341c81c42c40e01d0b40e280178524600c0b0098600440e21a031340700c49400d00036041001c4600a00201e201c80e44170501004200b94118840c0640d07039403905002080d194400f181c01e82c19513101000030a244406d00c011020180c0e45d1900030740e49441e00b440203801316038915004000d001c0d40c0d41d11000718241411060041240060101440b0b942040e00452027200d0120b0300005260049910010103803103030300180c40b9209003070344590b40c800b4060700215184002c0076060140e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 436968003 1250 436966753 436966757
    0x16020c090c0f0c010e1c0c08090117070806031501031a06120f0a1a100315020f030106030c090e0712051504050403050406020d020c092802040b0901080a1109010c08070b16 75
    0x180041b00c605401c0680c0c0895080d03000030707001750aa80129015800400001c0018075040b20782c007aa051104402100589260000449180512049160030407100b288144903504102055140da55030b00000c030748400c2c0c1004042800400034840340d81e44c20f20182051a45001c0d614603241c00d000d40c545650f0807000413124001d446020040f00c2254440081c4226282c8080d060b45a003103445802c400714002c00840c01e021f80030485152080ca501c00594001c002d183c4001c035014450394000317001c1401d9a00007140200401d4108940150702006110244403c0741c000209900e810441110310790f000301045400c5801c08062104141e030040081c003c0326095030980b64040c52008049031101e03050481c0a51260611010500e81410540031041c911104121495101550b0916100303981140d402410308a81c003145400040d60000c1005901140082c01000051804e1706840d01c24040d9840d00350400201800d0074041007480011110304607046a4100940d140a49203100010400032039100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 436969253 1250 436968003 436968013
    0x415110d12110301082e1802030f010b060315010c061812050a02030a0e030a120207090e0c0d0f26190f0e011824020616020c090c0f0c010e 61
    0x1c1203400d0041664161034400d005000d12040040c01b11003504100000169410030010042c90000e0440c402c003c0b036030301800500b0071a038079540101810030003004031a1400781d0506140b4095603075040100ea5001c10a12000c403903000325040104c8240c0349440004220720b04d00301c5181d83c021200503091841e9446a004141d50440401c021140d60013145076203009a841405a40d4403540500103808043d51f000e001c4824120349034071120000004c1c45404005a0082079041c00030000e83c3c010003003958061801030059a0b242c1000c03503c480d029040280c01010000c10300c01c20409000384440324004001d40d00c0c12100c58030345014a41d40d000016091209c2c1644428941c00390041144044c40170051721200d44444030302e001036a54020140b604101e80c61100408110701c1005121303454441403d4030604400005402e001c0d24020001e0726128484540990446400b07074000b8500454110580300740d040c40e141c4003049440780c00f88000403030b11101d0105807865401c40540c80031080051030400c0791 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 436970503 1250 436969253 436969271
    0xf0f15120305040603020d110d0e01050a090c0e0a0222050a0905060d0b25020102090906010504080a082206020c01021e150c070804030b04170a050415110d12 69
    0x3840181000c100a0200350180300402029020754041e03c0c0c049108a0045031700780b503100b000d240c2c90b484190010102d543d80d0402038500502442066485000b5000c2046100c500380c84406070541e043c4a0030145260240001da02101282c0580701150160780c0044c10b10702d40c80c209090700c0c200c0c6028103801500005000122910540200f50044d480038002d4282641c41d40c684ca025160001c051074588401c0b861010700030624460705070081942c0c3d500040e01c40101c80104840710340080c003c2410407405010510541c4008105280d00307960000d10107598002c1400c00c0082140400507003c0049a03800c0006421030f001304200101690036400c0d075100c51501403074110404d010602c510344aa0200300000034214441d20481d4004a60500803400c01c1c1540e03507040001d9006d0741049400407921814007041107540342c02030b20b2900400b081310b801c001401c00c1c01011409248502100040d081c02d891482d180141000c4d6503852510041d10001c003103c0380080d01d12814029922072961a2030040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 436971753 1250 436970503 436970519
    0xb0c06070813030c021503180610140d0512030106050a0201360606030c08030c07090225020105070b0405010c09050301020405030d05070c0801091212140408030a0f0f15 74
    0xa9100da07042c10054800c800142c1c800300c80ca440100412600110b02e0114444d041d03810303002075403007061460300300003d440c4104103090501c103020304400102e20642c4d07000d0101e0311042d41c40b00c02019090792417803210701403418010700d0314000d102912038040f0000000719180707500000801410443e90003d1092000c096a10302c3c099500c20352810100804402c41c10030030b0701c03c2991400d5039014880c0451010b4490302d4680000706150320145003075100266a4010b100d052201c074008007861300c402c41c10310700264002c212000303c44203640c18000700c030b002e1401160300602c191601702c0c0d003148035651540340c82d24040c1d0003070070a0505013000c1000c20000141d985414021202034480140240005616500090300d80750010401241d000403403101c0410151004d114000c562801540d040c0d40c003444d840300103048075181010b0605064204840303840c0540701840d015800580c0404950b40d40e030fa03049048002040103111071031030141001d41990070140950481907400280c1e0400c0c5024a40c0d501d00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 436973003 1250 436971753 436971767
    0x106030f0c020c10140906030c0a111614041d0a0507080d120c0306080d0507030e061206010f112e02071e061b030203150f13020903010f05010b0c0607 66
    0x1c6a0002801150034100c5104500c2d001e06170500400d15420000e4000004113607401c00c90f20b1006240011540d505450780c01440311015461303101c040e15071002c0051514110741c00c90300404e44448240c80c4040129225580106603070a003605c0d030300c000554844181915600c3e04002030311035102c3c520021403001008140600e90352102d450b031512004004981341c000c2c182440c00c000500d59100d000040800c0140491050004035036580f41c0d440700c603460091700340140c00c2c407214000c10081c440b105040b07000d8018940c10003000d0070050711403010414102c030110f200e485584254090001e020111020b403c905010842144000d070051402c0b10084a0480c01108001340907086450080e0501c0e40b21100c008000c107000707400200f005d078040c410741003840c1c0162124a00096001081045402e070400c80705440c1041110070300f200800304000512034210828042415590000700804642c1d001d5211811b2000461024001580e60300703815803071904820302c6900d050103844005001b140c07241807 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 436974253 1250 436973003 436973023
    0xc010506011e1b02030303041b060309110103023106080c030f01210b0c1206010c2604050a0303031b0503091203060402071a1006050304120e0d08030106030f0c02 71
    0x812007011014201c0844118003a000c0712882d1120907403503d00980c50a00055118902451821800c8001e03461000415025640f01d94101480d11442c50005054080d49020301c0d03070700346409621510b102c1201480400794058140d00030021044000440a810981c4811200582c403400100c4e40c91903144080d500c02104e0030640f030200c10005200780c40280090360160500c5007c001d03965041c035500c0c40494236080c0e40d03001e210b08010484100c0e1001101c03100c3e130f00420a280c0f0701c0c2460282c0d034482452039011800303081d007449010b110442030f01200060310b0080c50000d0114441c6603980c1400b4004048146001c0d4080c0038030b0380c81c1507505000301c08807070180c01044010030711228005080c8040d6040030703189070740c003031380810440c008100c1c07141e04880a1a15401202002c0c24000b030280700749030350342e44103005110040c0100700c04150052110705d10703a0414100444403000c1c0c50000b5031042070700750008050060200010a840c0e40c07542c070510034071803503c2c801c102869000700260b90381c0c0f446036 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 436975503 1250 436974253 436974287
    0x10c0212040b0316050d1104051219110103020c240f160302070303091505070f0906020c191d0406141302040c030b030a0503070c060f050a0c1e080c01050601 69
    0x498241010044420b421095034600030381410b0f541040a01640e181f03487d0100140804134050200c0d20303000c2d08008008140c440107003002c4400462881c161000c602d400741980400b0a00811264081d40440b1040c2c00c80f00107440308103908011020489224048003c090240030b00090812141a0001c83c09204200c01841034500d4140c4110003950040c1400c800301912a103e14002423800c408001944d0071200e0003194030720303080c40018104a5801e103070408118907040e00f0481c0540105411401e01401d4a92070310030010341001250102036680080c6460524007110910030544512050245225500c18013113141d1001c5d0100c4286000c1d40c0307070070b24a191a0103480042c542030713100c0c0412020508001c03407031503410390020303040001c1004299529080091902c5c2001581e1001002400403820450902e552450006100c3e00501040c0c400380020128a079040c00300b44110060f4608120303800740300d1036140d840d2140e01d603040556821419824140481d410313600506113600d0450300a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 436976753 1250 436975503 436975507
    0x50108040302100c0e1c1a0705070209180a03022104051c02010309060e03040302030111070b0612121911151b070f0308180a05102c010c0212040b 64
    0x80071100a14042d1000300520001400d9214a511b82000c0100012050644842212018284041c2e1a80760b0316415012500c600f08001040707421034180d400c8550180d40300d88440c1e44d044112201e0b41c0395050070225a01c0b44480d90800c141d80021030f42e4036540105c1c008104800322403103014040c061030090a601100c03001c0880d044994a12003070398058014500880d83ca0035940b1820200c0da03200d6030500c0290030010301802581800d00071030110304858214a4504529625811811500580100d1048110440d840f4410703a080040c003c04421a8031001d0751122060030100c400d03228504298003144125a020255190116103005540410320407000035a4642c0500c80128404000b1501d9200c1d040c04040c02040001c13190800051107501e4074501c2d418941640c1c6803c010101045683d079001d14002800950003052000c0e61103421240400c2c1c405803052401084071820300301d07441e840d2501d5501c200803030b01500001c1d441410b80d000c1c1c40d1a400350400d0383c8918070a5000d011041401 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 436978003 1250 436976753 436976773
    0xa0201080f0916030506101d06010c0203030f030a05010e06010c051b0112061e05060412020f01120510092405060d14070e090a021204030c05011e15050108040302 71
    0x4114500c03640102c40c0815540009504400340e039800007a0781040c0d030b10703a0100042110044100d2840005410f40305001c09600f11b01051030084584024516410000001c1114045450410a5460403d6615600340c0c03640f1304517000c6801032200340b04c1e03100b01e0300b04180032480305d5000d07180485007550042c0c0503220002c0410000c0022042c402a03507810045441c8030208803d0710751041401500e0100304c043d010717950807a0140d94060658118600c02d4400704000c2001548405940c85d895905803100840c8080100050b44d0501d8100003841da0391307082804100302d140740700030740000380c070182d000411901c8141c40d070100c54500c0034a80c06e00c0c811944d80d4107114615010001d4900c00c1a40c840105407214a90b80b011984001590b40d0760126070000000c540d40d2408144103944040707020070450a06070b4015100c030141c80040e0001d01482411141501440000e40007950202c0002a401950715080075500c0010007540b02c0711282003070018400301e07075903218540b010300440e0190300820407400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 436979253 1250 436978003 436978021
    0x3050a121b02010309020f13051014010c030f03150305010506090702011a091314060405070e06010e040906060b0309250f05060c161212080106050409090201030e0a0c06110a020108 79
    0x2800300c0342681d007c0300701c803a0340c0c096a030b07004040d000319908105c01040c14200284501c048207a646c00100c001c10b14403406c082541d92004100500c55018504180d024640203070980081c02d144c4011607503100c040310040705003c815040507002d10800e6401c0c428542d9043d40481c2264501000628020104034116420345456031480e0381043d074a440440ca4105141e4441c4800c000240c541c81d42500400108000c0c054240f144200402030403008601902e041d4000030880111598668070480d650032014051050950044020b440c11480072551f07030410441455035030701504c04072400e0381c05040b90680e0207000911040e003119801000244503d00f08020032002d03400000b0031811910480b0380b4007415028208003200100820307900d803a001c40301810540040000f10300480d09100b140001009010740c4801194100d900039500011210031510040340904498085c5184a2041c07400e01018400201d81510850795180c5800b02002d46541505480d00c2a044000c0d010130ac941000502c008 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 436980503 1250 436979253 436979261
    0x160f11040e071211030604030c1a0708010905071112040f05060f0702150d060b030604060b1309020a050706060b03150a031713080a030807021002041211061303050a121b020103 77
    0x2620400340c613441c0c0244140803070b18080c0304580940014900c00040c4092048900c0c410350620381481c203908840c0f800a034043c00804062003025442c07903a6a00080c10103225202010340091400c0c1503407440c2044c812180740c1c0350010701491881c141c5c07070b0800085c1c500d440c0302281c20364a0070322582810400c180e002c02007404050f620f20020020104815000300c4803a00c01c25001d0444a900c440d00d07400e100081c4003c41e00f03580c20115000d0400c02c200d0f03c01c01145980d900403105500c01c0540c0c1d030300100744115098094510000c2c0f2050400700702040140e07041010b03500c10040ca612a9403651024402c200030107c107448003600541a80401c501c3d9464154000d00c90540a41c00034805640d640c850140361004901e801e40c0080c0d030280501031300c1c9a05000c000c0f43d0102e120415400d15050411959203c00c0e43c90703001300703407030b0303050031208800d4541109507000c64108010718050b0307a0352801c04503152000740400b140c0120180000c04003090060a00c640303c800c3d0807900f02c0c25907860358010360081c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 436981753 1250 436980503 436980539
    0x803070507080a090810060e06090c1e07020f01030612110406030c090525021e0c101d0418061805031c1515080c160f11040e07 56
    0x41045401d0100d00700070000c00c1c40601d203a840c40780c407601c0e0940c0d4504000c076040e0588605410b1044c104a03c1c0103100450303411410031900b102c56511540d02c0049240b01d840c040060010200f02009983c5107500302501d45240240c030440c501c905407100443c00c5440c01e02407141020413525034140454842e5036201c8820501400008405880f511601919489603210601031901c0e00c1c10004c80c1c0303112100c40385844c03948a04503031b000080c1141c0691506004c0703401209035118100070788140c5500304140b07884444060b008004209442800510007a120807134040002507940c0f1005060406204002d4140c80416802502101950b20b0038041e04203040030764890b2500c044a0310100300184014076101c0b00c0800f01040c600b4031a1042801c1d1790a484142100c000944002c010900030b225a1340200e100602d00f41d0045d0b590302c07030034603275601503940ea07861005c03003143c0d5540c2040f0b032000d00048054054150a08202c1882c2d0801060b55440f00010116811000042100ea02e48001c60420 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 436983003 1250 436981753 436981757
    0x3020310020712080c0d1506031802010914040f0c2c0f01030e0a0501470607020a0b0c031314030a03031802060705010b04060e070203040302010f0e03030c060a0e010b0d080307 77
    0x6003480004001c6c0507116000c4c0c8021818451001c02c111aa030184a4085484220300302d1759840485a00042c03c400f80910560410701ca4907030038000316030780303640c005000305451901c100200d00c45080d000b04011030300b86000910005820b8002480c4203c1c0030702502040c0003c03c40d0020008050045000e03082c003000d10000c0b4418183c0c0390000036800c0c09203c08650420461282d41058844810b41c0803040100d10a410b50340d5400a58030140d00c080e0040d1030340170988180f82d6428180c400700740c007814160f0100268220116007412160310103c01040401c40c05614480781d1601c0d03001090700d002c44643c4e01903043d442100c41e800040d010b5084140e080c1e8503814501342c0a03102ea00070a081d6806507408540c180d42d1211152002c0c0340512510f00549400404000e0340d140c500300195881c0b00b6404080c1c1800380b005100300009124640012003030304007909482e11a0000301d680c554070709042c0c420b801000e007003c0080b01280350512481030301d03200007041070701d0714440303a00c03010001e5001070080c0007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 436984253 1250 436983003 436983007
    0x11509140d02040e01020a02100b010905150309071502010510150c061a03030a0504080607030c09030b06150c101a0d060b03030c010903020708060a0218060901110f0703020310020712080c 82
    0x7060940c03c6c80a4030189001c0d801a0152a91000b10181155900741007141400501c000510940e181d80c20011608150003022a65a071140d1a440d89821069842048007030b0036102440212541900810301440d03000c29809031142d01c0d420840fa401444101c2035000032440e6121070089251a000341c2044800c06000c2d42400c12410040303421175000a6010012420004040188040c100310890784406586010001c0704001f80c0018902d0110388006810401c0b010041150f558404401e0010f40f0750040da003680d10182e110072651620001c0034048078040c640807000201da4050031401078405402012000c00c142c265595030000c1103001310290305844180701e6a41e244109119245005c0d020342c000304401403800d0282850050300414480300f0700d00501506004001500182145000444000d9103c614500c012901da40117807804c1c1650744035580b1154024007002c64000252402174068880c0b00d05070920760000c2c3d104008000381031036513001d100c050143c4501051a0030014503c0024 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 436985503 1250 436984253 436984271
    0x2c0112150b0405270105070203070210030225022d041a09010609150203041202041a0406030b010906140607030e13020309011d0c030706030506130f05011509140d0204 73
    0x190441d0401c5681300e0203880c507444a40094142d603a0354a1400130f01c0b030028405850314410003916801913102c001d0055403032490031162540a81c0680340350304070a5001d803540c21a45069101e8402d180c11059010b030011041920329407003200c60b03080710014481c1711106502e03105030a2000601e030080101c101e9501048911b401d07661401d01542c024491940d640c091682000d5000740341c801022041d005650003003008003d00715808032071002e16901242c001403e0807181001d0203186c003800d00300f280e0040c940100842080a003e601c24107881c00c400007005420303200c65602900d001480c1d80340c1d0744904140301d4800024401c18402903a0340300500407140c103065495407074003a604141d40320b442a0b510341802c00030380019030040c00d40b61801b5800070889000701c40003003038035030750700c0d01509082549907000a800c5458140301d07a2540b041c6030303504000b0b00c550041c880f4000c04080c0191106100600880044144617101000c1510700c28561180440300d48400c115401014220807038001c2e031194000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 436986753 1250 436985503 436985509
    0x20109150906050d09051212060108040c050d150c0c030f02030f040b070203070b16030206060d03050a110f161508160305040f121d0a18180803012c0112150b 69
    0x203851f00400c03c84410b0700c40f48004006891882d0041041d4104184601040003180c044d802d01e10807204152500d10721618107041c0f14910502d0b41c000f46a034a42080c410102056000c54444010781c081c5e500e4006030211080c1c1240c80f03109400c80d4062041007400280704803882c0c00d000f056001d200070115400710b41c0e01e000346107450708184080000840d110060000307060f018841e0650005048420181d40d00d0980c0d40900103001d16110001084504802d211500f1001c1050340015200c42044600301c0410400c800401e080314016018540c0c1507501c00d44034a4000e0a03807600406101c603144e0b60b4486e0341031048005010080007a0f0f200b1442441c0071011507901c40c1145a500b140c2c0d40d684505180c03007a208007551400c1e03803d49001d1045544200100311480e804145040360f54207000c9054040d130b074505050f20100740310150028a0010000999030108a0711824000c0341003804110107107940c5074404150801d20405220b00c01014035a030000d0302c2c070001c4101c001d1064000080c1d0101040c04 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 436988003 1250 436986753 436986763
    0x603020315160306050913020121060f050f030a14191208060d02060d09260901110f0c0d06020c120406030e03090f151e0403020109150906050d0905 65
    0x980c0c0034100d0018203000000030104480882c40101d07003003d106682c80c0c400441c0340d035840207000c0540940140c3c05241160b200c1c555031504081c0b5004414001c5402e1030242000b03280e01e1280102c1c8017030f8400300040b1420040001d01c1c0130403000300540a421100d840328241034011112100042c059540b41101503601c020a82140c903028104880c154080072802421480f405007110303205e041c0c9511440016503481e421125180c11284012484001e94038000d414045a2803220301040120606c450392200d0110140069450036a60005c034500040c035456243c0c80d01c04010000b540000e1600701d920f00301008181d404500c141c100500d131007945030695040500c00b00c011400c0c03040c000307000c10805905026981a080c030060155203409036000004030b25000b1000c94a000e29101c0e000e100f01c402820061f00c08403c070807060200c20311000c0d4100780e00c1d40d00c280000c030701264082d4004600c10904a41d0800742c2c0b0b5a548950750071504100040d2640c0e00054412041592902518030001d10103002c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 436989253 1250 436988003 436988023
    0x30b04081921051017070e0901051e0118020a0c080a084003020f03030106020d0212041d06030709020706020d0f050f0c0706021209060711010c091806030203 69
    0x2591100022a5149144603004480010b801480c181070074010030850f0410400e0454845070340c100841032100803001e00306005a0300c211107441a910030070003030f03034011740250380f0070340000800800d882c80c4900c0c2d1450300a401e0207100325035148403c0c06600364030143c1c000c00c1410341a080c04843d021070b580d6405407650201c0045400205403400303001041c0ca1204412071908100740b0455452500c0d82824101700d101d07040081c00c40952060004141802800140202c1c2c2200068903602c0da19044041d5546002c24500001403085001ca00640e40c00c520035141503415060101002042e1504d080d081e034800640301d141c3c1070049150005809a1910092a52602c180d40158035128103200d640112410a6040070740c82d400c050401c1082c0345605a020b50000b650101140c0714555414814000d0081c201e20a52019611040c0079401e240041e01e644a80506d0340e5544404494510640c00e0b210140e903040041040403006005100036024080444842d04400082041c0e50b90002071400c040d42c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 436990503 1250 436989253 436989257
    0x30f070e031c0203120c090112181e05190c0603091a0910050c120103080304170307030e010c09050306150d050714120705030d081e09030c011d0304030b040819 70
    0x141149804540a45590b02c41451b812442c03d101c07200001070038441e0051303c1c01c2c8640e0750300c620308030090f00d110042d0b0708565040034144206c29200009a4020701d4000030540c2c4d14401c6400180d07901e2090a4460074181c2d0003403440c250706290001c01c0e40588490501110f0346e200031418200400c40d0928564811110b540080814012009580d4100d4502038102d240c904000c01c01700f801c3e50360111100d41101c0e800114203a60f50364900304040c0034000c1c0c1003501404e031000801e015000e641504184a1990300c00005c03c003420030341c201a600101e0341c2c41110b405403c640b000480018400061402c20707040549901c0c4004925581d0b241049010f820002203126041a02860b5040541946030720014a000406409007042c0010b5501c0c10349202520070806040d0002e0ba50f20b0048500344142d00001c0a070342018100072021607107a03044591011100d45c64103000c21490000400c030b211122200c100a180381c141541c0b01c0590320000140700380c03081d100070485098407081000075140350360425 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 436991753 1250 436990503 436990507
    0x80c0c03011b14090303180a031203020702181b09010e0a0909050705060309030d0b060c0a03020a20010903060902060c1b03010507092303010b0307060c0501060b030f070e031c0203 79
    0x1e80041e0483c01d8a400342200400e06014120281c0c40c0041110310410300e0a000141041e00c40001035031400198000403d200c40103000c00001136016005002308034401c95522003a10865501910054405c4440c8000480d1401082510b40c0301c0c40b00901d0407140602d050550580d03090081102d0b00d0f070303d500800c1d04565408610b07003400003d00c00000900000c41c0e8091035405c1030b046060703803409030305407041d40c85541c0c3c10000c0035130340c60004486074001e5100a95080c0703861820060740300c041805041e120b0341c464503404401d42420f0507010350303080b9058413501c1c02a419615240020074285000320307003140701000110800c6004024087e04440c851040c0350500344d02d4000c2c1802c0d40c0020300408203011500c01d090041890304a2446111f0808201800001c4450750009002d040900926a054040e500000c01d1560340a000c078806603000304000d101640e5100001f400c0c5d44001ca40d0b1342c001508170fa001c1034102d071158031140184c00004080300e04104aa001c0000303c4400b0902c490050b81c00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 436993003 1250 436991753 436991801
    0x60405061315051c110409020108010614040e09010203070906111203040f050703050d3510090f061d0705030c0d0207080a0f0e0a08060c0c0709060b0406090e0112080c0c0301 76
    0x207038400185e141c0c00d0980d4248204880b66002a00201060184405014550082c044000b01010a42d00100141043d014990809407030340c900035030042c2d48980c0011503440c6d020402500841012000300c0a03900100312041c0040a1111581c0000e04201c50301840c03242c0800116604108080145015401074009045034500103015403d100040303202e001e24150700c0d102c0c0c005005490700586a242301e039907452540c0b4560040a101143e80200780030510306005141038800650000701507646a954164203200003c0c400080100e08490400001d001000000e00403210340c40642482e69241c200942024101e595004140e0060503000e400950815180240c0d01d81c40b400b1032481d01c6c0c003a23540705034a80c1070410442d22614010501010041c0008000301da030078040000f10300503d515042004540c0c0c88181e154803a610a100720740c0011004030b4080b81001034160380c603048502c0c1041e40320012441d42d1b1408143e0304103500d401254007800101440c03d4400707004010404400080c118401a4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 436994253 1250 436993003 436993013
    0x60601090f2303030d1b08280b09041b080304030b0106030c05070503040312140309070605031e010e18060c0d0b0a0306090b04290c0d06031e0506060405061315051c 72
    0x10949810700c10032880b803082c030049090040013050282e00d08d18090800b02442d5003820003a02400c400580c1121180f000c20003800110030300400901160000038841c1c65907100b21035540c1c052804050315540703c0c4001080200c2c00f0341d024080f03034070003070400c13a0a1190507210281036400c164000e60b901c40f6110010342c0a50707440490301011400454100381182030641c1403c0e80c4000700d019030400d2000000c01325040143d00c0f002015a030f070b03018036040380c5582c443c1502d512031102540d0840c00d404a5822003446d07600081512407040040490060030a03036030340403200103002a45a09900014000000b00c0418000c2c01482a240c0c09091820014100b924084840860804c024401d500030340b481e16110034610039695401241c5503000c9502d40c1000c00f0380200504450b4001070002ea450091507805e1100380200442c1c150185c02038904907903a0000b4041640c9040314502d03400007281c001c0c07049a80690740310807402c1c1c1101004921454491020855800c4100c007c0841c00d42e9503038400080107 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 436995503 1250 436994253 436994291
    0x501060e011208030a0b010909020f04091d0a03080c07060212062107030b0406062105010b191511060a0e1b0114030703090b040f0203060601090f2303030d 68
    0x1ca40b04800b100d8226441e054101e010161203060199203400c190741441c0e00c940341c20805050101000c543d141d80b04400241190300c144101e0f00c1c01030a00d07403a1504065000c440c50480b4440344087e003924009580d044561180080048002540501c400e8000c10040d00c05081d030701c0b402e101c100c800c600b000b200700034402400b10380c21a8a508001c0300040009008a100c00c202d952001c0c00b80c0d4291114608a805002150089042000f401110103400004844142891070285000308100b041c2c1d40c050040c80e041152000c554011165820007012000092244802c83c60703103407105a81c1d0781c11004600f00101070720615401510740210084d0000188072110040c480501161f00601d011070005c1c00f99071801110700c45044001c40082e00d441d010390042c1d03450b960b1080300c100d80b074906844d006080d40b0546800b40d01a2003108001078040d40941800401d035010403148000003494071424140c0c00c80f11005007000842c24505150054408001520f204401140040340e06840b07502030b03100706 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 436996753 1250 436995503 436995509
    0x20f0415110a050d0309020a090906020301180b01050f070303091b230f010e011202031f0506070f02040c091e08010b0a0311010309031710060207050f01021c110601030501060e01 78
    0xc2d800c240c258000098001449450b021070904011403100e1903030000403060310196103d500300e02d0900b100c0e1010400160b004606807140b00b4681010310b0100520181202e94003412031380800c5040004021b000c0642d0082c0823014460318021828800e10b5030303403e4440c8003140e40080310756217002092100018816a0041d0f00f0351741d18004202031081c100103500c00d154595890305001c11311000800507449507080c0e1900d2400110103541e02d041c4020228401d0746500d0132201c2e240661400401c451811a00312102250422030104403000c0035002c000060201c0ca104005029110300001903680c0c40c046a00b580c0e00c0350010100c00345142c21a034500791000d26640c1032158440d2242880052060380b03411072907001c2880d00280c07918882c5810b8801c0803020000700101402c0703408002c1c0082c402c1c02410140c1d040d640c00d69501d1a9140e0600c40d01c0a0145511400744e00000180f02464006401c0b01c0080181482c0c040c4030300001500150521750301383c10650311651150000d000d040c642440755801 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 436998003 1250 436996753 436996787
    0x190e010e01090e04170a110705011d011d030d020a05100516080702010605040207050c030c1c0f0f0b0705071106030103240603020a0f080115030206040b0c01020f0415 73
    0x140103040400201403840070701801407603910000c0442c05021000c04007081c090403400b901c6a035030f540040e0160030740030201d940410500c1000404603495101e58800551022920060900d0041210044d41c440e06800c02580000e03040c1c08205125550400118950748040c0d0058800310066050860078480c107904400e4a00d4245000e20010300304400c110030380d080c994a01540145c0314203104901401147e4805036009001142403800d100c4085900496a042101141c02c00e0082d602801400c0c14003001d06000c0c580708100b6100800c00b180c040901842c41054409080c004c0740e40c600b40401401e1310074000003000483e85e8410000d054140c160baa41c401c41e01541190326543c0c401c40000003d442007442a900040d44880041903074001e60060b43d401048100c2c03080d00c8200c500c80d2101c0c580b048a8003982059039041042012410020a507900a002c10380341505041180802d03910491405400f59403c000c0710303018103041405400501607807010380045038103c0ca801441420030205040d4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 436999253 1250 436998003 436998017
    0xc040303030509010c0512070c0b01030b0f0a0c1e1106010b2710030b030a020904080d14160309020102030d0204030f02011e0801170703020604090f0501080f070501030b0f0402190e01 80
    0x1005d0350080f0903101941041c0b2404078040da1388440482d8001c030400e40080c28028044008410040320701c0d03c0358450300c8141d04c81141c542e12504901c06541c0654860004510004500c6078800b4080c4a2401314450070b0800e290b040110300c100a1a00d139003640240325590b0089000c01c0c9070081c002c1840d18005eaa19891519039850000098912150642860501d0b90b921030354421510180250203103aa00204425110b10342030030311034002c3e803203900140b403194a4401c40c1425005030114060180d02c240d00c440504c031100240550087c8602c000590662101303200400000030140028406944101654201e50382103200143c00043c1007180c2c2200841c40d8a291500c8035440204141110030422010300307070b021449529800d00d801d6070400781d008280028007282074030300d9802c828013001040100300856a03032025010307103c1100320144083c0e0b4004400c200801c4d81f007130b0852080c41e207004049411214003040010120f0380308021540001607005c4038130348955002200402c00b1202030a00c0c032 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 437000503 1250 436999253 436999271
    0x7031103160b0d1d01150501030c080a020d02190c051207081801030e030a18060804050d0e0a0f0e060109050613030f320f1b0d11090c04030303050901 66
    0x44055524012801c00c608007055000000c200f0350071000202002c03090a40c240d11048000e280607080e4030703e0000700070b2550301300011154403130721032441c1d21070455495481036200d144040c801b03580000c038840702a9400307010b00306041403240040d001d04007280e104d0580541c5549001030400218665a0912403c02d22504000c10080004c680510200c22400200c1d440e1403401a4020482742c40041c1161202140c44400789802140c2c00c4480004160320004169a568040b1040e06080350010710b1500b012205c0600c15004030424840c01c2402400c07052b005845000126883c0c00903030105803000d01c1c003018800c2c10750300b11407190041e01083e91247c0c41c245507034402e594104e8003440000c0400141406007414480d03101c0701403018900846544844c0101c44204008050020011500c0c9010300349444590000014411680c8200c0061000410107418104010071041c00025200c03044606120003103552102d02c030341d20a4410548440c0c0b03e03819801c0c01411508000d200b0901685020101 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 437001753 1250 437000503 437000533
    0x3030906030b0a1517150406090603050d050706110a03020307031401080d140d050109061a070c06030c051b0d23030a021b150a050603030316050c1e07031103 69
    0x381055030010b1030300100003400075104985c00c1c81000b141c0d074080303840761091101c4074080402d00c400000d07040302c0034803841d40c07540d0580e002c403051440000c103c0e0340035443c03c1c40a680039001410f60b9a004000001b20b10606144501440d03019050040009a00004101c2310541601c5000740840251020001369030500845690368520b0305407280a20407550b4014512050440494500d4103231401d0501003540d40ea4002070182c0340c7c1d4014a803940781c2215009200240400c00e07103c00607001a0342d0710005107440e60903001451010041010404200245030341b031000460744801c4004810020401c0c8511480d0080c6540c40c400f4604040354000c07010b82034050011801ea0b07400505c59000141d595000030a440c5064080303101e5582180614240c00c200b0903030b44004244144002142070109070b0701c4108041e20b921040341d4942501e01070fa000701d0455807090340076112103d5420308450200903441e081003952003260159007260340c0400320900401c034005020103001c0c0402c0d00200b41020b150140 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 437003003 1250 437001753 437001769
    0x310120309090203190204030c03060c14030a020304150e0c010305060316230a0617060603041e0503161b06021203070323090307062409091407080703030906030b 71
    0x780b0281282c000c0041620b0345520190074503910000c2c24119501c03aaa4500707058030048501c4140c0d00a4540060416100d00805400b814146801d1100c1d11b1681c501c0030041c001c0d0405013003a03172002c1d107103052001c03400a00d1240c803000c9d401d01002011103840c0e64000409032040100614001d4001c840d13100130890352501342005440501001203001c20100030218400130b03c0d1040b01d136100e10f060b1030024509422201c02c0c424030102140040c195034a01040c400702d84411355004296605890031054507140c88007a10341454030803005e0728608091420820030005010809a03004c0c100c40541c02d134960b4030b902c2090001d00d0240081c01c1d4500240c00f0320022400010701d0041070540700e02d034000301c40c003030288551030909800c4048045030800c001c1040e5039030072082080701c0382032400d00300101c001400954501c0504e4410450b4154074140641140602024001105e8404030040d1007003803140180440303005800410020400e0702d10f035040050048030036503c01000d1510b000c05810f1141c5900342 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 437004253 1250 437003003 437003009
    0x9010f0c020315040f0308011e093b070801090b041e020306040b0f06010c05030a0e010905040203070206091006050d030f17012c06090a090f080409020310120309 71
    0x2849540310030280003182c100005402000002e10703020702044108991507400201c02406a0798805090f030300d0b540758042c0c0b8100484100c200c00030001d010400076946820410340b51107104880e141808410702c1c81c02c0307840e03201c40210350035102e0800e507162504130410400000f004030400034000c0e00c045490381305000401600162080c0312000501c4490b0041000c4580d0059010703045554a20701810214110041662560055205030340030440360741c0315490018295420001851a000c07400030300351100c403440c00d8114144029154001001d40d15840070710305c200c10a401810140c40d0842c1c6042c28041010000030300d0a2034140c00b403200d52103841007400565490f04000c07080c0310701007401b030f14501c0c001602c00350f50a26200000c510742d1102807102540040c001d040c51440b2801180e102c180c140101ca030660080d203e140040c11642064018611050144000810543c015194035a003503100e9007002c440386030000240b10000081410356401003c015030304608001440e90000c2003417680e48 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 437005503 1250 437004253 437004257
    0x71401030e06010b25080a0e0906010810210203010906061d010b07030305061f02070608090f0c0f060705070f0e0c0403021e041d0c0a0b030903040306020c2109090c09010f 75
    0x30703003101040000002c4884201c2d0004550740d201c0702010710051a000234084070314018103903000030500c6075004010301401600b4100d0307524942c81c24410350048252108140e9103600b840d040008001d41c8080c414590502e010b000b011903030500b4a000c6900c490700048452469201d50740041042701590070a840619503d0319000c200c075110480003030405102c2003040d452080310038055000042c0c00003001c0c4215000c54440440c65074400043c00c0d290001c44054480a0300710411550b818030700928080520000103203610b051000a4565a00e00050794000581c50138034034070180071000c00d00e540b40c1e900c181110030807031616041d98040703034100c0c10f801c1014000075910407268085640300e400c010f4a4101042c986c2007420b0040d0841950380003001081801007181c90f40106125118200b02c910030900900190300d01440d540c0c0700b1000b544210300e03c070a07900441c21002080140b0f10010b0b0f8031107907517a80d107a854404840c2009440750380a404a130000302c00b00002c611a90b01b00d600c1600e03205040c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 437006753 1250 437005503 437005537
    0xf040b07030c060509060a06060302090a06031805070e010e10030f0305030a06080f0c090a02070b1b0d051617090601061d0612070906020c1f11071401030e06010b 71
    0x9440e0540784888882e200801c0340d400c1004000c0c2007100091440d12948180d01c017803142d40da85040c00d030102c1c450110b0301303504800c500000b4800b050003908030b80c195880e030034990f0401d01d42689032242028019000031414286203001000f198440165898101505940d0303075141a1a40d81c5030203011100c1c80c001400d1080c0400041d00302c1c1410b502060007003001400343c811003100554135a440f450b90101c400c0c03042c036403100414024030591095a0709a0b500c0305e85d040d038035182c055060b0800f5980420010700310300d00b04500070f0b4025490003210f008403051410700f011805c1888000e01078184c5022181060050300341000440032000880d9411aa16410410703c070a01e14400b0b602d03400c199441080d008080051481c01212880b820745100704003a683d000c0301c1c03589965040762240220b0031840c0c0d000000c405018141348880301030203c16212400c000b8009803600c9650381c144010f80c2d10441c141e19000c0c40185965800d4040c030694280c01c0c1000d040c181d81410707022401800f0399200400001c1c51 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 437008003 1250 437006753 437006767
    0x206090f031918060906020d030e060a05040519120801080109030f0f17090601031a040b191b080a0c030b01080103120905030a080301081e060f07210f110f040b 70
    0x5030301c141c2103c281481d200d60005840d0a0007070100d44040c440c4100610a2001031441940b10303101c1c0c5080180d1440103003032a07071604039101c00a010040d00544190084000300d83d8240c04280001c00340d54415103000d407034200c241070094018001644240320590601c1807030070029330b00c925100c20313101190034501c0c0100c840c00802c8402405461540c0820b9250b0004d00c280d0900003c2c9c540c3c100ea01c1100c81c2d02174410071600f01607004c4016a0000c2c0007081c0040828514500241c04040b0b00c2c0c0a0340000941c40c2014035202c044060200c0824003013820042800310064060080f13038504106030074113000802100000a02144c4140310242c401091040320411840c841d4001000401c0000c00f00d030b40c801e069007049845d951013072040580901c21300070440c0c40c44c0c07103225068002200c400c1c003500d8030741c2d00c1c07400d001d0000200030151420010480184401d4000c0300040e82c600103c070710b100203020618a170f580012204030b05507203c80b034070003442810410300c1c403c000c440c16981e41d1503081e91a210303 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 437009253 1250 437008003 437008007
    0x513030f0e120c13020a1d150a0e09070201021314041506090603270204021326010e07050f060d110f12060405010e0105190312020d0206090f0319 64
    0x1907a01201030307024404640320003195400040d036402d50b040c12144894181d50707503180c0c071040f03126142003034000c9607401100c095a00050540c020709000003815041c0c0d9060f01104d1095240d000b400d000b00420101c2d1301803101418099002035020b11f141c0003c51034403d05907000d801e2400d8a1050111220601050705426200c540060140c003120350750814039141c5a84000c0e2070012a40146400a4a8941007100c40403810040c071035030010540c90b01c030146680781c09001c007030360000b10015030341186105c1c000b401020a101015081e1400d050070421003091050407829205c8201200d140d0f50301c00740301031180e80d5070100d41c4c03640c0c480100c44181d52a01c042d80d074200602070310408200144070115509500050b81401071811015030300d8503003001e9940c0c10400048450a0055000f0501604010b00160510b09074143c00d04e089407444040c00e5690759135141681382c40c2d1200381c005030001821008581d8041203016004616030000d0b0a04145110740c1b40e41e00c0c000c065102d80c200b0728035441d03550341c28 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 437010503 1250 437009253 437009267
    0x150230011710020d050603100203010623090a0f1404020301081c11060f010e07020d0206070f030e061009050c07081801030905060a09031101270606210507090513030f 73
    0x200d0388070815903d40c440713201d4410083c0300480d02c4074042d024985154010141a1084906a07400e907201c00c4801c040d04a10349510300800d8401010f0b02cbc0701000556070740d9580b9290b48000b80b0508900e07219080c1844451105c40446003603241c010343c01840180010480807510301d00481d884500c407504a03042d450202c4245500c1da070010785500078103060080440b1035030407140c10703501880001d601e40d89503d0004c0344d44805c0c164411006801803408110080e01c0b4842800486a55140109070904145d0b489820700c07070f040c0e03032101010130102401c000f5140c40d40a01640b002403840c1031810126607480c0d04142d449000300e03108440442a0115105070301030343c0210b00b0030b48c00c401110100e2624824090040c0f00c0f4401c107030041a003207140d01e25000814050500c0310400c1400515000000c0e9650440c0e0b540200003c0720801c0e180c03900415000e6485222000c901c8242881907001c1e0220b080c020b050a82542001140c1401c28081105c004242d007440e10b0882d07450324051540791071507a0101d44e04 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 437011753 1250 437010503 437010523
    0x7180506010c0f03050c1203131202071823010605180619021e011b18120c0303091a0304020603060a0e131b0e1906031502300117 57
    0x960800340151007132541c800e015000b00307814001103c3d144440044008071a0000b00d4002943d5044c101422002600000ca121501410360040355a10f03920380a5001400d58461400700d191581c070328402c3c5a5a4109105480301101000c08125039410003c0041c024031490340d030000220f10264980c1200e0b284c11080f121a00b0b00c4e2035400b0b082102052001351626140d10901e6154141c400b140b032130440d0188100d5000c0d01c5031400564010001440076a080e00d421404001c012010b604002440858030b40c11580540c072488007a04d0003803c61034040c000030000d0300012030000c0d001382c9001074080b000048030740140e0102c0f1150f483e81d40d50400070350500c40940080f44c2e03218040050010f5660002c0f00030954030f12884180b40d5003500083c43c804207503a036101d80103090304041d01081c40c070018055401004900202d020a0464403071315001585000d000900d00c10503400035041402c040404644460286400b0710b0341000544c000420b40300100600840d0300c0d0310031034124406407907030401c004154 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 437013003 1250 437011753 437011763
    0x203360604060504061a0f010c050a060615090b03060303030103031d030709050a0605121e12030f1b090102070b030903210f01060f0801030f0807080d0608010e07180506010c 76
    0x45282915040b4003400e4107071803c441c1c1d00d0030224003901401d00318440006481001c1e11002d8900c1c1d01100440701c1c4880300a06460070301840100c640803425034001c020280040303d020000000369000001c08140580c0e00a100c090002d0091000541e8040b08490450f505494513100c12158000304a202c2d0020209007907140c4580342d4002654034403074005600c10062907400300716042d61801800342d10100c0d030180500540298034001414140c2d045054174000e2140112078034040d480028000301d901c142c4041c016201d1400411403603651a010100c0c44604804405082000c01030010f96a4842c031b024181e1a80000700c00100d450038100140d138242c1c4145040f595007040242c4032442064000d4500700d0004459000100d00b6030b0007000c0e405061180c40da9468800d80c61901c1d01d82d02d00d4000358089901c3d042c03c2000801254008024080340d5104000c000780051400312854211540760362160800c1c0c005a004000b0b4000c64074549190070070f1007102088070380d034210048031004462100101 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 437014253 1250 437013003 437013013
    0x3010f0620060916090c0512040f0506090c19060c0b04081312060f0225080d0e030901020c030d020a0303020306060906040806070305061e01120f0e1f020336 69
    0x20f042c000050754216804550031000f405926094240191940c00d08080007140f000c100482c0400d9052460b00c1d485406020900e10060740d84d0b450701d06040301a58502c01c039500920400c0c0c03051411240f103000a9012010700d00601349008005000c500c2c0c1580007800803544400041e00703105c0450200e07030300c1c400f403110401403c5482d4107072500c4012084500391515480c150301e050790701c0814402c65440b18805031030703981e4440e100c0d6000b10545081410403503200d40c06200400c610780b118000c6140d1003488001035501d54400310b000a03e411440c01481c0d10960154450707280c11500860004101500f502d40584c3c1c035560b130300c04502d44d48115002160000400100022240e50100303c1034003410b016074007840181c643e03200f0401240b18441e0b1100103d122010000702c3c660181100891901040f0000f0030210558100f980413180d044c81c5a44150708282c182154884164629a1109494203011401d40c1040303544a21400d4080c480c40c116a1038400c1c185040d4840c40c05c1150034041d501e000c4030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 437015503 1250 437014253 437014261
    0x311120105010f0608010806010614072a15080403270e0705041a090303091c0204140601030e150105010305060a0807080c0108060d02091f1707030b0c03010f062006 72
    0x80102c03e040c400e660006484100118003200e010403e5030480d032a03540c50b099688021045040e0a901c450411203481c1c1e411055508510407124800104001c981500c074130382880d00d540a84c0d000d8402d0301c2181001081010000042e400080c2e0706030654100e4440310b48110814091514240c468000d1080d5014030002c001e006588a002001034414441000d031105d80700410750441c41c00b0329900d9661641042c0446016400e090304174104200d0165000c80d00d465403a00400c007100c00070400b02507144a45c0741005000d580500404a900d0b03001002400503000c180c4200d1070442040c007a950401d0b44a50200c3d202380d81e8840340d0405001d000d03080c1d4545c10b6850358032030b544982800c50207000c1500700000131018034103200c10420742c40c0c014003c2c91155680c1072540b4501e40d8641040501c4690032000424920411315203054001c403d640100384490030340c1000c09805000030321440c02c491041005000320054641c0e01ca0895040e8141000c107442c0480c00707220f20400302c02c1e109110b4030402c0104 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 437016753 1250 437015503 437015519
    0x91a0907022508030f0c150405060403140910110111040e010b0703030605030d0203090a14060715021b0703061404240908071a010e16140f070803011d060109031112010501 75
    0x201155020101107d1071402801c030328500800d01254082c140c4d8215100080c04a030045c261091600c44003e42c192a113503101c400650b980960105a400080818030420a211f60134440c8001156180d901c0b1800e0a181403007010420f070f814020300d80a02d8002c2180b00826000c0d400003000303418010240c2c1e24150000c07100941e46e0708001246482141000c1300007401c40c40c140d0040d80c0107500034049902c1c100d01521440b9040f42d00640805080e642007080c1e8040211204282008044000c090400c40c1d1442c10040242c0300001e40300c26901f10318409000000e00c500019a0404d48a140c4800d00d2400d02001c3c81c0042210890250000d000002c004040140c2d90640010b42070300c041040c25641d803100301502010380b01321140980c82c0349804611824a00070043c1c80100301150041c2850b00c0702c4804580c0103508003100c2141d00640100c0180581c104507070129603041c01c580c06a900ca40b4110300000c00c11000c0d84000341042e071228400c5040f030f4440301d0981c045895404001c0c840c41d6542d00031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 437018003 1250 437016753 437016757
    0x40b1302030705070b0a02040e1f0b032a04150f12050a090b0f06011b020a03020a0b0a120e070b0703033c05060f01081807091a0907022508030f 63
    0x1202c0c5e04240340b001a55000c25403003903805464085641c1841c40ea541c1100038a4540c1d2460b52030710b542c01d142000201c00501c40021880ba51428400280300340211410000c2c60001119400011200303110500000407511890300d2290114030701040d058031000e20a5803a0300b01c0d443c900100a00702003c2041c16071450300300c800c410b80b154032011801e640e10310308109100b0059529a0000c2c104103001c0d840784001c10381a1130442c2c002000d903a44a684d030390000f15044410b03485000124000b050411290340c0201400c041d081600c0c8080c4210320720000d4041d02c07800c090161b145140030200b0504c007894800d504c8001c62180d28150090184c0c600303164020951040d0302c080084030307009000e10741d190700c3c0b601906004000103400c040341d0380c8102c0d00644450b40700034110b180390881e440540801c5101040210b0081804c07100002c0c4060741150150315109541c0c03036103402031200701c0a00241a50000710461520b000c4514004a0001c1d281c22071a1402c280c1c0c402091484013160640350503400c100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 437019253 1250 437018003 437018017
    0xf0d020607082809050d02130b131a0306130f1203022101080c04060803040e0c0c070303030c0210140f0402060d091b05040e0706050c1903180e090c040b1302030705 72
    0x84e9050352070340c0e034410410130320740364007009400850300c95810044c800c041e00600480f5000034908580b10900995500c00ca4043c21a5138880c18071105d240c440c141814400c0c550070a0700a500e2604e42503441e100e1809120540d00001c0c459408441c903100d580d40300380e0545a0b140440442404018002790091280c02c000307000d0180c05d40101d5950211510b4144035210444040b000918241841d04104e080201d4000b080482c1c122020881d00c2e40c081020b00001000d9840b036100041d1665406400a24240160300c558400510700070a41940e40d200781da015901c0110350b40e10681079900c80c8007251280c0910b8506000c00c90600084601700800d40050400f98014040c146030380b00c0c0e1340c80801094803880103150000c2d0300098424440e0500c43c40c01403060407100f43c22140103075101d0190208904011105034006a0201c0428007101f202440042c014040c107010402130f030801ca04515143c50352190858461a0707130305009142030322951101c8626070b58440c81151646011034000d410b03944020 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 437020503 1250 437019253 437019257
    0xd060501050301120f020d21030605010804030e0904140105070906020f1b1005091509030606010305100605070201140d0608070801090f0602090f040f020a0e0f0d0206070828 76
    0x10002191951140050700e040b208414410304d81d40446848000c03021740d000b1000d0742c05c281c48541d52400702d484040c80401d08070a00944501610b0310a100030201c60403504800c1c1004080018000426481840b1072070380c00c0c3c1210b00c0c035040e8445e841c00c0100d076401d0200700e6030f0a50810f030030850b182c0e4000010f603040350b440da0241c8070b50103009040c00e5201c0500c20b2201320780d07190810303401446041c00a46d170008a203090030118646a203090001d1155416201e0038442c840002903076035151305050000c60340003842030034280041d0a1041d0380c2490311505014407400c001000c5911070940e803191a1000302c07444d90500a9a46140400c1c1c0321028040c1070080c0e490303d100d2800c0025903c081441410206c0303800410000407140300d0780d6284040c3d8020380f2100c2c1d01c04951849107030180d84a100342d080e01030142c1e05c01681c5081c27159016015030100c0c294070b403050121124005031921039400040d4821750440d1000d60361125480e1868050148002500a400e561184920601c0d158264401410525 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 437021753 1250 437020503 437020511
    0x101b050717060603030d0e1f06230f0f04111810020a0506010506030a0b0319020f0f2218050607200316030905040c12060602030703200a0b04080d 64
    0x182081d542c408040d40ca03507030180d20410a01200215980c004403440805034166081540b0000c1100e0464600c40d851008150b5500300402103044c5c1d00a4052108020003002d58000c0c0103500095055420b402c0c480b40544400d011244031a9225804071000000c640070580d1180c0103101174200003803600f2420340c01540e68a042189260001070b6510740d052f800710081419a0820081c00060703003003c0d0a503040951645072054242e9010305c006034010241d541c1ca1802d000d254010450b58440d400004c0c1d0007004402420311441d191161307442529500181a00082107680d80b440002305950f145103070380000300415003400c10a0116599020b9010755880060416095648400c00c0f003403644075a038503600402c024045030040720300b00031160b80039051295400307559401141c00e03100480000c500050000d05941c848501611891003d04094802141010481d40d0064030014000a0080160b85210b107500341c038500c200b043c0070300590320030480f11031401c091030445400d070401301c6400f07200c6040c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 437023003 1250 437021753 437021789
    0xf2402070b0402100e030715050d0603060b01020d050c190812010303200114071206080f1609060305070e04080409181202010b060a030e030f1306080c04060e101b0507 73
    0x80340d1815804400c0080c06418071720310b08104004100342c8c0c01919810f120f01800110341011440c81000e0040d0302550000c940119036070002414801d0f10380e1240c041c05801c0c0040d05040f4030004d8a1448116090030a0540041500f40400c00e8018080d2039403e05a00b44000304c00c01da404230b070400e0400c5864443c540e5100c14200002d0aa0b2010380494110390010000200000e210792070481c01c4040c0b20b4000150a52144001e031700308021645181e560350701c00c80c402c68081e021911200010900100104400d508640c0c2e426255803162107901c2005000202040c2400b5020b070440300200122002002482600b031204010143e00c02c8054504001c0e001200d048030340107020b944280a001031203030f1728000817110190014150451000802d00c800d1180c904d0307140a600042c801054400b02c4030200c03625007000103186500c001c1c04080380c898280410003496401842a0507200000c0b82d81107040d00080c03504a580c03460642c1d40500c0701d44480e10803414400041090340942320743c0390006480e00c034 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 437024253 1250 437023003 437023007
    0x60933020706120b03120a0c062d05010e0c070203120408070e01140a051002010608010519050c0f07080a1b0f0606051002061911040810060509040f2402070b040210 72
    0x204c0c00c4040c64268200d24451702c0f407405000700034521040325082c507000f804201d44402044540c0541c4103140c0102c000325440c1c036080031814085409045000500c181c0d81005801e0a0740c0401900d0300410a8000c24000d04642d002d00c071202100000790714441d05c580d61100d401e40d683c0791a01c03428903141c4002c4008215901030315003110303800601400403503400385083c00348100c07418044603802c110355842c08080b50901c1c080c0a000c0c02220701040c0c00766541155000001141c001600400140c001001811a441240c4060715031058000702403a8072201c0841e8103507542c1d0414125a800d482c10301c86c640d003c03c600c1241c08801c141c0104804c00c411030b110014400c0b1702e1000040f02025a10440004041e41c001c41d01d9803078107440c3c80354042401c1344421021401c3c0e420030b40240c0c40303a801ca0300742c40e902002c8600c00da00082101b280e000c0c0b0f5a0400c0c1d22144090b200d01c43d0040e05d81107034564190746180020309144006403250b40219035499082c02d04200d031500c1560f0492180c04441078034200d043c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 437025503 1250 437024253 437024261
    0x105010903020121020d110301050f1008010b0d1529090a0e190507200a02060403030528020d030b03150609070e0904030e01020d0906093302070612 65
    0x9506840c2d444070b8604100a481808007070b800564904e9808001c1c84501c0c503824003a0610102c000402240c695040408001c12021503c000d03030b028107251903042091765400044107044403500f842c0582d0301c540d410404405031203913400801c0780d0400400c002558404017000002c010398105040c140f070b0210290080124800c20b4502035210002250602c6400240621650051421800c3c2504c14000e85203200a680f000c45484001c502c00d0b00d0310002d1f242c800d51004c2d00c10300301000a04030609040d800110540110301024003009400300c2c400a002501c6000c0d03c40400010212190040c4d5030a00203603640d0b0080c030300701d0010307003072111a00302d9040008801015140c030300c441541c42d54901007400000304005145401704503a01540c91115120714101a0144d1301039036402d40c1c40c0c0445000a860844840e80303480800c1841030080054035802208141580d41c0141d032018210281780c10201c0c40b600c804258140103039074440c095240c40e00061200c1c1211219222040300c07142c910040c800719 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 437026753 1250 437025503 437025509
    0x70c080310030233090303090306010e0f010b040605070809060909010807060f170705071703270a0f03080a0e0709020301090b1c390314010905190c0b0a021501050109 73
    0x13005900c40b0029500c01c590050321a01c40c3c003900301c81c185042600000e29109007a8041c040c2114000705005680405481d81382c0504001c11280b803902d450103a00510520420b0005441804040785813801907071503100312141d101c0c2c0203010840d1561905251070f240d0045210320008220203d046002e414003034003035080a000d46900200959481240c2a00d4690041d00c0c115050000521802c040f190020003850040280302104054040b1032882881101811030b15480a80d02007280040054800c8090b24045daa052038a4034080c3c9035200d500d805031080c0c81c580c0555008845000c074400c44c1660146048400040c400c2c04204c8080b0b0900030002103610060090101e8116001c020840b00600710441182e6480c070902081820a07983c100e070b90460070303000300c50051100200140858400c2100c1d42c510b561000b00300e90101d0781e8580c1d13601e810301800d202070441601c40b48010310110919034401000e00300381441c0d44d000440c000948078542c001e8691354001e400c100105003944100f08040c19 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 437028003 1250 437026753 437026819
    0x30206240f060c030c1f1103131104020d06120c0501030b0105030c0f09040609020d0f022b0209030d0503090607080402130f06081006060305150a0e070c0803100302 72
    0x300100018044103500081c52040c0f030707200c02c10100c0344d8068100f20444801d41c4c0c00a2070483e18031400c40300000d036184404000040c1d8400d20902c1907002c82d0702c51040b00154004400181100740b00081000703070081015004840d0b1410b0310020f2404c40700a101f80f10340303200e14144001240c80704010350490b2035840c2c019001070000e00000320005050030051032508442d40c4903900740f160500c0018180c0389540c0000c8011600171131070035a02422400f5007030103816000f4040d4201903446802100d03c162920150040d00b6288075070000701580d5504541c400e000c05010351b08420034405001e8460390080c0c1c1d0020951050b000011000d61040620a0280d43d0040c030203400b0700380c0e5410103006000c01400701da03034055482100150300e00082202d001a107840c4000032581c00c1c501070001c0c044031001007002c000c4400c402c03d49560741d80d03800b48440176280c901003401240c1d190303540300b00c0d8940d0f403050300184456400004c2c49401d4020101e0407040300e10031035013031910391611040d9200907685203003034143c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 437029253 1250 437028003 437028019
    0x70305031b0405040c0c0506090106080309270112050f0a05060402060a11060f0912070c03060c050d06080606041a030a1101020a050a1a060a0305100b01110a03020624 73
    0xca007181d9103402150810034250a2401d00da21240001c0c01c9403078082559000c07841601040f01082410301c100c40c0d000042c00000c0020514050066031644106e040c010300ca5640004c41d500c0c1d0341c084442c600ca9210344125440388640e12141c50724140700300f825003030310349104112000505040004840b440c1ca503200b0701403d12a101e0380e00b800101d4105000d40d20901003090310700c0100701000c01600d07102d42c0042107041c5850900480140c01c0804080c60440031308000c0140d000428403000c202c5081325800400001e071000c400000b01c840f0b00450742494061070a11038000360b5038100140c0a40642001c840800c558000f030703c41a000741800d00320854054110403480f801040d80342690303100d00501070050b40d85100310b83c0e481e90b041404181003111000ca0101400c0a80301044a86136403019040d02c43d50003550558441590762482062440643c0c0e88450010343e090344903030380c40702580c000c020031140b09420ba0314019498030003c56801000c01c1c042030070002400b456811104c004003001e05289 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 437030503 1250 437029253 437029261
    0x901090807062f0303040b06010905030d02060117070503030d020403060c030623011b0605010f050a12060f09020604090902041a0f0607020402360307060f03020903211b010207030503 80
    0x20008100202e001400d07240311807464030f0030710341c02d100951140b4490900074a891501c00d00141c01a60b640d00150701a03401a0016680e11b80c00050060549101040b48440325202c800c507107280400766008103402d40804500010169503035006082508d2240005000381c0e000548214203c40052080030b802110a0744608038440d0000402070103030308185800180e0303d03261385034000414025081112015690001002105070b80c00704c0360041c00701220700f5181c091820380006242030320b405016002950b6a01000d845000d16405035400ca0390240206480e07550300ca100c000109004402640280d003003084001c0b4030301010900d544503800080210802d0306044040c4001600301150880e00142e003080f030301d815510108002c002580e0383e030700c000c200380c1c003111207a00340415070441c914000d6128401c00c0c0201c2d900a084c5500d907680303600e00141c4078070301c0700006460700508035907911646802e511183c1d2202c124030001e00c41000c11103440d081c4a00c401d40254200c0c49011806800141c0520200d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 437031753 1250 437030503 437030537
    0x70909020901030f0c090504060503120a2a0b0405100b010f0e03010b12011d010506010c0210051e30060118090e0105010620060612010204090e0102090109080706 71
    0x2814101c5410b140014041c0084804842214008078981c8040386038403504010b940340c1030107a030740605800e4018201c03002c1400b0b2121103038007880c004070080c4501d141d00d202480824040004a40381441d66401203061030f41400303000c040d41a10152154000c08a03488841c990034002e0503906181a0744191440c042640308031003d5802d0f000c603036419521800e0040c41642d40c0060000148556800059004000c91500b80382d0143c1740c400700c506904090402620781c0e04840ea081d00e268040c2c03034a9450400620040355580725617072948400e40c0c03004003e24880c030301510203085407007a100585a00e464140c40c46004181c04460204140030401c00054451351003914601102e000700d40c030070303080161240c030030005507520302c0500403081e99034800400c41e0b15070120181c0e5040c031821744035140440c4106419601c0340c800801031401784100640c41d11500b54254100e900500740803800b000b8100341038140c81d010b5030140e8441800205140400f081203400803440e10207d8071180c484e5100030200c5d24035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 437033003 1250 437031753 437031757
    0x50105011b02281401030b03280c0306020c060411030a0510020a1e0302130509060d06050402030f0a030e0f01030203010608010e041a0411120102030709050d1506080f1507090902 78
    0x19108080001514541102c030042c0c0c00201825104000100b1300001500040c2100c2d008800c45110340c1c0550002c003000450745d0103044540030700109662070b19031142002010541c160740014034240c4001600c076034101010400038011413040c08840b2440c41404201540c44a1121010304990480804000c0c440c4e002c2d4010f01010086e810100100b1842c200b2582d03458002c4629000402d80000e00049542c0d491216031002e00400c070b407200071605002d40030650040c502c8200800e10390307450780440e083d950100520b581105900048501c00c00440c50300800c10f1442c150000e0107108400c4c0c00b448250b0107802034034182e03090344d40c68050682c80d280d013034886800b01400580c0d8003c1d2a468041c1803c13034130314015100d0b0303000301d0300c000d03420802c0300600a108003100700d880c0a5074030500c180502554030201d00021070780111004035000000781000c04038548003004040c0708238540400040c1c90b140114048519814810aa0b40078441540861700008030880e0390000140c8201001c1c40030039107580c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 437034253 1250 437033003 437033029
    0x30d02130503030c0a050616120504050c06041412030c0303070818070f06020d031505010c110303030109051608040f0803071707050d111218030c01020706050a050105011b02 76
    0x340c250165104003103421903205070003440740c1c0c1d042090300909100d41006080c2d08491007505000e00c050b40050000c01040c00d00700e400025903260000300c0c1c1448030810540d9174030a03000f400d843d03660303079100c1070044001800000b86025080214480840b8400842030b03900610449001d9446d654540740111a44103000b06800940d40c503810305200d02e0141000004090001006160b000c44d05000c2c000e8a8005141e02070740415050901d44410b00000500e8041210028207000c540d0100c0d5191954000c40595840b58041c880031000013100c42d201d82101d0700440e0407036409040f984240b1001c40740300d182128007505410515020301e002608800c000c41c0d00c01d44524103042d110f4242d2206205a0a054446100260f404206001e902d01c0745d2141c1040c0b0610201c0d020b180850007500d82003030401c010900c000d40c444424200444c80000c2c021954140410002155945050b1030042c0003000250340c0446031a10b05030001c14070794050300314500220f0b4021100f40c020300740c42d420014040389000c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 437035503 1250 437034253 437034277
    0xb0115090b0a05071403090a090b13020f09040612080910050f1209070b0703120906020c0604051006140f1002070807060809010f021201120201170a021206060903030d02 74
    0x301000480603141800360402603081c0ea0364035038a6000781040c220300e008038808541e494008002942c0c0795a9500c1c2c0c4102281c40c4080d0210f0668600000544968207036180c0341541400066001c1c411121100109900601100e0410030503490351110103d80d506080001e281c020100020407084c584144018000319191401624080000c46140c0c0c40303070031171b10f10040298910b1043c0009094144000400b9240d0390045908084164030001c2c0000707602013151103155502c0d500401030000e0358048030801103c1c2801c407007440c00c0502c1c19503550540807240580c5145840c1021591402940100600140050803e01440c04001c108241e20080e04d40f15002c1d031160120000d000201408030b40010030558941c06100d00c3d155200c1c41c01c0d00c4003070341c01e500000c0c0304003d903140c202441501103054a141d202201c02c0301c621480161884a02101081c0030390034103500700229030155400900501846003500c0301e50341c030790b4002d00940340254058140d241d00b040c080501e00c2c01e156809410b40c4a554 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 437036753 1250 437035503 437035517
    0x50a0309050316080a020106061107031b0e0f161403010608060d021309150207051216050105161101050f0606070f020d050309030d0804050c010807050c010606030c0306060206040b0115 81
    0x2450140d84440c103580b030125502080402c01071042e903028411640148211300f049200e4130ada44c0002034070341c51a4000248120342055201c482c40c3d10b50304996001e0154441400024280b500350b1201c0b41000f103c44c5956202c2e91030f01c000c0301c18860b140c03602c19190b4010049080d40d0a000050310300e103200170007003a0000b4111151002607a20350141c10030076401c00c100000c03641101e040101d0721b807443c074503240602c41c010016407001440000d20050304000420007951107103a034140c282a44400f1650242080d801d0a05002211f00b8544d9554601504c1c3c0e218044d01e050103401d0340f030a80c0c00c1100d10304512402e0100080d0542410801022094401c0e00303059241041d070f60000f2586500040700703070380726070004c102c907181d0b17080030807801c035070802c032401c041c1440d00c0c0c00c1c0d036865640c000b801ea581d4100b240040c04100090f001f035050724000c103d15070080c010365850b46002070042003059203020001c0d0520000240e10f50011030150f01070f0b81c12400c4042e00340c0c2028414000d10f1840704c0c500e8104085 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 437038003 1250 437036753 437036767
    0x170d0f1b05161e03020a060c08070b0108011a041b0e030a140a02040e0609030d180204051f090204240e0a171b0d02041d10060801050c0a050a03090503 66
    0x4188001e40c0c030b4814011428a07903c3c1042000c05124054400101d80400040410b2025035500300d988000c840c101d00e420803070340340c3ca40b80c0742183d03000d0400c00a01112401d000410012019008040d50444210040380c2500c582c10421068490b05440f10704e0b016000e1460034107061007240a0020518058112511a8500d940703050040c4a0001c040100b0381021001d0000c520300f602a0003100c00c1031400500301810f1820b9000d440f803207001c030f01201c031aa0380e200c151000c0800e5131184050640080c8200400d1600e0b414030064425100021844000c0f55170f404220000240b0a80b010780e0601d4024180b00c1e0341102041028000c580b0101d41403210a88180700c0b183e50b010701c07140161100c0c0c030b8201d040040c681d94051400c50350660b04500040402c00070300c0c007a200e09051f1070302107804403004540c070800c2da90710f03688013500111842554062071030704480750b481c00d80001e000c07600c00700e000300900d03030b900e1008180c41d01076403605000040c01040308502d101e202e60410910a401001581d141c00c80c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 437039253 1250 437038003 437038013
    0x2d011802010f030902120304061e360504020a030506011413050d230307060c0c03050904090c03050607050a02070e010e0f04060e011b0f030908251b170d0f1b 69
    0x80d07001400003414116002e02d480f8071075003002b881d1112810542d103440032001100100b2500d584d4100c1c40b0320f4420384c01c0082c05140a2101b8010140030784115034030502004002c0140400300c8605022510411550a10059002c11500382207021054580614109010040307200c41809080e185851056028080ea92501100c5699131700d016008664450307803031901c08140ca940c054490148001d04940c4400700c4e8002e000c95010351000ca40c0000e03940c3d075074a0310140040e040d80015000f81325005c00c001406030840d0040c140b0f400383e81c00b21824a0342d51210041e02c0c003424000c580d03815142a0102e844446600041a042449810049022a0503400b81800c40b0b03120703140b42200815155100c4810354020842c0c07c40c00b00d1902e17081c00005910b84942e140c5104041d00407464004819500c02008111103403103000710340c05034140d07482c030242811030124503101d8040c5008400381c440d01c0030f10400b40080e95421040664803114106007400a0544401c80c81d100c140500c8501d82300e035140018 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 437040503 1250 437039253 437039257
    0x3070b0703050c07121502030f0601030209040f0905030307090e01031203020a050705060906010e0a0e061801060f030804050306060a030b072003070609032304090e2d011802010f0309021203 83
    0x82855200baa10049032410484820340207401ba640140388100184000c0c0c600c011640c60f8000d00c282005644d904607100414000c02c8600401c0b092580703840303006420010301100440c0203404503603400241d5611164080746d44507082c44003d00801811100e01545c0d4041c0e000340a14440c1ca09105040107820b03228a400c0150403a00010360760400c40041c85a540704c015250340119400f003040002411303d09549540e041d01030078417072040d00b0701022100f116100350040400b40590390144940c555681c5050307400c0d43c01a0144501c280500000180142020403112049075007100d80210039845810741039400c0c444402c038068103040707000031221030358100300300400041d48680320014880740e00b42401040f0904a50441a00154100d003404600c00782e81c0a40c4c0640c1c0101100140c400c100255191801c8016824440e42c0551414507a0b0308445e01c100d0390110f4001c141c024041501400000e031090142c5d00340c024041414000502c0c0c600348654060078070700d4805000925400381a6000520315 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 437041753 1250 437040503 437040509
    0x102031c18021519090806060d02040204081603020a09051324091202010e121e04080a050a0c08161509030602030a09020f06070210050a02010b1c1101090503070b0703050c07 76
    0x10318000981c1641c188802c0c80941c6049501e40341c601c405da400c0003003064070342c00040c000710b124620340560182556204d9040b03c5c000d054210842c2c1c81d01c50856000c4034810000c2c8003d0303108084030781d40002c144456004161159072884180300300d000c0340703075544025101d0768141034101c440c1c410008a111252072280b0340d0550300810012401d22050240242941c1550260400303903003000205440c44407100382680c400d41e42c4803801d014044602213204109008943c0074a00038031441000800340000810390500c01409a14554840c540360384c0c503603030784060781c448a80480f0070a5108001088104940f0480c2d001a841c0405046603a901e400b82640c0059644859059a503500340c411450b0025000700c07107902c1598018100b800f50b80025803500165070070308083c00400038450801b540301790f10600e132403d0028203c0d4a14500f00c82040e505c4203d810b0110341e01044c0e803200822070340c01000250100e43d001002003804500b40320018640c3d8102e44021030600405002210003500b0134000d0a020b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 437043003 1250 437041753 437041789
    0xf020406170a06030503030c0c01150308030f070504230f0d080c010b040b1f090315090312051005060c07090516090501080f13020114070606140102031c1802 69
    0xd0000990407666809070140140d40303154540042000040c1000c4140e9a21030064010262561000542e090242c00070b844580050000002c000c01040a06030240d030280c07045080189103035903400310580da148168000e10140e1002c600640303480042001030b6580708100500002e0a109107100400c0400107529400c40c2c141e90082080b03130b5a03c0e000d100350b1404283c01c0720284050505400412413548120544001c1c00401d03000300d40036940a180250000c590140d0031140c203080800c600d000800408404030f0000b03005040f4900344070340a0044038090b004806402007624540800c004031a4844032aa030f826000320103000481d940507110304c5106e25102c80c0328104c0c881021000411620103034002605010070340052000310b1f44207091996000b52201e8160114070428001078440c50491101810165400148001040801c3e0040400c5820100300072984030418001603840380940c0000c64900a039407105c41d5034004813908041100d044900c0400540341450300840c6400911241c0114 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 437044253 1250 437043003 437043017
    0x905090604061109090606090d0b0106020a0203070504050c19090b040f05030c030d0c060b2b14030a440106140405090103080c01140709080606031b01080a0f020406 72
    0xe0103254090441020009440c5501d01008140059448140038046ca4000c5802044041300d54031000d12002d6041d400c008401903541c2c1d1140001d540b88000d23041240030703020307929000405c0d05103402803074001c00d81c42200d00c0c109001c142e5540740c060000c0c2e01003030400510a80c001442140c650007030024010f112161030103142802c050500e400648280c19001e0b501400752302c40c0c1540e01c10300b0401060b0740b0440c0400c000f80d00c000001c0e003840320390800c3c0030200d6052080c086083c417443c03001045c0c548908062640d90201c0b6000640724013801182c800828031740e4010710351480c0d640d904000008240122180c3e880b40c5101c103102d030306070070038500e024985824005200560b0084402c90102c400019418901820300e0045500313550180710080080c00c0101b41c8080c0580290002d4103ca101c51046040c2c07490704110080c034241403481000018010744010980a050116070911181104000c103104c0007508001110b001c1801058062610341e508a044120440e50008000501060792550 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 437045503 1250 437044253 437044261
    0xf05060306091e013f080a12110705010c1d0d0309030830010803070b07031409011e11041502160f0e070c0c05011b05070f0602010b0a120b1009050906 66
    0x10314417030b904c41001d02c584081da080416011407004144221548509143d0701c0307011300641036415064038130030609414105001e0407100c00541014180540c0900020f0000012400c0b0035141c0312640030354041c10501d40000e44140b03040501c0d00d08241c9109140c401b14041c2d03240c50b0010305400c000030700c40300040484901d16a20001e1030040410740180d486404055161208850b9203200310203008000d2550a0b00180d1080d0195000c0b060000c0c405941320141e03d81000030b02e00903d10340002403000480d00903a41a9002e041c410819103414002401e4605410300c101d4045046a281c0320500b1803185162465114005c0d0b900c4600400c0c0c1e82540300651400c046003032041da80c0007000d4004210984141c04003203070710078003000c04032442803c2100c500300f201102010b0b170042148000e415442852000034807000340c0f455403800c4819640c001c2007003541c2c00041200fa82c00601c40d08401c40b860750300310004507014603000d5802c80c40107044902180e980708e03a24019030754215001b546031b0308004104 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 437046753 1250 437045503 437045549
    0x6030803060f010f050306100302040509190507140306040e010b030a0b0105030d0813140708010c050712050f070605070c0b090607090515040603050a02120108060a060f05060306091e01 81
    0xb0080d400002d00b4468801d0044901c01811400001c28043c400e64980710342e01d00040c000c0d811a07028090181002c0c0051a0018a200d0711603010141462103070724000014460358400c003820710300d86d689070014620b541c40d14420407014101c0c0b810507107519540c4000240c11075030204a5550f82900c1110300d40e8181d0f24040415007424800004081030000c55400c01543d00c0032000311901031580700c00803601101510300124500000c0e03400890040d1b1910f11288403c0ba0040003521a5a210702e01180508600100031206d03805041c501c10f0030340c81c0a001200000b50705400c05540600c891a181000d001c841d111f0b2446103500b80d8a08186401c0307281030203640340d171140d081c002901064415101c5e481592815030010722071886800201952580414400303541501110417100840c07440341c0065840d040c0c9e070341e250342e0196234402d6400d1500f140001d0a4401600000803610005d24032815951404203000c0c1440d40144580c0943c0c4140c0701100b0903056001106000c2c140c8900c0d0028080126104 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 437048003 1250 437046753 437046769
    0xa0309080c040b01120e0c032505120a0213020918040303050f07080a0b060405040603080322080301060c1506030302060a0c0201270215040e0601030c0f02070311030a060603080306 79
    0x41e5a010b0750074940c1500042c1d0300b018444440c201c84801c00182e08041c80c60352801c085043d00b20540c54002c07030046c203980b1100e05181c090080c410801038101d00c0e6444003001015042c402d8041e440d44c004840c100050b281682d801c0345144510940980b8042101002034540001000d0303000c40d04035881c0c00e00082c1035240c4100d80d806144851140b805080c1082d019000340c40040c98055001c1e255600d007145a11080c0a803402814042c06c140705242e01c0b460f20a42d00d40045400c00d4202c04060802e0300c0c00400302c210028201d411900003461a403c1640c125420030094006507400c8045a44c030f0148008644180c50080d4000d50103046c15047c00541241941c4006a1074421a030401151a5441441d1210080c0c0400c216100e00c090141d940f000c00e0076603000302e0140d2039100c404940017810121044c4a1b500c911001d03682001480400c0100b0742e04072240072003030300050b4070455041c00014004901418040d10040c00c03250840b809035158000c3c0e40c6a90001c5800510100c00c0c00a2030805410f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 437049253 1250 437048003 437048023
    0x60501050117190f05091027030e04061721090f0f030c060a08100614030610020313140f03010203091c1704030206071403072f0a030908 60
    0xa0010b400c0c6444455282d07419401030414215465030124050300c1901d10342c454a805400c4540910540c6003181c00e294481140100004142d410700322414100062005290250409000041134031207480e101210364200307000809030031650b0340e24007103443d0741710a00034008081b85000a0031356000201350020b0403504c0000e203006103030061000500300d6882d10a507481040040d240e058550007080002880e0400200e80706400ca000080e19000c407a501140c05446400c0003080703083e0065845400702d8444d08810340405c1643c00c14000300e0a41d00d4400212000c00f60780f84103d0f814640350150040940409034400509648c0d141000b01d110700301740d1118840d440d803c42c000c500350305d0651142500c0300340070300c40310084180b403844110515004004800c43d000300078125009520301840d02030350b0740d101601d4800101e5850780440b640810300d5001c4074880d09090351170700c01200d001100b001103481142c3c21014040c0e038058482c010400b0812402162500a030380f40b090301d80c600208541040f0a083c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 437050359 1106 437049253 437049257
    0x1419022803050d17150405041505280e0703120311030c0a1206080d050703021c031b02120909060619080a0f1b050309120f070605010501 60
    0x1070344030030500091302c8040030882480992601d002d8111413018441d039511904c400e80b42000c1d040355810030302c5406007400b0548403030740500513624110b1b41000d0a598201c3c54070b0300c0c40c161040744507400881c446c040041440c1600c00984502c01804043c020b02814049054038512075800364200345280c01000d0307168203004900d01e00030b0b404242c035107000507000f001c1c5c089408030b10720034a4104d4081d14001d000c95542404141c4185e00080c03000d80c00d600400b502c495101c43d031014050301d89a04c558000a070032119a035070111010300c650409046600212401c80002c00600c01c480c2038040032640f40352581d6070207001901c548a603a40a11000034007038284080c090300404054040c041818092200c0302c3c0c028003490171200c40740b240d003000c0e41e10030780006001806100110b400644000542d1010780300c00210200c0c81d842a40f00340001240042c2480511606100d9103024000074 = true := by decide +kernel

theorem cover : BRFrame.Cov 436870503 437050359 := by
  have h0 := BRFrame.cov_init 436870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 436870503 ≤ n) (h2 : n < 437050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
